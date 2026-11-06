import * as fs from 'node:fs';
import { ReadStream } from 'node:fs';
import { FileHandle } from 'node:fs/promises';
import * as path from 'node:path';
import { crc32, createInflate, createInflateRaw } from 'node:zlib';

const CUR_VERSION = 0;

interface ArchiveDataManager {
  sources: Record<string, ArchiveDataSourceInfo>;
  loadArchive(filePath: string): Promise<ArchiveDataSource>;
  readFile(filePath: string): Promise<Buffer | null>;
  readFileStream(filePath: string): Promise<ReadStream | null>;
}

type ArchiveDataSource = {
  path: string;
  size: number;
  data: Record<string, CompactArchiveDataFile>;
}

type ArchiveDataSourceInfo = {
  path: string;
  size: number;
  fileCount: number;
}

// [length, crc32, fileHeaderOffset, sourceId]
type CompactArchiveDataFile = [number, number, number, number];

type ZipDataOffset = {
  filePath: string;
  name: string;
  crc32: number;
  offset: number;
  compressionMethod: number; // 0 = Store, 8 = Deflate
  compressedLength: number;
  length: number;
}

export type PathTreeNode = {
  files?: Map<number, CompactArchiveDataFile>;
  children?: Map<string, PathTreeNode>;
};

export class FpArchiveDataManager implements ArchiveDataManager {
  sources: Record<number, ArchiveDataSourceInfo> = {};
  nextSourceId = 0;
  pathTree: PathTreeNode = {};

  async loadDirectory(dirPath: string, concurrency: number = 1, cache = false, recursiveMatcher?: (filename: string) => boolean): Promise<void> {
    const files = fs.readdirSync(dirPath, { withFileTypes: true }).filter(f => f.isFile() && f.name.endsWith('.zip'));
    for (let i = 0; i < files.length; i += concurrency) {
      const batch = files.slice(i, i + concurrency);
      await Promise.all(batch.map(async (file) => {
        try {
          await this.loadArchive(path.join(dirPath, file.name), false, recursiveMatcher);
        } catch (err: any) {
          console.error(err.message);
        }
      }));
    }
  }

  async loadArchive(filePath: string, cache = false, recursiveMatcher?: (filename: string) => boolean): Promise<ArchiveDataSource> {
    const archiveData: Record<string, CompactArchiveDataFile> = {};

    const sourceId = this.nextSourceId++;
    if (filePath in this.sources) {
      throw new Error('Archive already loaded');
    }

    // Read archive metadata
    const fd = await fs.promises.open(filePath, 'r');
    const stats = await fd.stat();
    const fileSize = stats.size;

    const archive: ArchiveDataSource = {
      path: filePath,
      size: fileSize,
      data: archiveData,
    };

    // Read the central directory at the end of the file
    await this.parseZipRange(fd, filePath, fileSize, 0, archiveData, filePath, sourceId, recursiveMatcher)
      .finally(() => fd.close());

    this.sources[sourceId] = {
      path: filePath,
      size: fileSize,
      fileCount: Object.keys(archive.data).length
    };
    this._buildIndexForSource(archive, sourceId);

    return archive;
  }

  private _buildIndexForSource(source: ArchiveDataSource, sourceId: number) {
    for (const [fileName, fileInfo] of Object.entries(source.data)) {
      const parts = fileName.split('/');
      let node = this.pathTree;

      // Navigate/create tree structure
      for (let i = 0; i < parts.length - 1; i++) {
        const part = parts[i]!;
        if (!node.children) {
          node.children = new Map();
        }

        let child = node.children.get(part);
        if (!child) {
          child = {};
          node.children.set(part, child);
        }
        node = child;
      }

      // Store file at leaf
      const filename = parts[parts.length - 1]!;
      if (!node.children) {
        node.children = new Map();
      }

      let fileNode = node.children.get(filename);
      if (!fileNode) {
        fileNode = { files: new Map() };
        node.children.set(filename, fileNode);
      }

      if (!fileNode.files) {
        fileNode.files = new Map();
      }

      fileNode.files.set(sourceId, fileInfo);
    }
  }

  async parseZipRange(fd: FileHandle, filePath: string, fileSize: number, fileOffset: number, archiveData: Record<string, CompactArchiveDataFile>, parentFilename: string, sourceId: number, recursiveMatcher?: (filename: string) => boolean): Promise<void> {
    const INITIAL_READ_SIZE = 2048;
    const MAX_COMMENT_SIZE = 65535;
    const EOCD_SIZE = 22;

    // Read initial buffer
    const initialSize = Math.min(INITIAL_READ_SIZE, fileSize);
    let readSize = initialSize;
    let buffer = Buffer.allocUnsafe(initialSize);

    await fd.read(buffer, 0, initialSize, fileOffset + (fileSize - initialSize));

    // Search from end (most likely position)
    let eocdPos = -1;
    for (let i = buffer.length - EOCD_SIZE; i >= 0; i--) {
      if (buffer.readUInt32LE(i) === 0x06054b50) {
        eocdPos = fileOffset + (fileSize - initialSize) + i;
        break;
      }
    }

    // If not found, expand search
    if (eocdPos === -1 && fileSize > INITIAL_READ_SIZE) {
      const fullSize = Math.min(EOCD_SIZE + MAX_COMMENT_SIZE, fileSize);
      readSize = fullSize;

      // Only read the additional data we haven't read yet
      const additionalSize = fullSize - initialSize;
      const additionalBuffer = Buffer.allocUnsafe(additionalSize);

      await fd.read(additionalBuffer, 0, additionalSize, fileOffset + (fileSize - fullSize));

      // Combine buffers
      buffer = Buffer.concat([additionalBuffer, buffer]);

      // Search only the new portion (we already searched the end)
      for (let i = additionalSize - 4; i >= 0; i--) {
        if (buffer.readUInt32LE(i) === 0x06054b50) {
          eocdPos = fileOffset + (fileSize - fullSize) + i;
          break;
        }
      }
    }

    if (eocdPos === -1) {
      if (filePath === parentFilename) {
        throw new Error(`ZIP: End of central directory not found for ${filePath}`);
      } else {
        throw new Error(`ZIP: End of central directory not found for ${parentFilename} in ${filePath}`);
      }
    }

    const eocdBuffer = Buffer.alloc(22);
    await fd.read(eocdBuffer, 0, 22, eocdPos);

    const centralDirOffset = fileOffset + eocdBuffer.readUInt32LE(16); // Offset to start of central directory
    const isZip64 = centralDirOffset === 0xffffffff;
    const entryCount = eocdBuffer.readUInt16LE(10); // Number of records
    const centralDirSize = eocdBuffer.readUInt32LE(12); // Size of central directory in bytes

    if (isZip64) {
      let eocd64Pos = -1;
      for (let i = buffer.length - 4; i >= 0; i--) {
        if (buffer.readUInt32LE(i) === 0x06064b50) {
          eocd64Pos = fileOffset + (fileSize - readSize) + i;
          break;
        }
      }

      if (eocd64Pos === -1) {
        if (filePath === parentFilename) {
          throw new Error(`ZIP64: End of central directory not found for ${filePath}`);
        } else {
          throw new Error(`ZIP64: End of central directory not found for ${parentFilename} in ${filePath}`);
        }
      }


      const eocd64Buffer = Buffer.alloc(56);
      await fd.read(eocd64Buffer, 0, 56, eocd64Pos);

      const centralDir64Size = eocd64Buffer.readBigUint64LE(40);
      const centralDir64Offset = BigInt(fileOffset) + eocd64Buffer.readBigUint64LE(48);

      const chunkSize = 64 * 1024; // 64kb chunks
      let remainingBuffer = Buffer.alloc(0); // Buffer to hold partial records from previous chunk
      let processedBytes = 0n;

      while (processedBytes < centralDir64Size) {
        // Read next chunk of central directory
        const bytesLeft = (centralDir64Size - processedBytes);
        const readSize = bytesLeft > BigInt(chunkSize) ? chunkSize : Number(bytesLeft);
        const newChunk = Buffer.alloc(readSize);
        
        await fd.read(newChunk, 0, readSize, (centralDir64Offset + processedBytes) as any);
        processedBytes += BigInt(readSize);
        
        // Combine remaining buffer from previous chunk with new chunk
        const cdBuffer = Buffer.concat([remainingBuffer, newChunk]);
        let pos = 0;
        let recordSize = 0;
        
        while (pos + 46 <= cdBuffer.length) {
          // Check for valid central directory signature
          if (cdBuffer.readUInt32LE(pos) !== 0x02014b50) {
            if (filePath === parentFilename) {
              throw new Error(`Bad file header signature for ${filePath} got 0x${cdBuffer.readUInt32LE(pos).toString(16)}`);
            } else {
              throw new Error(`Bad file header signature for ${parentFilename} in ${filePath} got 0x${cdBuffer.readUInt32LE(pos).toString(16)}`);
            }
          }
          
          const crc32 = cdBuffer.readUInt32LE(pos + 16);
          const nameLength = cdBuffer.readUInt16LE(pos + 28);
          const extraFieldLength = cdBuffer.readUInt16LE(pos + 30);
          const fileCommentLength = cdBuffer.readUInt16LE(pos + 32);
          const externAttributes = cdBuffer.readUInt16LE(pos + 38);
        
          if ((externAttributes & 0x10) || ((externAttributes >> 16) & 0o040000)) {
            // Is directory, skip
            recordSize = 46 + nameLength + extraFieldLength + fileCommentLength;
            pos += recordSize;
            continue;
          }
          
          recordSize = 46 + nameLength + extraFieldLength + fileCommentLength;
          
          // Check if we have the complete record in the buffer
          if (pos + recordSize > cdBuffer.length) {
            break;
          }

          let uncompressedLength: number = cdBuffer.readUint32LE(pos + 20);
          let length: number = cdBuffer.readUint32LE(pos + 24);
          let fileHeaderOffset: number = cdBuffer.readUInt32LE(pos + 42);
          // Read Zip64 extra field
          let zip64Pos = 4;
          if (uncompressedLength === 0xffffffff) {
            uncompressedLength = Number(cdBuffer.readBigUInt64LE(pos + 46 + nameLength + zip64Pos));
            zip64Pos += 8;
          }
          if (length === 0xffffffff) {
            length = Number(cdBuffer.readBigUInt64LE(pos + 46 + nameLength + zip64Pos));
            zip64Pos += 8;
          }
          if (fileHeaderOffset === 0xffffffff) {
            fileHeaderOffset = fileOffset + Number(cdBuffer.readBigUInt64LE(pos + 46 + nameLength + zip64Pos));
            zip64Pos += 8;
          }

          const fileName = cdBuffer.toString('utf8', pos + 46, pos + 46 + nameLength);
          archiveData[fileName] = [
            length,
            crc32,
            fileHeaderOffset,
            sourceId,
          ];

          if (recursiveMatcher) {
            if (fileName.toLowerCase().endsWith('.zip') && recursiveMatcher(fileName)) {
              const compressionMethod = cdBuffer.readUint16LE(pos + 10);
              // Only parse uncompressed zips
              if (compressionMethod === 0) {
                const lfhLengthsBuffer = Buffer.alloc(4);
                await fd.read(lfhLengthsBuffer, 0, 4, fileHeaderOffset + 26);
                const lfhNameLength = lfhLengthsBuffer.readUInt16LE(0);
                const lfhExtraFieldLength = lfhLengthsBuffer.readUInt16LE(2);
                const dataOffset = fileHeaderOffset + 30 + lfhNameLength + lfhExtraFieldLength;
                try {
                  await this.parseZipRange(fd, filePath, length, dataOffset, archiveData, fileName, sourceId);
                } catch (err: any) {
                  console.error(err.message);
                }
              }
            }
          }
          
          pos += recordSize;
        }
        
        // If we processed all records in this buffer, clear the remaining buffer
        if (pos + 46 > cdBuffer.length || pos + recordSize > cdBuffer.length) {
          remainingBuffer = cdBuffer.subarray(pos);
        } else {
          remainingBuffer = Buffer.alloc(0);
        }
      }      

    } else {
      const chunkSize = 64 * 1024; // 64kb chunks
      let remainingBuffer = Buffer.alloc(0); // Buffer to hold partial records from previous chunk
      let processedBytes = 0;

      while (processedBytes < centralDirSize) {
        // Read next chunk of central directory
        const bytesLeft = (centralDirSize - processedBytes);
        const readSize = bytesLeft > BigInt(chunkSize) ? chunkSize : Number(bytesLeft);
        const newChunk = Buffer.alloc(readSize);

        await fd.read(newChunk, 0, readSize, (centralDirOffset + processedBytes));
        processedBytes += readSize;

        // Combine remaining buffer from previous chunk with new chunk
        const cdBuffer = Buffer.concat([remainingBuffer, newChunk]);
        let pos = 0;
        let recordSize = 0;

        while (pos + 46 <= cdBuffer.length) {
          if (cdBuffer.readUint32LE(pos) !== 0x02014b50) {
            if (filePath === parentFilename) {
              throw new Error(`Bad file header signature for ${filePath} got 0x${cdBuffer.readUInt32LE(pos).toString(16)}`);
            } else {
              throw new Error(`Bad file header signature for ${parentFilename} in ${filePath} got 0x${cdBuffer.readUInt32LE(pos).toString(16)}`);
            }
          }

          const nameLength = cdBuffer.readUInt16LE(pos + 28);
          const extraFieldLength = cdBuffer.readUInt16LE(pos + 30);
          const fileCommentLength = cdBuffer.readUInt16LE(pos + 32);
          const externAttributes = cdBuffer.readUInt16LE(pos + 38);

          if ((externAttributes & 0x10) || ((externAttributes >> 16) & 0o040000)) {
            // Is directory, skip
            pos += 46 + nameLength + extraFieldLength + fileCommentLength;
            continue;
          }

          recordSize = 46 + nameLength + extraFieldLength + fileCommentLength;

          // Check if we have the complete record in the buffer
          if (pos + recordSize > cdBuffer.length) {
            break;
          }

          const crc32 = cdBuffer.readUInt32LE(pos + 16);
          const length = cdBuffer.readUint32LE(pos + 24);
          const fileHeaderOffset = fileOffset + cdBuffer.readUInt32LE(pos + 42);
          const fileName = cdBuffer.toString('utf8', pos + 46, pos + 46 + nameLength);
          archiveData[fileName] = [
            length,
            crc32,
            fileHeaderOffset,
            sourceId,
          ];

          if (recursiveMatcher) {
            if (fileName.toLowerCase().endsWith('.zip') && recursiveMatcher(fileName)) {
              const compressionMethod = cdBuffer.readUint16LE(pos + 10);
              // Only parse uncompressed zips
              if (compressionMethod === 0) {
                const lfhLengthsBuffer = Buffer.alloc(4);
                await fd.read(lfhLengthsBuffer, 0, 4, fileHeaderOffset + 26);
                const lfhNameLength = lfhLengthsBuffer.readUInt16LE(0);
                const lfhExtraFieldLength = lfhLengthsBuffer.readUInt16LE(2);
                const dataOffset = fileHeaderOffset + 30 + lfhNameLength + lfhExtraFieldLength;
                try {
                  await this.parseZipRange(fd, filePath, length, dataOffset, archiveData, fileName, sourceId);
                } catch (err: any) {
                  console.error(err.message);
                }
              }
            }
          }

          pos += recordSize;
        }

        // If we processed all records in this buffer, clear the remaining buffer
        if (pos + 46 > cdBuffer.length || pos + recordSize > cdBuffer.length) {
          remainingBuffer = cdBuffer.subarray(pos);
        } else {
          remainingBuffer = Buffer.alloc(0);
        }
      }
    }
  }

  async readFile(filePath: string): Promise<Buffer | null> {
    const zipDataOffset = await this.getZipDataOffset(filePath);
    if (zipDataOffset === null) {
      throw createENOENTError(filePath);
    }

    const stream = await createStreamFromOffset(zipDataOffset);
    if (stream === null) {
      return null;
    }

    return new Promise<Buffer>((resolve, reject) => {
      const chunks: Buffer[] = [];
      
      stream.on('data', (chunk) => {
        if (typeof chunk === 'string') {
          chunks.push(Buffer.from(chunk));
        } else {
          chunks.push(chunk);
        }
      });
      
      stream.on('end', () => {
        const buffer = Buffer.concat(chunks);
        if (buffer.length !== zipDataOffset.length) {
          throw new Error('Did not read whole length');
        }
        const hash = crc32(buffer);
        if (hash !== zipDataOffset.crc32) {
          throw new Error('CRC32 did not match file data');
        }
        resolve(buffer); // Convert to unsigned 32-bit
      });
      
      stream.on('error', reject); 
    });
  }

  async readFileStream(filePath: string): Promise<ReadStream | null> {
    const zipDataOffset = await this.getZipDataOffset(filePath);
    if (zipDataOffset === null) {
      throw createENOENTError(filePath);
    }
    
    return createStreamFromOffset(zipDataOffset);
  }

  async getZipDataOffset(filePath: string): Promise<ZipDataOffset | null> {
    const parts = filePath.split('/');
    let node: PathTreeNode = this.pathTree;

    // Navigate tree
    for (const part of parts) {
      if (!node.children) return null;
      const child = node.children.get(part);
      if (!child) return null;
      node = child;
    }

    // Get first file entry
    if (!node.files || node.files.size === 0) {
      return null;
    }

    const [sourceIndex, fileInfo] = node.files.entries().next().value!;
    const source = this.sources[sourceIndex]!;

    const fd = await fs.promises.open(source.path, 'r');
    return parseZipDataOffset(fd, source.path, fileInfo)
      .finally(() => {
        fd.close();
      });

    return null;
  }
}

function createENOENTError(path: string) {
  const error = new Error(`ENOENT: no such file or directory, open '${path}'`) as NodeJS.ErrnoException;
  error.code = 'ENOENT';
  error.errno = -2; // Standard errno for ENOENT
  error.syscall = 'open';
  error.path = path;
  return error;
}

// == Local File Header ==
// Offset Length Field
// 0	4	Magic number. Must be 50 4B 03 04 (PK♥♦ in latin1).
// 4	2	Version needed to extract (minimum).
// 6	2	General purpose bit flag.
// 8	2	Compression method; e.g. none = 0, DEFLATE = 8 (or "\0x08\0x00").
// 10	2	File last modification time.
// 12	2	File last modification date.
// 14	4	CRC-32 of uncompressed data.
// 18	4	Compressed size (or FF FF FF FF for ZIP64).
// 22	4	Uncompressed size (or FF FF FF FF for ZIP64).
// 26	2	File name length (n).
// 28	2	Extra field length (m).
// 30	n	File name.
// 30+n	m	Extra field.

// == End of Central Directory record - Regular Zip ==
// Offset Length Field
// 0	4	Magic number. Must be 50 4B 05 06.
// 4	2	Number of this disk (or FF FF for ZIP64).
// 6	2	Disk where central directory starts (or FF FF for ZIP64).
// 8	2	Number of central directory records on this disk (or FF FF for ZIP64).
// 10	2	Total number of central directory records (or FF FF for ZIP64).
// 12	4	Size of central directory in bytes (or FF FF FF FF for ZIP64).
// 16	4	Offset of start of central directory, relative to start of archive (or FF FF FF FF for ZIP64).
// 20	2	Comment length (n).
// 22	n	Comment.

// == End of Central Directory record Zip 64 - 56 bytes not including Comment ==
// Offset Length Field
// 0	4	Magic number. Must be 50 4B 06 06.
// 4	8	Size of the EOCD64 minus 12.
// 12	2	Version made by.
// 14	2	Version needed to extract (minimum).
// 16	4	Number of this disk.
// 20	4	Disk where central directory starts.
// 24	8	Number of central directory records on this disk.
// 32	8	Total number of central directory records.
// 40	8	Size of central directory in bytes.
// 48	8	Offset of start of central directory, relative to start of archive.
// 56	n	Comment (up to the size of EOCD64).

// == Central Directory file record - 46 bytes not including metadata ==
// Offset Length Field
// 0	4	Magic number. Must be 50 4B 01 02.
// 4	2	Version made by.
// 6	2	Version needed to extract (minimum).
// 8	2	General purpose bit flag.
// 10	2	Compression method.
// 12	2	File last modification time.
// 14	2	File last modification date.
// 16	4	CRC-32 of uncompressed data.
// 20	4	Compressed size (or FF FF FF FF for ZIP64).
// 24	4	Uncompressed size (or FF FF FF FF for ZIP64).
// 28	2	File name length (n).
// 30	2	Extra field length (m).
// 32	2	File comment length (k).
// 34	2	Disk number where file starts (or FF FF for ZIP64).
// 36	2	Internal file attributes.
// 38	4	External file attributes.
// 42	4	Relative offset of local file header (or FF FF FF FF for ZIP64). This is the number of bytes between the start of the first disk on which the file occurs, and the start of the local file header. This allows software reading the central directory to locate the position of the file inside the ZIP file.
// 46	n	File name.
// 46+n	m	Extra field.
// 46+n+m	k	File comment.
export async function parseZipDataOffset(fd: FileHandle, sourcePath: string, fileInfo: CompactArchiveDataFile): Promise<ZipDataOffset> {
  const [fileLength, crc32, fileHeaderOffset] = fileInfo;

  // Read local file header
  const lfhBuffer = Buffer.alloc(30);
  await fd.read(lfhBuffer, 0, 30, fileHeaderOffset);

  const compressionMethod = lfhBuffer.readUint16LE(8);
  let compressedLength = lfhBuffer.readUInt32LE(18);
  let length = lfhBuffer.readUInt32LE(22);
  const nameLength = lfhBuffer.readUint16LE(26);
  const extraFieldLength = lfhBuffer.readUInt16LE(28);

  const nameBuffer = Buffer.alloc(nameLength);
  await fd.read(nameBuffer, 0, nameLength, fileHeaderOffset + 30);
  const name = nameBuffer.toString('utf-8');

  if (fileLength === 0) {
    return {
      name,
      filePath: sourcePath,
      crc32: crc32,
      offset: 0,
      compressionMethod: 0,
      compressedLength: 0,
      length: 0
    }
  }

  if (length === 0xFFFFFFFF || compressedLength === 0xFFFFFFFF) {
    let zip64Pos = 4;
    const zip64Buffer = Buffer.alloc(extraFieldLength);
    await fd.read(zip64Buffer, 0, extraFieldLength, fileHeaderOffset + 30 + nameLength);

    if (length === 0xFFFFFFFF) {
      length = Number(zip64Buffer.readBigUInt64LE(zip64Pos));
      zip64Pos += 8;
    }

    if (compressedLength === 0xFFFFFFFF) {
      compressedLength = Number(zip64Buffer.readBigUInt64LE(zip64Pos));
      zip64Pos += 8;
    }
  }

  const trueOffset = fileHeaderOffset + 30 + nameLength + extraFieldLength;

  // Just read the field sizes so we can get the accurate start point

  return {
    name,
    filePath: sourcePath,
    crc32: crc32,
    compressionMethod,
    compressedLength,
    length,
    offset: trueOffset,
  }
}

export async function createStreamFromOffset(zipDataOffset: ZipDataOffset): Promise<ReadStream | null> {
  if (zipDataOffset.length === 0) {
    return null;
  }

  const stream = fs.createReadStream(zipDataOffset.filePath, {
    start: zipDataOffset.offset,
    end: Number(zipDataOffset.offset + zipDataOffset.compressedLength) - 1
  });

  // Pipe deflated data through inflate stream
  if (zipDataOffset.compressionMethod === 8) {
    const inflateStream = createInflateRaw();
    stream.pipe(inflateStream);
    return inflateStream as unknown as ReadStream;
  }

  // Store, pipe back raw data
  return stream;
}
