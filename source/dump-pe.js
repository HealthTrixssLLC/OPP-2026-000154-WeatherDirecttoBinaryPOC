'use strict';
/**
 * Read-only PE inspector. Does not compile anything.
 * Writes receipts proving weather.exe is a native PE32+ console image.
 */
const fs = require('fs');
const path = require('path');

const exe = path.join(__dirname, '..', 'weather.exe');
const outDir = path.join(__dirname, '..', 'receipts');
const buf = fs.readFileSync(exe);

function u16(o) { return buf.readUInt16LE(o); }
function u32(o) { return buf.readUInt32LE(o); }
function u64(o) { return buf.readBigUInt64LE(o); }
function cstr(o, max) {
  let s = '';
  for (let i = 0; i < max; i++) {
    const c = buf[o + i];
    if (!c) break;
    s += String.fromCharCode(c);
  }
  return s;
}

const mz = String.fromCharCode(buf[0], buf[1]);
const e_lfanew = u32(0x3C);
const pe = buf.slice(e_lfanew, e_lfanew + 4).toString('ascii');
const coff = e_lfanew + 4;
const machine = u16(coff);
const nsec = u16(coff + 2);
const optSize = u16(coff + 16);
const chars = u16(coff + 18);
const opt = coff + 20;
const magic = u16(opt);
const entry = u32(opt + 16);
const imageBase = u64(opt + 24);
const sectAlign = u32(opt + 32);
const fileAlign = u32(opt + 36);
const sizeOfImage = u32(opt + 56);
const sizeOfHeaders = u32(opt + 60);
const subsystem = u16(opt + 68);
const dllChars = u16(opt + 70);
const numRva = u32(opt + 108);
const dirs = opt + 112;
const importRva = u32(dirs + 1 * 8);
const importSz = u32(dirs + 1 * 8 + 4);
const iatRva = u32(dirs + 12 * 8);
const iatSz = u32(dirs + 12 * 8 + 4);

const sections = [];
const secOff = opt + optSize;
for (let i = 0; i < nsec; i++) {
  const o = secOff + i * 40;
  sections.push({
    name: buf.slice(o, o + 8).toString('ascii').replace(/\0+$/, ''),
    vsize: u32(o + 8),
    va: u32(o + 12),
    raw: u32(o + 16),
    ptr: u32(o + 20),
    ch: u32(o + 36),
  });
}

function rvaToOff(rva) {
  for (const s of sections) {
    if (rva >= s.va && rva < s.va + Math.max(s.vsize, s.raw)) {
      return s.ptr + (rva - s.va);
    }
  }
  return -1;
}

const imports = [];
if (importRva) {
  let o = rvaToOff(importRva);
  while (o >= 0) {
    const oft = u32(o);
    const nameRva = u32(o + 12);
    const ft = u32(o + 16);
    if (!oft && !nameRva && !ft) break;
    const dll = cstr(rvaToOff(nameRva), 64);
    const fns = [];
    let t = rvaToOff(oft || ft);
    while (t >= 0) {
      const thunk = buf.readBigUInt64LE(t);
      if (thunk === 0n) break;
      if (thunk & (1n << 63n)) {
        fns.push('ordinal ' + Number(thunk & 0xffffn));
      } else {
        const hn = rvaToOff(Number(thunk & 0xffffffffn));
        fns.push(cstr(hn + 2, 64));
      }
      t += 8;
    }
    imports.push({ dll, functions: fns });
    o += 20;
  }
}

const forbidden = ['mscoree.dll', 'mscoreei.dll', 'clr.dll', 'python', 'vcruntime', 'msvcp', 'ucrtbase', 'ntdll'];
const importDlls = imports.map((x) => x.dll.toLowerCase());
const hasDotNet = importDlls.some((d) => d.includes('mscoree') || d.includes('clr'));
const hasCrt = importDlls.some((d) => d.includes('vcruntime') || d.includes('msvcrt') || d.includes('ucrtbase'));

let header = '';
header += 'PE HEADER RECEIPT — weather.exe\r\n';
header += 'Inspector: source/dump-pe.js (Node byte reader, not a compiler)\r\n';
header += 'File: ' + exe + '\r\n';
header += 'Size: ' + buf.length + ' bytes\r\n\r\n';
header += 'DOS signature:        ' + mz + (mz === 'MZ' ? '  PASS' : '  FAIL') + '\r\n';
header += 'e_lfanew:             0x' + e_lfanew.toString(16) + '\r\n';
header += 'PE signature:         ' + JSON.stringify(pe) + (pe === 'PE\u0000\u0000' ? '  PASS' : '  FAIL') + '\r\n';
header += 'Machine:              0x' + machine.toString(16) + (machine === 0x8664 ? '  AMD64 PASS' : '') + '\r\n';
header += 'Sections:             ' + nsec + '\r\n';
header += 'Optional magic:       0x' + magic.toString(16) + (magic === 0x20b ? '  PE32+ PASS' : '') + '\r\n';
header += 'Entry RVA:            0x' + entry.toString(16) + '\r\n';
header += 'ImageBase:            0x' + imageBase.toString(16) + '\r\n';
header += 'SectionAlign:         0x' + sectAlign.toString(16) + '\r\n';
header += 'FileAlign:            0x' + fileAlign.toString(16) + '\r\n';
header += 'SizeOfImage:          0x' + sizeOfImage.toString(16) + '\r\n';
header += 'SizeOfHeaders:        0x' + sizeOfHeaders.toString(16) + '\r\n';
header += 'Subsystem:            ' + subsystem + (subsystem === 3 ? '  CONSOLE PASS' : '') + '\r\n';
header += 'DllCharacteristics:   0x' + dllChars.toString(16) + '\r\n';
header += 'Characteristics:      0x' + chars.toString(16) + '\r\n';
header += 'NumberOfRvaAndSizes:  ' + numRva + '\r\n';
header += 'Import dir RVA/size:  0x' + importRva.toString(16) + ' / ' + importSz + '\r\n';
header += 'IAT RVA/size:         0x' + iatRva.toString(16) + ' / ' + iatSz + '\r\n\r\n';
header += 'SECTIONS\r\n';
for (const s of sections) {
  header += '  ' + s.name.padEnd(8) + ' VA=0x' + s.va.toString(16) +
    ' VSize=' + s.vsize + ' RawPtr=0x' + s.ptr.toString(16) +
    ' RawSize=' + s.raw + ' Ch=0x' + s.ch.toString(16) + '\r\n';
}
header += '\r\nNOT a .NET image (no mscoree): ' + (!hasDotNet ? 'PASS' : 'FAIL') + '\r\n';
header += 'NOT linked to MSVC CRT:          ' + (!hasCrt ? 'PASS' : 'FAIL') + '\r\n';

let imp = 'IMPORT TABLE RECEIPT — weather.exe\r\n';
imp += 'Only Windows system DLLs should appear.\r\n';
imp += 'No compiler runtime, no .NET, no Python.\r\n\r\n';
for (const x of imports) {
  imp += x.dll + '\r\n';
  for (const f of x.functions) imp += '  ' + f + '\r\n';
  imp += '\r\n';
}
imp += 'DLL list: ' + imports.map((x) => x.dll).join(', ') + '\r\n';
imp += '.NET host present: ' + (hasDotNet ? 'YES — FAIL' : 'NO — PASS') + '\r\n';
imp += 'MSVC CRT present:  ' + (hasCrt ? 'YES — FAIL' : 'NO — PASS') + '\r\n';

const ascii = [];
let cur = '';
for (let i = 0; i < buf.length; i++) {
  const c = buf[i];
  if (c >= 32 && c <= 126) cur += String.fromCharCode(c);
  else {
    if (cur.length >= 4) ascii.push(cur);
    cur = '';
  }
}
if (cur.length >= 4) ascii.push(cur);
const interesting = ascii.filter((s) =>
  /Weather|version|1\.0\.0|kernel32|wininet|open-meteo|zippopotam|Enter your|forecast|PE/i.test(s)
);

let str = 'ASCII STRINGS RECEIPT (length >= 4, filtered)\r\n';
str += 'Proves version 1.0.0 and API hosts are inside the native image.\r\n\r\n';
for (const s of interesting) str += s + '\r\n';

fs.writeFileSync(path.join(outDir, 'pe-headers.txt'), header);
fs.writeFileSync(path.join(outDir, 'import-table.txt'), imp);
fs.writeFileSync(path.join(outDir, 'ascii-strings.txt'), str);
console.log('Wrote PE receipts');
console.log(header);
console.log(imp);
