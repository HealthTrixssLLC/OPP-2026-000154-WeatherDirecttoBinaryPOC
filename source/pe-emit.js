'use strict';
/**
 * PE32+ / x64 byte emitter for weather.exe
 *
 * This is NOT the application and NOT a compiler.
 * Node.js only writes PE structures and x64 opcodes as bytes.
 * The resulting weather.exe is native machine code: no C/C#/Go/Rust
 * source, no assembler, no .NET runtime host.
 *
 * Product: Weather CLI
 * Version: 1.0.1
 */
const fs = require('fs');
const path = require('path');

const APP_NAME = 'Weather CLI';
const APP_VERSION = '1.0.1';
const APP_BUILD = '20260919.2';

const RAX = 0, RCX = 1, RDX = 2, RBX = 3, RSP = 4, RBP = 5, RSI = 6, RDI = 7;
const R8 = 8, R9 = 9, R10 = 10, R11 = 11, R12 = 12, R13 = 13, R14 = 14, R15 = 15;

const CC = {
  jb: 2, jae: 3, je: 4, jne: 5, jbe: 6, ja: 7,
  js: 8, jns: 9, jl: 12, jge: 13, jle: 14, jg: 15,
};

function u16(n) {
  n >>>= 0;
  return [n & 255, (n >>> 8) & 255];
}
function u32(n) {
  n >>>= 0;
  return [n & 255, (n >>> 8) & 255, (n >>> 16) & 255, (n >>> 24) & 255];
}
function u64(n) {
  const v = BigInt(n);
  return [...u32(Number(v & 0xffffffffn)), ...u32(Number((v >> 32n) & 0xffffffffn))];
}
function align(n, a) {
  return (n + a - 1) & ~(a - 1);
}
function cstr(s) {
  return [...Buffer.from(s, 'ascii'), 0];
}

class Asm {
  constructor() {
    this.b = [];
    this.labels = Object.create(null);
    this.fixups = [];
  }
  get pos() { return this.b.length; }
  emit(...xs) {
    for (const x of xs) {
      if (Array.isArray(x)) this.emit(...x);
      else this.b.push(x & 255);
    }
  }
  emitU32(n) { this.emit(...u32(n)); }
  emitU64(n) { this.emit(...u64(n)); }
  label(name) {
    if (this.labels[name] !== undefined) throw new Error('dup label ' + name);
    this.labels[name] = this.pos;
  }
  rel32(label) {
    this.fixups.push({ off: this.pos, label, type: 'rel32' });
    this.emitU32(0);
  }
  rip32(label) {
    this.fixups.push({ off: this.pos, label, type: 'rip32' });
    this.emitU32(0);
  }
  emitRex(w, r, x, b) {
    const R = (r >= 8) ? 1 : 0;
    const X = (x != null && x >= 8) ? 1 : 0;
    const B = (b >= 8) ? 1 : 0;
    const v = 0x40 | (w ? 8 : 0) | (R << 2) | (X << 1) | B;
    if (w || R || X || B) this.emit(v);
  }
  rexW(r, x, b) { this.emitRex(1, r, x, b); }
  modrm(mod, reg, rm) { this.emit(((mod & 3) << 6) | ((reg & 7) << 3) | (rm & 7)); }
  emitMem(regField, base, index, disp, scale) {
    if (scale == null) scale = 1;
    const d = disp | 0;
    const hasIdx = index !== null && index !== undefined;
    const baseL = base & 7;
    let mod, emitDisp;
    if (d === 0 && baseL !== 5) {
      mod = 0; emitDisp = 0;
    } else if (d >= -128 && d <= 127) {
      mod = 1; emitDisp = 1;
    } else {
      mod = 2; emitDisp = 4;
    }
    const needSib = hasIdx || baseL === 4;
    if (!needSib) {
      this.modrm(mod, regField, base);
    } else {
      this.modrm(mod, regField, 4);
      const idx = hasIdx ? (index & 7) : 4;
      const sc = { 1: 0, 2: 1, 4: 2, 8: 3 }[scale];
      if (sc === undefined) throw new Error('bad scale ' + scale);
      if (hasIdx && (index & 7) === 4) throw new Error('rsp cannot be index');
      this.emit((sc << 6) | (idx << 3) | baseL);
    }
    if (emitDisp === 1) this.emit(d & 255);
    if (emitDisp === 4) this.emitU32(d);
  }

  push(r) {
    if (r >= 8) this.emit(0x41);
    this.emit(0x50 + (r & 7));
  }
  pop(r) {
    if (r >= 8) this.emit(0x41);
    this.emit(0x58 + (r & 7));
  }
  ret() { this.emit(0xC3); }
  leave() { this.emit(0xC9); }
  cqo() { this.emit(0x48, 0x99); }
  int3() { this.emit(0xCC); }

  mov_rr(dst, src) {
    this.rexW(dst, 0, src);
    this.emit(0x8B);
    this.modrm(3, dst, src);
  }
  mov_ri32(dst, imm) {
    this.emitRex(0, 0, 0, dst);
    this.emit(0xB8 + (dst & 7));
    this.emitU32(imm);
  }
  mov_ri64(dst, imm) {
    this.rexW(0, 0, dst);
    this.emit(0xB8 + (dst & 7));
    this.emitU64(imm);
  }
  xor_r(r) {
    this.emitRex(0, r, 0, r);
    this.emit(0x33);
    this.modrm(3, r, r);
  }
  add_rr(dst, src) {
    this.rexW(dst, 0, src);
    this.emit(0x03);
    this.modrm(3, dst, src);
  }
  sub_rr(dst, src) {
    this.rexW(dst, 0, src);
    this.emit(0x2B);
    this.modrm(3, dst, src);
  }
  cmp_rr(dst, src) {
    this.rexW(dst, 0, src);
    this.emit(0x3B);
    this.modrm(3, dst, src);
  }
  test_rr(a, b) {
    this.rexW(a, 0, b);
    this.emit(0x85);
    this.modrm(3, a, b);
  }
  test_rr32(a, b) {
    this.emitRex(0, a, 0, b);
    this.emit(0x85);
    this.modrm(3, a, b);
  }
  alu_ri(dst, imm, ext) {
    this.rexW(0, 0, dst);
    if (imm >= -128 && imm <= 127) {
      this.emit(0x83);
      this.modrm(3, ext, dst);
      this.emit(imm & 255);
    } else {
      this.emit(0x81);
      this.modrm(3, ext, dst);
      this.emitU32(imm);
    }
  }
  add_ri(dst, imm) { this.alu_ri(dst, imm, 0); }
  or_ri(dst, imm) { this.alu_ri(dst, imm, 1); }
  and_ri(dst, imm) { this.alu_ri(dst, imm, 4); }
  sub_ri(dst, imm) { this.alu_ri(dst, imm, 5); }
  cmp_ri(dst, imm) { this.alu_ri(dst, imm, 7); }
  inc(r) {
    this.rexW(0, 0, r);
    this.emit(0xFF);
    this.modrm(3, 0, r);
  }
  dec(r) {
    this.rexW(0, 0, r);
    this.emit(0xFF);
    this.modrm(3, 1, r);
  }
  neg(r) {
    this.rexW(0, 0, r);
    this.emit(0xF7);
    this.modrm(3, 3, r);
  }
  imul_rr(dst, src) {
    this.rexW(dst, 0, src);
    this.emit(0x0F, 0xAF);
    this.modrm(3, dst, src);
  }
  imul_ri(dst, imm) {
    this.rexW(dst, 0, dst);
    if (imm >= -128 && imm <= 127) {
      this.emit(0x6B);
      this.modrm(3, dst, dst);
      this.emit(imm & 255);
    } else {
      this.emit(0x69);
      this.modrm(3, dst, dst);
      this.emitU32(imm);
    }
  }
  div(r) {
    this.rexW(0, 0, r);
    this.emit(0xF7);
    this.modrm(3, 6, r);
  }
  idiv(r) {
    this.rexW(0, 0, r);
    this.emit(0xF7);
    this.modrm(3, 7, r);
  }
  shr_ri(r, imm) {
    this.rexW(0, 0, r);
    this.emit(0xC1);
    this.modrm(3, 5, r);
    this.emit(imm);
  }
  shl_ri(r, imm) {
    this.rexW(0, 0, r);
    this.emit(0xC1);
    this.modrm(3, 4, r);
    this.emit(imm);
  }
  lea_rip(dst, label) {
    this.rexW(dst, 0, 0);
    this.emit(0x8D);
    this.modrm(0, dst, 5);
    this.rip32(label);
  }
  mov_from_rip(dst, label) {
    this.rexW(dst, 0, 0);
    this.emit(0x8B);
    this.modrm(0, dst, 5);
    this.rip32(label);
  }
  mov_to_rip(src, label) {
    this.rexW(src, 0, 0);
    this.emit(0x89);
    this.modrm(0, src, 5);
    this.rip32(label);
  }
  mov_r32_from_rip(dst, label) {
    this.emitRex(0, dst, 0, 0);
    this.emit(0x8B);
    this.modrm(0, dst, 5);
    this.rip32(label);
  }
  lea_m(dst, base, index, disp, scale) {
    this.emitRex(1, dst, index, base);
    this.emit(0x8D);
    this.emitMem(dst, base, index, disp || 0, scale);
  }
  mov_rm(dst, base, index, disp, scale) {
    this.emitRex(1, dst, index, base);
    this.emit(0x8B);
    this.emitMem(dst, base, index, disp || 0, scale);
  }
  mov_mr(src, base, index, disp, scale) {
    this.emitRex(1, src, index, base);
    this.emit(0x89);
    this.emitMem(src, base, index, disp || 0, scale);
  }
  movzx8_rm(dst, base, index, disp, scale) {
    this.emitRex(1, dst, index, base);
    this.emit(0x0F, 0xB6);
    this.emitMem(dst, base, index, disp || 0, scale);
  }
  mov8_mr(src, base, index, disp, scale) {
    this.emitRex(0, src, index, base);
    this.emit(0x88);
    this.emitMem(src, base, index, disp || 0, scale);
  }
  mov8_mi(base, index, disp, imm, scale) {
    this.emitRex(0, 0, index, base);
    this.emit(0xC6);
    this.emitMem(0, base, index, disp || 0, scale);
    this.emit(imm);
  }
  cmp8_mi(base, index, disp, imm, scale) {
    this.emitRex(0, 0, index, base);
    this.emit(0x80);
    this.emitMem(7, base, index, disp || 0, scale);
    this.emit(imm);
  }
  cmp8_rr(a, b) {
    this.emitRex(0, a, 0, b);
    this.emit(0x3A);
    this.modrm(3, a, b);
  }
  call_iat(name) {
    this.emit(0xFF, 0x15);
    this.rip32(name);
  }
  call_lab(name) {
    this.emit(0xE8);
    this.rel32(name);
  }
  jmp(name) {
    this.emit(0xE9);
    this.rel32(name);
  }
  jcc(cc, name) {
    this.emit(0x0F, 0x80 + cc);
    this.rel32(name);
  }
  je(n) { this.jcc(CC.je, n); }
  jne(n) { this.jcc(CC.jne, n); }
  jl(n) { this.jcc(CC.jl, n); }
  jge(n) { this.jcc(CC.jge, n); }
  jle(n) { this.jcc(CC.jle, n); }
  jg(n) { this.jcc(CC.jg, n); }
  ja(n) { this.jcc(CC.ja, n); }
  jb(n) { this.jcc(CC.jb, n); }
  jae(n) { this.jcc(CC.jae, n); }
  jbe(n) { this.jcc(CC.jbe, n); }
  js(n) { this.jcc(CC.js, n); }
  jns(n) { this.jcc(CC.jns, n); }

  prolog() {
    this.push(RBP);
    this.mov_rr(RBP, RSP);
    this.sub_ri(RSP, 0x100);
    this.and_ri(RSP, -16);
  }
  epilog() {
    this.leave();
    this.ret();
  }

  resolve(textRva, symbols) {
    for (const f of this.fixups) {
      let target;
      if (this.labels[f.label] !== undefined) target = textRva + this.labels[f.label];
      else if (symbols[f.label] !== undefined) target = symbols[f.label];
      else throw new Error('unknown label ' + f.label);
      const next = textRva + f.off + 4;
      const disp = (target - next) | 0;
      const v = disp >>> 0;
      this.b[f.off] = v & 255;
      this.b[f.off + 1] = (v >>> 8) & 255;
      this.b[f.off + 2] = (v >>> 16) & 255;
      this.b[f.off + 3] = (v >>> 24) & 255;
    }
  }
}

const K32 = [
  'GetStdHandle',
  'WriteFile',
  'ReadFile',
  'GetProcessHeap',
  'HeapAlloc',
  'HeapFree',
  'ExitProcess',
];
const WININET = [
  'InternetOpenA',
  'InternetOpenUrlA',
  'InternetReadFile',
  'InternetCloseHandle',
];

const STRINGS = {
  s_prompt_name: 'Enter your name: ',
  s_prompt_zip: 'Enter ZIP code: ',
  s_err_name: 'Name cannot be empty.\r\n',
  s_err_zip: 'Please enter a 5-digit US ZIP code.\r\n',
  s_err_loc: 'Could not find location for ZIP ',
  s_err_net: 'Could not reach weather service. Check your internet connection.\r\n',
  s_fetching: 'Fetching weather...\r\n',
  s_here: ' here is the forecast for ',
  s_now: 'Now: ',
  s_unit_f: ' F',
  s_crlf: '\r\n',
  s_high: '  High: ',
  s_low: '  Low: ',
  s_precip: '  Precipitation: ',
  s_pct: '%',
  s_space: ' ',
  s_attr: 'Data: Open-Meteo.com (CC BY 4.0)\r\n',
  s_banner: 'Weather CLI v1.0.1\r\n',
  s_agent: 'WeatherCli/1.0.1',
  s_headers: 'User-Agent: WeatherCli/1.0.1\r\n',
  s_version: '1.0.1',
  s_pause: '\r\nPress Enter to close...',
  s_url_zip: 'https://api.zippopotam.us/us/',
  s_url_f1: 'https://api.open-meteo.com/v1/forecast?latitude=',
  s_url_f2: '&longitude=',
  s_url_f3: '&current=temperature_2m&daily=temperature_2m_max,temperature_2m_min,precipitation_probability_max&temperature_unit=fahrenheit&timezone=auto&forecast_days=7',
  s_key_lat: '"latitude"',
  s_key_lon: '"longitude"',
  s_key_current: '"current":',
  s_key_daily: '"daily":',
  s_key_t2m: '"temperature_2m":',
  s_key_tmax: '"temperature_2m_max":',
  s_key_tmin: '"temperature_2m_min":',
  s_key_pop: '"precipitation_probability_max":',
  s_key_time: '"time":[',
};

const DAYS = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];

const DATA_FIELDS = [
  ['d_hIn', 8],
  ['d_hOut', 8],
  ['d_hHeap', 8],
  ['d_httpBuf', 8],
  ['d_httpLen', 8],
  ['d_ioCount', 8],
  ['d_current', 8],
  ['d_name', 256],
  ['d_zip', 32],
  ['d_url', 2048],
  ['d_lat', 32],
  ['d_lon', 32],
  ['d_tmp', 64],
  ['d_dates', 7 * 16],
  ['d_highs', 7 * 8],
  ['d_lows', 7 * 8],
  ['d_precips', 7 * 8],
  ['d_save', 64],
  ['d_exitCode', 8],
];

function emitProgram(a) {
  // ---------- strlen: rcx=ptr -> rax=len (rcx preserved) ----------
  a.label('strlen');
  a.xor_r(RAX);
  a.label('strlen_loop');
  a.cmp8_mi(RCX, RAX, 0, 0);
  a.je('strlen_done');
  a.inc(RAX);
  a.jmp('strlen_loop');
  a.label('strlen_done');
  a.ret();

  // ---------- strcpy: rcx=dest rdx=src ----------
  a.label('strcpy');
  a.label('strcpy_loop');
  a.movzx8_rm(RAX, RDX, null, 0);
  a.mov8_mr(RAX, RCX, null, 0);
  a.inc(RDX);
  a.inc(RCX);
  a.test_rr32(RAX, RAX);
  a.jne('strcpy_loop');
  a.ret();

  // ---------- append: rcx=dest rdx=src ----------
  a.label('append');
  a.push(RDX);
  a.call_lab('strlen');
  a.pop(RDX);
  a.add_rr(RCX, RAX);
  a.call_lab('strcpy');
  a.ret();

  // ---------- skip_ws: rcx=ptr -> rcx advanced ----------
  a.label('skip_ws');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.cmp_ri(RAX, 0x20);
  a.je('skip_ws_inc');
  a.cmp_ri(RAX, 9);
  a.je('skip_ws_inc');
  a.ret();
  a.label('skip_ws_inc');
  a.inc(RCX);
  a.jmp('skip_ws');

  // ---------- find: rcx=haystack rdx=needle -> rax=match or 0 ----------
  a.label('find');
  a.movzx8_rm(RAX, RDX, null, 0);
  a.test_rr32(RAX, RAX);
  a.je('find_ret_hay');
  a.label('find_outer');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.test_rr32(RAX, RAX);
  a.je('find_fail');
  a.mov_rr(R8, RCX);
  a.mov_rr(R9, RDX);
  a.label('find_inner');
  a.movzx8_rm(RAX, R9, null, 0);
  a.test_rr32(RAX, RAX);
  a.je('find_found');
  a.movzx8_rm(R10, R8, null, 0);
  a.test_rr32(R10, R10);
  a.je('find_fail');
  a.cmp8_rr(RAX, R10);
  a.jne('find_next');
  a.inc(R8);
  a.inc(R9);
  a.jmp('find_inner');
  a.label('find_next');
  a.inc(RCX);
  a.jmp('find_outer');
  a.label('find_found');
  a.mov_rr(RAX, RCX);
  a.ret();
  a.label('find_fail');
  a.xor_r(RAX);
  a.ret();
  a.label('find_ret_hay');
  a.mov_rr(RAX, RCX);
  a.ret();

  // ---------- extract_value: rcx=after_key rdx=dest -> rax 1/0 ----------
  a.label('extract_value');
  a.mov_rr(R11, RDX);
  a.call_lab('skip_ws');
  a.cmp8_mi(RCX, null, 0, 0x3A); // :
  a.jne('ev_fail');
  a.inc(RCX);
  a.call_lab('skip_ws');
  a.cmp8_mi(RCX, null, 0, 0x22); // "
  a.je('ev_quoted');
  a.xor_r(R8);
  a.label('ev_num');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.cmp_ri(RAX, 0x2B); // +
  a.je('ev_num_ok');
  a.cmp_ri(RAX, 0x2D); // -
  a.je('ev_num_ok');
  a.cmp_ri(RAX, 0x2E); // .
  a.je('ev_num_ok');
  a.cmp_ri(RAX, 0x30);
  a.jb('ev_num_done');
  a.cmp_ri(RAX, 0x39);
  a.ja('ev_num_done');
  a.label('ev_num_ok');
  a.cmp_ri(R8, 30);
  a.jae('ev_num_done');
  a.mov8_mr(RAX, R11, R8, 0);
  a.inc(R8);
  a.inc(RCX);
  a.jmp('ev_num');
  a.label('ev_num_done');
  a.mov8_mi(R11, R8, 0, 0);
  a.test_rr(R8, R8);
  a.je('ev_fail');
  a.mov_ri32(RAX, 1);
  a.ret();
  a.label('ev_quoted');
  a.inc(RCX);
  a.xor_r(R8);
  a.label('ev_qloop');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.test_rr32(RAX, RAX);
  a.je('ev_fail');
  a.cmp_ri(RAX, 0x22);
  a.je('ev_qdone');
  a.cmp_ri(R8, 30);
  a.jae('ev_qdone');
  a.mov8_mr(RAX, R11, R8, 0);
  a.inc(R8);
  a.inc(RCX);
  a.jmp('ev_qloop');
  a.label('ev_qdone');
  a.mov8_mi(R11, R8, 0, 0);
  a.mov_ri32(RAX, 1);
  a.ret();
  a.label('ev_fail');
  a.xor_r(RAX);
  a.ret();

  // ---------- trim in-place rcx=buf ----------
  a.label('trim');
  a.mov_rr(RDX, RCX);
  a.label('tr_lead');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.cmp_ri(RAX, 0x20);
  a.je('tr_linc');
  a.cmp_ri(RAX, 9);
  a.je('tr_linc');
  a.jmp('tr_copy');
  a.label('tr_linc');
  a.inc(RCX);
  a.jmp('tr_lead');
  a.label('tr_copy');
  a.mov_rr(R8, RDX);
  a.label('tr_cploop');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.mov8_mr(RAX, R8, null, 0);
  a.inc(RCX);
  a.inc(R8);
  a.test_rr32(RAX, RAX);
  a.jne('tr_cploop');
  a.dec(R8);
  a.label('tr_trail');
  a.cmp_rr(R8, RDX);
  a.jbe('tr_done');
  a.dec(R8);
  a.movzx8_rm(RAX, R8, null, 0);
  a.cmp_ri(RAX, 0x20);
  a.je('tr_z');
  a.cmp_ri(RAX, 9);
  a.je('tr_z');
  a.jmp('tr_done');
  a.label('tr_z');
  a.mov8_mi(R8, null, 0, 0);
  a.jmp('tr_trail');
  a.label('tr_done');
  a.ret();

  // ---------- validate_zip rcx=buf -> rax 1/0, may truncate ZIP+4 ----------
  a.label('validate_zip');
  a.mov_rr(R8, RCX);
  a.call_lab('strlen');
  a.cmp_ri(RAX, 5);
  a.je('vz5');
  a.cmp_ri(RAX, 10);
  a.je('vz10');
  a.label('vz_bad');
  a.xor_r(RAX);
  a.ret();
  a.label('vz5');
  a.xor_r(R9);
  a.label('vz5l');
  a.cmp_ri(R9, 5);
  a.jae('vz_ok');
  a.movzx8_rm(RAX, R8, R9, 0);
  a.cmp_ri(RAX, 0x30);
  a.jb('vz_bad');
  a.cmp_ri(RAX, 0x39);
  a.ja('vz_bad');
  a.inc(R9);
  a.jmp('vz5l');
  a.label('vz10');
  a.cmp8_mi(R8, null, 5, 0x2D);
  a.jne('vz_bad');
  a.xor_r(R9);
  a.label('vz10a');
  a.cmp_ri(R9, 5);
  a.jae('vz10b');
  a.movzx8_rm(RAX, R8, R9, 0);
  a.cmp_ri(RAX, 0x30);
  a.jb('vz_bad');
  a.cmp_ri(RAX, 0x39);
  a.ja('vz_bad');
  a.inc(R9);
  a.jmp('vz10a');
  a.label('vz10b');
  a.mov_ri32(R9, 6);
  a.label('vz10c');
  a.cmp_ri(R9, 10);
  a.jae('vz10d');
  a.movzx8_rm(RAX, R8, R9, 0);
  a.cmp_ri(RAX, 0x30);
  a.jb('vz_bad');
  a.cmp_ri(RAX, 0x39);
  a.ja('vz_bad');
  a.inc(R9);
  a.jmp('vz10c');
  a.label('vz10d');
  a.mov8_mi(R8, null, 5, 0);
  a.label('vz_ok');
  a.mov_ri32(RAX, 1);
  a.ret();

  // ---------- parse_number: rcx=ptr -> rax=rounded, rdx=newptr ----------
  a.label('parse_number');
  a.xor_r(R8);
  a.xor_r(R9);
  a.cmp8_mi(RCX, null, 0, 0x2D);
  a.jne('pn_int');
  a.mov_ri32(R8, 1);
  a.inc(RCX);
  a.label('pn_int');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.cmp_ri(RAX, 0x30);
  a.jb('pn_frac');
  a.cmp_ri(RAX, 0x39);
  a.ja('pn_frac');
  a.imul_ri(R9, 10);
  a.sub_ri(RAX, 0x30);
  a.add_rr(R9, RAX);
  a.inc(RCX);
  a.jmp('pn_int');
  a.label('pn_frac');
  a.xor_r(R10);
  a.cmp8_mi(RCX, null, 0, 0x2E);
  a.jne('pn_done');
  a.inc(RCX);
  a.movzx8_rm(RAX, RCX, null, 0);
  a.cmp_ri(RAX, 0x30);
  a.jb('pn_done');
  a.cmp_ri(RAX, 0x39);
  a.ja('pn_done');
  a.cmp_ri(RAX, 0x35);
  a.jb('pn_skipmore');
  a.mov_ri32(R10, 1);
  a.label('pn_skipmore');
  a.inc(RCX);
  a.movzx8_rm(RAX, RCX, null, 0);
  a.cmp_ri(RAX, 0x30);
  a.jb('pn_done');
  a.cmp_ri(RAX, 0x39);
  a.ja('pn_done');
  a.jmp('pn_skipmore');
  a.label('pn_done');
  a.mov_rr(RAX, R9);
  a.add_rr(RAX, R10);
  a.test_rr(R8, R8);
  a.je('pn_pos');
  a.neg(RAX);
  a.label('pn_pos');
  a.mov_rr(RDX, RCX);
  a.ret();

  // ---------- itoa: rcx=signed rdx=dest ----------
  a.label('itoa');
  a.mov_rr(R8, RDX);
  a.test_rr(RCX, RCX);
  a.jns('itoa_chk0');
  a.mov8_mi(R8, null, 0, 0x2D);
  a.inc(R8);
  a.neg(RCX);
  a.label('itoa_chk0');
  a.test_rr(RCX, RCX);
  a.jne('itoa_div');
  a.mov8_mi(R8, null, 0, 0x30);
  a.inc(R8);
  a.jmp('itoa_term');
  a.label('itoa_div');
  a.xor_r(R10);
  a.label('itoa_loop');
  a.mov_rr(RAX, RCX);
  a.xor_r(RDX);
  a.mov_ri32(R11, 10);
  a.div(R11);
  a.mov_rr(RCX, RAX);
  a.add_ri(RDX, 0x30);
  a.push(RDX);
  a.inc(R10);
  a.test_rr(RCX, RCX);
  a.jne('itoa_loop');
  a.label('itoa_pop');
  a.pop(RAX);
  a.mov8_mr(RAX, R8, null, 0);
  a.inc(R8);
  a.dec(R10);
  a.jne('itoa_pop');
  a.label('itoa_term');
  a.mov8_mi(R8, null, 0, 0);
  a.ret();

  // ---------- weekday: rcx=year rdx=month r8=day -> rax 0=Sun ----------
  a.label('weekday');
  a.push(R12);
  a.push(R13);
  a.mov_rr(R11, RCX);
  a.mov_rr(R9, RDX);
  a.mov_rr(R10, R8);
  a.cmp_ri(R9, 3);
  a.jge('wd_ok');
  a.add_ri(R9, 12);
  a.dec(R11);
  a.label('wd_ok');
  a.mov_rr(RAX, R11);
  a.xor_r(RDX);
  a.mov_ri32(R8, 100);
  a.div(R8);
  a.mov_rr(R12, RAX); // J
  a.mov_rr(R13, RDX); // K
  a.mov_rr(RAX, R9);
  a.inc(RAX);
  a.imul_ri(RAX, 13);
  a.xor_r(RDX);
  a.mov_ri32(R8, 5);
  a.div(R8);
  a.add_rr(RAX, R10);
  a.add_rr(RAX, R13);
  a.mov_rr(RCX, R13);
  a.shr_ri(RCX, 2);
  a.add_rr(RAX, RCX);
  a.mov_rr(RCX, R12);
  a.shr_ri(RCX, 2);
  a.add_rr(RAX, RCX);
  a.mov_rr(RCX, R12);
  a.add_rr(RCX, R12);
  a.sub_rr(RAX, RCX);
  a.cqo();
  a.mov_ri32(R8, 7);
  a.idiv(R8);
  a.test_rr(RDX, RDX);
  a.jns('wd_modok');
  a.add_ri(RDX, 7);
  a.label('wd_modok');
  a.add_ri(RDX, 6);
  a.mov_rr(RAX, RDX);
  a.xor_r(RDX);
  a.mov_ri32(R8, 7);
  a.div(R8);
  a.mov_rr(RAX, RDX);
  a.pop(R13);
  a.pop(R12);
  a.ret();

  // ---------- print: rcx=cstr ----------
  a.label('print');
  a.prolog();
  a.mov_mr(RBX, RBP, null, -8);
  a.mov_rr(RBX, RCX);
  a.call_lab('strlen');
  a.mov_from_rip(RCX, 'd_hOut');
  a.mov_rr(RDX, RBX);
  a.mov_rr(R8, RAX);
  a.lea_rip(R9, 'd_ioCount');
  a.xor_r(RAX);
  a.mov_mr(RAX, RSP, null, 0x20);
  a.call_iat('iat_WriteFile');
  a.mov_rm(RBX, RBP, null, -8);
  a.epilog();

  // ---------- print_i32: rcx=number ----------
  a.label('print_i32');
  a.prolog();
  a.lea_rip(RDX, 'd_tmp');
  a.call_lab('itoa');
  a.lea_rip(RCX, 'd_tmp');
  a.call_lab('print');
  a.epilog();

  // ---------- read_line: rcx=buf rdx=max ----------
  a.label('read_line');
  a.prolog();
  a.mov_mr(RBX, RBP, null, -8);
  a.mov_mr(R12, RBP, null, -16);
  a.mov_mr(R13, RBP, null, -24);
  a.mov_rr(RBX, RCX);
  a.mov_rr(R12, RDX);
  a.dec(R12);
  a.xor_r(R13);
  a.label('rl_loop');
  a.xor_r(RAX);
  a.mov_to_rip(RAX, 'd_ioCount');
  a.mov_from_rip(RCX, 'd_hIn');
  a.lea_rip(RDX, 'd_tmp');
  a.mov_ri32(R8, 1);
  a.lea_rip(R9, 'd_ioCount');
  a.xor_r(RAX);
  a.mov_mr(RAX, RSP, null, 0x20);
  a.call_iat('iat_ReadFile');
  a.mov_r32_from_rip(RAX, 'd_ioCount');
  a.test_rr32(RAX, RAX);
  a.je('rl_done');
  a.lea_rip(RDX, 'd_tmp');
  a.movzx8_rm(RAX, RDX, null, 0);
  a.cmp_ri(RAX, 10);
  a.je('rl_done');
  a.cmp_ri(RAX, 13);
  a.je('rl_loop');
  a.cmp_rr(R13, R12);
  a.jae('rl_loop');
  a.mov8_mr(RAX, RBX, R13, 0);
  a.inc(R13);
  a.jmp('rl_loop');
  a.label('rl_done');
  a.mov8_mi(RBX, R13, 0, 0);
  a.mov_rr(RAX, R13);
  a.mov_rm(RBX, RBP, null, -8);
  a.mov_rm(R12, RBP, null, -16);
  a.mov_rm(R13, RBP, null, -24);
  a.epilog();

  // ---------- http_get: rcx=url -> rax=length ----------
  a.label('http_get');
  a.prolog();
  a.mov_mr(RBX, RBP, null, -8);
  a.mov_mr(R12, RBP, null, -16);
  a.mov_mr(R13, RBP, null, -24);
  a.mov_mr(R14, RBP, null, -32);
  a.mov_rr(R14, RCX);
  a.lea_rip(RCX, 's_agent');
  a.mov_ri32(RDX, 1); // INTERNET_OPEN_TYPE_DIRECT
  a.xor_r(R8);
  a.xor_r(R9);
  a.xor_r(RAX);
  a.mov_mr(RAX, RSP, null, 0x20);
  a.call_iat('iat_InternetOpenA');
  a.test_rr(RAX, RAX);
  a.je('hg_fail');
  a.mov_rr(RBX, RAX); // hInet
  a.mov_rr(RCX, RBX);
  a.mov_rr(RDX, R14);
  a.lea_rip(R8, 's_headers');
  a.mov_ri32(R9, 0xFFFFFFFF);
  a.mov_ri32(RAX, 0x84800200);
  a.mov_mr(RAX, RSP, null, 0x20);
  a.xor_r(RAX);
  a.mov_mr(RAX, RSP, null, 0x28);
  a.call_iat('iat_InternetOpenUrlA');
  a.test_rr(RAX, RAX);
  a.je('hg_fail_inet');
  a.mov_rr(R12, RAX); // hUrl
  a.xor_r(R13); // total
  a.label('hg_read');
  a.mov_ri32(RAX, 65535);
  a.sub_rr(RAX, R13);
  a.jle('hg_done');
  a.xor_r(RDX);
  a.mov_to_rip(RDX, 'd_ioCount');
  a.mov_rr(RCX, R12);
  a.mov_from_rip(RDX, 'd_httpBuf');
  a.add_rr(RDX, R13);
  a.mov_rr(R8, RAX);
  a.lea_rip(R9, 'd_ioCount');
  a.call_iat('iat_InternetReadFile');
  a.test_rr32(RAX, RAX);
  a.je('hg_done');
  a.mov_r32_from_rip(RAX, 'd_ioCount');
  a.test_rr32(RAX, RAX);
  a.je('hg_done');
  a.add_rr(R13, RAX);
  a.jmp('hg_read');
  a.label('hg_done');
  a.mov_from_rip(RAX, 'd_httpBuf');
  a.add_rr(RAX, R13);
  a.mov8_mi(RAX, null, 0, 0);
  a.mov_to_rip(R13, 'd_httpLen');
  a.mov_rr(RCX, R12);
  a.call_iat('iat_InternetCloseHandle');
  a.mov_rr(RCX, RBX);
  a.call_iat('iat_InternetCloseHandle');
  a.mov_rr(RAX, R13);
  a.jmp('hg_rest');
  a.label('hg_fail_inet');
  a.mov_rr(RCX, RBX);
  a.call_iat('iat_InternetCloseHandle');
  a.label('hg_fail');
  a.xor_r(RAX);
  a.xor_r(R13);
  a.mov_to_rip(R13, 'd_httpLen');
  a.label('hg_rest');
  a.mov_rm(RBX, RBP, null, -8);
  a.mov_rm(R12, RBP, null, -16);
  a.mov_rm(R13, RBP, null, -24);
  a.mov_rm(R14, RBP, null, -32);
  a.epilog();

  // ---------- lookup_key: rcx=haystack rdx=key -> rax=after key or 0 ----------
  a.label('lookup_key');
  a.push(RSI);
  a.push(RDI);
  a.mov_rr(RSI, RDX);
  a.call_lab('find');
  a.test_rr(RAX, RAX);
  a.je('lk_fail');
  a.mov_rr(RDI, RAX);
  a.mov_rr(RCX, RSI);
  a.call_lab('strlen');
  a.add_rr(RDI, RAX);
  a.mov_rr(RAX, RDI);
  a.pop(RDI);
  a.pop(RSI);
  a.ret();
  a.label('lk_fail');
  a.pop(RDI);
  a.pop(RSI);
  a.ret();

  // ---------- parse_num_array: rcx=ptr_at_[  rdx=dest_i64  r8=count ----------
  a.label('parse_num_array');
  a.prolog();
  a.mov_mr(RBX, RBP, null, -8);
  a.mov_mr(R12, RBP, null, -16);
  a.mov_mr(R13, RBP, null, -24);
  a.mov_rr(RBX, RDX);
  a.mov_rr(R12, R8);
  a.inc(RCX);
  a.xor_r(R13);
  a.label('pna_loop');
  a.cmp_rr(R13, R12);
  a.jae('pna_done');
  a.call_lab('skip_ws');
  a.cmp8_mi(RCX, null, 0, 0x2C);
  a.jne('pna_parse');
  a.inc(RCX);
  a.call_lab('skip_ws');
  a.label('pna_parse');
  a.call_lab('parse_number');
  a.mov_mr(RAX, RBX, R13, 0, 8);
  a.mov_rr(RCX, RDX);
  a.inc(R13);
  a.jmp('pna_loop');
  a.label('pna_done');
  a.mov_rm(RBX, RBP, null, -8);
  a.mov_rm(R12, RBP, null, -16);
  a.mov_rm(R13, RBP, null, -24);
  a.epilog();

  // ---------- parse_date_array: rcx=ptr_at_[  rdx=dest 16-byte slots r8=count ----------
  a.label('parse_date_array');
  a.prolog();
  a.mov_mr(RBX, RBP, null, -8);
  a.mov_mr(R12, RBP, null, -16);
  a.mov_mr(R13, RBP, null, -24);
  a.mov_rr(RBX, RDX);
  a.mov_rr(R12, R8);
  a.inc(RCX);
  a.xor_r(R13);
  a.label('pda_loop');
  a.cmp_rr(R13, R12);
  a.jae('pda_done');
  a.call_lab('skip_ws');
  a.cmp8_mi(RCX, null, 0, 0x2C);
  a.jne('pda_str');
  a.inc(RCX);
  a.call_lab('skip_ws');
  a.label('pda_str');
  a.cmp8_mi(RCX, null, 0, 0x22);
  a.jne('pda_done');
  a.inc(RCX);
  a.mov_rr(R8, R13);
  a.shl_ri(R8, 4);
  a.lea_m(R9, RBX, R8, 0);
  a.xor_r(R10);
  a.label('pda_copy');
  a.movzx8_rm(RAX, RCX, null, 0);
  a.test_rr32(RAX, RAX);
  a.je('pda_term');
  a.cmp_ri(RAX, 0x22);
  a.je('pda_term');
  a.cmp_ri(R10, 14);
  a.jae('pda_term');
  a.mov8_mr(RAX, R9, R10, 0);
  a.inc(R10);
  a.inc(RCX);
  a.jmp('pda_copy');
  a.label('pda_term');
  a.mov8_mi(R9, R10, 0, 0);
  a.cmp8_mi(RCX, null, 0, 0x22);
  a.jne('pda_next');
  a.inc(RCX);
  a.label('pda_next');
  a.inc(R13);
  a.jmp('pda_loop');
  a.label('pda_done');
  a.mov_rm(RBX, RBP, null, -8);
  a.mov_rm(R12, RBP, null, -16);
  a.mov_rm(R13, RBP, null, -24);
  a.epilog();

  // ---------- pause so a double-clicked console stays open ----------
  // rcx = exit code. Prints "Press Enter to close..." then waits.
  // Piped stdin hits EOF immediately and does not hang tests.
  a.label('pause_exit');
  a.mov_to_rip(RCX, 'd_exitCode');
  a.lea_rip(RCX, 's_pause');
  a.call_lab('print');
  a.lea_rip(RCX, 'd_tmp');
  a.mov_ri32(RDX, 16);
  a.call_lab('read_line');
  a.mov_from_rip(RCX, 'd_exitCode');
  a.call_iat('iat_ExitProcess');

  // ---------- die_net / die_loc / exit ----------
  a.label('die_net');
  a.lea_rip(RCX, 's_err_net');
  a.call_lab('print');
  a.mov_ri32(RCX, 1);
  a.jmp('pause_exit');

  a.label('die_loc');
  a.lea_rip(RCX, 's_err_loc');
  a.call_lab('print');
  a.lea_rip(RCX, 'd_zip');
  a.call_lab('print');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.mov_ri32(RCX, 1);
  a.jmp('pause_exit');

  // ---------- entry / main ----------
  a.label('entry');
  a.prolog();
  a.mov_mr(RBX, RBP, null, -8);
  a.mov_mr(R12, RBP, null, -16);
  a.mov_mr(R13, RBP, null, -24);
  a.mov_mr(R14, RBP, null, -32);
  a.mov_mr(R15, RBP, null, -40);

  a.mov_ri32(RCX, 0xFFFFFFF5); // STD_OUTPUT_HANDLE
  a.call_iat('iat_GetStdHandle');
  a.mov_to_rip(RAX, 'd_hOut');
  a.mov_ri32(RCX, 0xFFFFFFF6); // STD_INPUT_HANDLE
  a.call_iat('iat_GetStdHandle');
  a.mov_to_rip(RAX, 'd_hIn');

  a.call_iat('iat_GetProcessHeap');
  a.mov_to_rip(RAX, 'd_hHeap');
  a.mov_rr(RCX, RAX);
  a.mov_ri32(RDX, 8);
  a.mov_ri32(R8, 65536);
  a.call_iat('iat_HeapAlloc');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_to_rip(RAX, 'd_httpBuf');

  a.lea_rip(RCX, 's_banner');
  a.call_lab('print');

  // name prompt
  a.xor_r(R12);
  a.label('name_loop');
  a.cmp_ri(R12, 10);
  a.jae('die_net');
  a.lea_rip(RCX, 's_prompt_name');
  a.call_lab('print');
  a.lea_rip(RCX, 'd_name');
  a.mov_ri32(RDX, 200);
  a.call_lab('read_line');
  a.lea_rip(RCX, 'd_name');
  a.call_lab('trim');
  a.lea_rip(RCX, 'd_name');
  a.call_lab('strlen');
  a.test_rr(RAX, RAX);
  a.jne('name_ok');
  a.lea_rip(RCX, 's_err_name');
  a.call_lab('print');
  a.inc(R12);
  a.jmp('name_loop');
  a.label('name_ok');

  // zip prompt
  a.xor_r(R12);
  a.label('zip_loop');
  a.cmp_ri(R12, 3);
  a.jae('zip_giveup');
  a.lea_rip(RCX, 's_prompt_zip');
  a.call_lab('print');
  a.lea_rip(RCX, 'd_zip');
  a.mov_ri32(RDX, 20);
  a.call_lab('read_line');
  a.lea_rip(RCX, 'd_zip');
  a.call_lab('trim');
  a.lea_rip(RCX, 'd_zip');
  a.call_lab('validate_zip');
  a.test_rr(RAX, RAX);
  a.jne('zip_ok');
  a.lea_rip(RCX, 's_err_zip');
  a.call_lab('print');
  a.inc(R12);
  a.jmp('zip_loop');
  a.label('zip_giveup');
  a.mov_ri32(RCX, 1);
  a.jmp('pause_exit');
  a.label('zip_ok');

  a.lea_rip(RCX, 's_fetching');
  a.call_lab('print');

  // zip URL
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 's_url_zip');
  a.call_lab('strcpy');
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 'd_zip');
  a.call_lab('append');
  a.lea_rip(RCX, 'd_url');
  a.call_lab('http_get');
  a.test_rr(RAX, RAX);
  a.je('die_loc');

  a.mov_from_rip(RCX, 'd_httpBuf');
  a.lea_rip(RDX, 's_key_lat');
  a.call_lab('lookup_key');
  a.test_rr(RAX, RAX);
  a.je('die_loc');
  a.mov_rr(RCX, RAX);
  a.lea_rip(RDX, 'd_lat');
  a.call_lab('extract_value');
  a.test_rr(RAX, RAX);
  a.je('die_loc');

  a.mov_from_rip(RCX, 'd_httpBuf');
  a.lea_rip(RDX, 's_key_lon');
  a.call_lab('lookup_key');
  a.test_rr(RAX, RAX);
  a.je('die_loc');
  a.mov_rr(RCX, RAX);
  a.lea_rip(RDX, 'd_lon');
  a.call_lab('extract_value');
  a.test_rr(RAX, RAX);
  a.je('die_loc');

  // forecast URL
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 's_url_f1');
  a.call_lab('strcpy');
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 'd_lat');
  a.call_lab('append');
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 's_url_f2');
  a.call_lab('append');
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 'd_lon');
  a.call_lab('append');
  a.lea_rip(RCX, 'd_url');
  a.lea_rip(RDX, 's_url_f3');
  a.call_lab('append');
  a.lea_rip(RCX, 'd_url');
  a.call_lab('http_get');
  a.test_rr(RAX, RAX);
  a.je('die_net');

  // current temp from "current":
  a.mov_from_rip(RCX, 'd_httpBuf');
  a.lea_rip(RDX, 's_key_current');
  a.call_lab('lookup_key');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(RCX, RAX);
  a.lea_rip(RDX, 's_key_t2m');
  a.call_lab('find');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(RCX, RAX);
  a.lea_rip(RDX, 's_key_t2m');
  a.mov_rr(R14, RCX);
  a.mov_rr(RCX, RDX);
  a.call_lab('strlen');
  a.add_rr(R14, RAX);
  a.mov_rr(RCX, R14);
  a.call_lab('parse_number');
  a.mov_to_rip(RAX, 'd_current');

  // daily block
  a.mov_from_rip(RCX, 'd_httpBuf');
  a.lea_rip(RDX, 's_key_daily');
  a.call_lab('lookup_key');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(R15, RAX); // daily start

  a.mov_rr(RCX, R15);
  a.lea_rip(RDX, 's_key_time');
  a.call_lab('find');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(R14, RAX);
  a.lea_rip(RCX, 's_key_time');
  a.call_lab('strlen');
  a.dec(RAX);
  a.add_rr(R14, RAX);
  a.mov_rr(RCX, R14);
  a.lea_rip(RDX, 'd_dates');
  a.mov_ri32(R8, 7);
  a.call_lab('parse_date_array');

  a.mov_rr(RCX, R15);
  a.lea_rip(RDX, 's_key_tmax');
  a.call_lab('find');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(R14, RAX);
  a.lea_rip(RCX, 's_key_tmax');
  a.call_lab('strlen');
  a.add_rr(R14, RAX); // now at '['  because key includes no '[' — key is `"temperature_2m_max":`
  // value starts with `[` after the key. extract: after key we are at `[` if no space.
  a.mov_rr(RCX, R14);
  a.call_lab('skip_ws');
  a.lea_rip(RDX, 'd_highs');
  a.mov_ri32(R8, 7);
  a.call_lab('parse_num_array');

  a.mov_rr(RCX, R15);
  a.lea_rip(RDX, 's_key_tmin');
  a.call_lab('find');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(R14, RAX);
  a.lea_rip(RCX, 's_key_tmin');
  a.call_lab('strlen');
  a.add_rr(R14, RAX);
  a.mov_rr(RCX, R14);
  a.call_lab('skip_ws');
  a.lea_rip(RDX, 'd_lows');
  a.mov_ri32(R8, 7);
  a.call_lab('parse_num_array');

  a.mov_rr(RCX, R15);
  a.lea_rip(RDX, 's_key_pop');
  a.call_lab('find');
  a.test_rr(RAX, RAX);
  a.je('die_net');
  a.mov_rr(R14, RAX);
  a.lea_rip(RCX, 's_key_pop');
  a.call_lab('strlen');
  a.add_rr(R14, RAX);
  a.mov_rr(RCX, R14);
  a.call_lab('skip_ws');
  a.lea_rip(RDX, 'd_precips');
  a.mov_ri32(R8, 7);
  a.call_lab('parse_num_array');

  // output
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.lea_rip(RCX, 'd_name');
  a.call_lab('print');
  a.lea_rip(RCX, 's_here');
  a.call_lab('print');
  a.lea_rip(RCX, 'd_zip');
  a.call_lab('print');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.lea_rip(RCX, 's_now');
  a.call_lab('print');
  a.mov_from_rip(RCX, 'd_current');
  a.call_lab('print_i32');
  a.lea_rip(RCX, 's_unit_f');
  a.call_lab('print');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');

  a.xor_r(R12);
  a.label('day_loop');
  a.cmp_ri(R12, 7);
  a.jae('days_done');
  a.lea_rip(RBX, 'd_dates');
  a.mov_rr(RAX, R12);
  a.shl_ri(RAX, 4);
  a.add_rr(RBX, RAX); // date string
  a.mov_rr(RCX, RBX);
  a.call_lab('parse_number');
  a.mov_rr(R13, RAX); // year
  a.mov_rr(RCX, RDX);
  a.cmp8_mi(RCX, null, 0, 0x2D);
  a.jne('day_next');
  a.inc(RCX);
  a.call_lab('parse_number');
  a.mov_rr(R14, RAX); // month
  a.mov_rr(RCX, RDX);
  a.inc(RCX);
  a.call_lab('parse_number');
  a.mov_rr(R8, RAX); // day
  a.mov_rr(RCX, R13);
  a.mov_rr(RDX, R14);
  a.call_lab('weekday');
  a.shl_ri(RAX, 4);
  a.lea_rip(RCX, 'weekdays');
  a.add_rr(RCX, RAX);
  a.call_lab('print');
  a.lea_rip(RCX, 's_space');
  a.call_lab('print');
  a.mov_rr(RCX, RBX);
  a.call_lab('print');
  a.lea_rip(RCX, 's_high');
  a.call_lab('print');
  a.lea_rip(RDX, 'd_highs');
  a.mov_rr(R11, R12);
  a.mov_rm(RCX, RDX, R11, 0, 8);
  a.call_lab('print_i32');
  a.lea_rip(RCX, 's_unit_f');
  a.call_lab('print');
  a.lea_rip(RCX, 's_low');
  a.call_lab('print');
  a.lea_rip(RDX, 'd_lows');
  a.mov_rr(R11, R12);
  a.mov_rm(RCX, RDX, R11, 0, 8);
  a.call_lab('print_i32');
  a.lea_rip(RCX, 's_unit_f');
  a.call_lab('print');
  a.lea_rip(RCX, 's_precip');
  a.call_lab('print');
  a.lea_rip(RDX, 'd_precips');
  a.mov_rr(R11, R12);
  a.mov_rm(RCX, RDX, R11, 0, 8);
  a.call_lab('print_i32');
  a.lea_rip(RCX, 's_pct');
  a.call_lab('print');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.label('day_next');
  a.inc(R12);
  a.jmp('day_loop');

  a.label('days_done');
  a.lea_rip(RCX, 's_crlf');
  a.call_lab('print');
  a.lea_rip(RCX, 's_attr');
  a.call_lab('print');
  a.xor_r(RCX);
  a.jmp('pause_exit');
}

function writeDesc(buf, off, oft, name, ft) {
  const bytes = [...u32(oft), ...u32(0), ...u32(0), ...u32(name), ...u32(ft)];
  for (let i = 0; i < 20; i++) buf[off + i] = bytes[i];
}

function build() {
  const a = new Asm();
  emitProgram(a);
  if (a.labels.entry === undefined) throw new Error('no entry');

  const FILE_ALIGN = 0x200;
  const SECT_ALIGN = 0x1000;
  const textRva = 0x1000;
  const headerSize = 0x200;

  // .rdata layout (size independent of RVAs except we store RVAs inside)
  // We first compute rdata size with a dummy rva, then rebuild... actually we need rdataRva
  // which is 0x1000 + align(code, 0x1000). Code size known.
  const textRaw = align(a.b.length, FILE_ALIGN);
  const rdataRva = textRva + align(a.b.length, SECT_ALIGN);

  function buildRdata(rdataRva, iatK32, iatWin) {
    const b = [];
    const sym = {};
    const emit = (arr) => { for (const x of arr) b.push(x); };
    const pad = (n) => { while (b.length % n) b.push(0); };

    const impOff = 0;
    for (let i = 0; i < 60; i++) b.push(0);

    pad(2);
    sym.str_kernel32 = rdataRva + b.length;
    emit(cstr('kernel32.dll'));
    pad(2);
    sym.str_wininet = rdataRva + b.length;
    emit(cstr('wininet.dll'));

    for (const fn of K32) {
      pad(2);
      sym['hn_' + fn] = rdataRva + b.length;
      emit([0, 0, ...cstr(fn)]);
    }
    for (const fn of WININET) {
      pad(2);
      sym['hn_' + fn] = rdataRva + b.length;
      emit([0, 0, ...cstr(fn)]);
    }

    pad(8);
    sym.ilt_k32 = rdataRva + b.length;
    for (const fn of K32) emit(u64(sym['hn_' + fn]));
    emit(u64(0));
    pad(8);
    sym.ilt_win = rdataRva + b.length;
    for (const fn of WININET) emit(u64(sym['hn_' + fn]));
    emit(u64(0));

    for (const [name, s] of Object.entries(STRINGS)) {
      sym[name] = rdataRva + b.length;
      emit(cstr(s));
    }
    pad(16);
    sym.weekdays = rdataRva + b.length;
    for (const d of DAYS) {
      const slot = Array(16).fill(0);
      for (let i = 0; i < d.length; i++) slot[i] = d.charCodeAt(i);
      emit(slot);
    }

    writeDesc(b, impOff, sym.ilt_k32, sym.str_kernel32, iatK32);
    writeDesc(b, impOff + 20, sym.ilt_win, sym.str_wininet, iatWin);
    return { bytes: b, sym };
  }

  // IAT size
  const iatK32Size = (K32.length + 1) * 8;
  const iatWinSize = (WININET.length + 1) * 8;
  const iatSize = iatK32Size + iatWinSize;

  let fieldSize = 0;
  for (const [, sz] of DATA_FIELDS) fieldSize += sz;
  const dataSize = iatSize + fieldSize;

  // Need rdata size first: build once with dummy IAT rvas then... rdata size doesn't depend on IAT values, only contents of 20-byte desc.
  const dummy = buildRdata(rdataRva, 0, 0);
  const rdataBytes = dummy.bytes;
  const rdataRaw = align(rdataBytes.length, FILE_ALIGN);
  const dataRva = rdataRva + align(rdataBytes.length, SECT_ALIGN);

  const iatK32 = dataRva;
  const iatWin = dataRva + iatK32Size;
  const rdata = buildRdata(rdataRva, iatK32, iatWin);

  const data = [];
  for (const fn of K32) data.push(...u64(rdata.sym['hn_' + fn]));
  data.push(...u64(0));
  for (const fn of WININET) data.push(...u64(rdata.sym['hn_' + fn]));
  data.push(...u64(0));
  const symbols = Object.assign({}, rdata.sym);
  let off = iatSize;
  for (const fn of K32) symbols['iat_' + fn] = iatK32 + K32.indexOf(fn) * 8;
  for (const fn of WININET) symbols['iat_' + fn] = iatWin + WININET.indexOf(fn) * 8;
  for (const [name, sz] of DATA_FIELDS) {
    symbols[name] = dataRva + off;
    for (let i = 0; i < sz; i++) data.push(0);
    off += sz;
  }

  a.resolve(textRva, symbols);

  const dataRaw = align(data.length, FILE_ALIGN);
  const textFile = headerSize;
  const rdataFile = textFile + textRaw;
  const dataFile = rdataFile + rdataRaw;
  const sizeOfImage = dataRva + align(data.length, SECT_ALIGN);

  const pe = [];
  const put = (arr) => { for (const x of arr) pe.push(x); };

  // DOS header + stub (0x80)
  const dos = Array(0x80).fill(0);
  dos[0] = 0x4D; dos[1] = 0x5A; // MZ
  dos[2] = 0x90;
  dos[8] = 0x04; // pages? keep simple
  dos[0x3C] = 0x80; // e_lfanew
  // tiny message
  const msg = 'This program cannot be run in DOS mode.\r\r\n$';
  for (let i = 0; i < msg.length && 0x40 + i < 0x7C; i++) dos[0x40 + i] = msg.charCodeAt(i);
  put(dos);

  // PE signature
  put([0x50, 0x45, 0x00, 0x00]);
  // COFF
  put(u16(0x8664));
  put(u16(3));
  put(u32(0));
  put(u32(0));
  put(u32(0));
  put(u16(0xF0));
  put(u16(0x0022));

  // Optional PE32+
  put(u16(0x20B));
  put([14, 0]); // linker
  put(u32(textRaw));
  put(u32(rdataRaw + dataRaw));
  put(u32(0));
  put(u32(textRva + a.labels.entry));
  put(u32(textRva));
  put(u64(0x140000000));
  put(u32(SECT_ALIGN));
  put(u32(FILE_ALIGN));
  put(u16(6)); put(u16(0));
  put(u16(0)); put(u16(0));
  put(u16(6)); put(u16(0));
  put(u32(0));
  put(u32(sizeOfImage));
  put(u32(headerSize));
  put(u32(0));
  put(u16(3)); // console
  put(u16(0x0160));
  put(u64(0x100000));
  put(u64(0x1000));
  put(u64(0x100000));
  put(u64(0x1000));
  put(u32(0));
  put(u32(16));

  const dirs = Array(16).fill(null).map(() => [0, 0]);
  dirs[1] = [rdataRva, 60]; // import
  dirs[12] = [dataRva, iatSize]; // IAT
  for (const [rva, sz] of dirs) {
    put(u32(rva));
    put(u32(sz));
  }

  function section(name, vsize, va, raw, ptr, ch) {
    const n = Buffer.alloc(8);
    n.write(name);
    put([...n]);
    put(u32(vsize));
    put(u32(va));
    put(u32(raw));
    put(u32(ptr));
    put(u32(0)); put(u32(0));
    put(u16(0)); put(u16(0));
    put(u32(ch));
  }
  section('.text', a.b.length, textRva, textRaw, textFile, 0x60000020);
  section('.rdata', rdata.bytes.length, rdataRva, rdataRaw, rdataFile, 0x40000040);
  section('.data', data.length, dataRva, dataRaw, dataFile, 0xC0000040);

  if (pe.length > headerSize) throw new Error('headers too big ' + pe.length);
  while (pe.length < headerSize) pe.push(0);

  const padRaw = (bytes, raw) => {
    const out = bytes.slice();
    while (out.length < raw) out.push(0);
    return out;
  };
  put(padRaw(a.b, textRaw));
  put(padRaw(rdata.bytes, rdataRaw));
  put(padRaw(data, dataRaw));

  return Buffer.from(pe);
}

function main() {
  const out = path.join(__dirname, '..', 'weather.exe');
  const buf = build();
  fs.writeFileSync(out, buf);
  console.log('Wrote', out);
  console.log('Size', buf.length);
  console.log('App', APP_NAME, APP_VERSION, 'build', APP_BUILD);
  if (buf[0] !== 0x4D || buf[1] !== 0x5A) throw new Error('bad MZ');
}

main();
