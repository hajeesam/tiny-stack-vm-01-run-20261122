// Tiny stack VM for make.fun's ISA v1 (kit generator/subject/ISA.md).
// Faithful port of the reference VM generator/subject/vm.mjs: same check order
// per step (step limit, pc range, unknown opcode, truncated immediate, stack
// under/overflow, then the instruction's own traps), same trap codes, same
// 32-bit wrap semantics. Pre-decodes every byte position once so the hot loop
// is a tight switch; deterministic, no clock or environment is read.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Op ids: 0 HALT,1 PUSH8,2 PUSH32,3 POP,4 DUP,5 SWAP,6 OVER,7 ROT,8 ADD,9 SUB,
// 10 MUL,11 DIV,12 MOD,13 DIVU,14 MODU,15 NEG,16 AND,17 OR,18 XOR,19 NOT,
// 20 SHL,21 SHR,22 SHRU,23 EQ,24 LT,25 LTU,26 JMP,27 JZ,28 JNZ,29 CALL,
// 30 RET,31 LOAD,32 STORE,33 PRINT,34 PUTC,35 IN,36 EXIT
const BYT = new Int8Array(256).fill(-1);
const IL = [0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0];
const PO = [0, 0, 0, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 0, 1, 1, 0, 0, 1, 2, 1, 1, 0, 1];
const PU = [0, 1, 1, 0, 2, 2, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0];
for (const [b, o] of [[0, 0], [1, 1], [2, 2], [3, 3], [4, 4], [5, 5], [6, 6], [7, 7], [0x10, 8], [0x11, 9], [0x12, 10], [0x13, 11], [0x14, 12], [0x15, 13], [0x16, 14], [0x17, 15], [0x18, 16], [0x19, 17], [0x1a, 18], [0x1b, 19], [0x1c, 20], [0x1d, 21], [0x1e, 22], [0x20, 23], [0x21, 24], [0x22, 25], [0x30, 26], [0x31, 27], [0x32, 28], [0x33, 29], [0x34, 30], [0x40, 31], [0x41, 32], [0x50, 33], [0x51, 34], [0x52, 35], [0x53, 36]]) BYT[b] = o;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  // Pre-decode per byte position: op id (-1 unknown), bad (0 ok / 5 bad opcode /
  // 9 truncated immediate), imm (PUSH8 sign-extended, PUSH32, JMP/JZ/JNZ signed,
  // CALL unsigned). A jump into the middle of an instruction re-decodes that
  // byte as an opcode, exactly like the reference VM reading program[pc].
  const op = new Int8Array(n);
  const bad = new Uint8Array(n);
  const imm = new Int32Array(n);
  const il = new Uint8Array(n);
  for (let i = 0; i < n; i++) {
    const o = BYT[p[i]];
    op[i] = o;
    if (o < 0) { bad[i] = 5; continue; }
    const l = IL[o];
    il[i] = l;
    if (i + l >= n) { bad[i] = 9; continue; }
    if (o === 1) imm[i] = (p[i + 1] << 24) >> 24;
    else if (o === 2) imm[i] = p[i + 1] | (p[i + 2] << 8) | (p[i + 3] << 16) | (p[i + 4] << 24);
    else if (o === 26 || o === 27 || o === 28) imm[i] = ((p[i + 1] | (p[i + 2] << 8)) << 16) >> 16;
    else if (o === 29) imm[i] = p[i + 1] | (p[i + 2] << 8);
  }
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const done = (code: number) => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const b = bad[pc];
    if (b) return done(b);
    steps++;
    const o = op[pc];
    if (sp < PO[o]) return done(2);
    if (sp - PO[o] + PU[o] > 256) return done(3);
    const im = imm[pc];
    const nx = pc + 1 + il[pc];
    pc = nx;
    switch (o) {
      case 0: return done(0);
      case 1: case 2: D[sp++] = im; break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 15: D[sp - 1] = -D[sp - 1] | 0; break;
      case 19: D[sp - 1] = ~D[sp - 1]; break;
      case 8: case 9: case 10: case 11: case 12: case 13: case 14:
      case 16: case 17: case 18: case 20: case 21: case 22: case 23: case 24: case 25: {
        const bb = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (o === 8) r = (a + bb) | 0;
        else if (o === 9) r = (a - bb) | 0;
        else if (o === 10) r = Math.imul(a, bb);
        else if (o === 11) { if (bb === 0) return done(4); r = a === -2147483648 && bb === -1 ? a : (a / bb) | 0; }
        else if (o === 12) { if (bb === 0) return done(4); r = bb === -1 ? 0 : (a % bb) | 0; }
        else if (o === 13) { if (bb === 0) return done(4); r = Math.floor((a >>> 0) / (bb >>> 0)) | 0; }
        else if (o === 14) { if (bb === 0) return done(4); r = ((a >>> 0) % (bb >>> 0)) | 0; }
        else if (o === 16) r = a & bb;
        else if (o === 17) r = a | bb;
        else if (o === 18) r = a ^ bb;
        else if (o === 20) r = a << (bb & 31);
        else if (o === 21) r = a >> (bb & 31);
        else if (o === 22) r = (a >>> (bb & 31)) | 0;
        else if (o === 23) r = a === bb ? 1 : 0;
        else if (o === 24) r = a < bb ? 1 : 0;
        else r = (a >>> 0) < (bb >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 26: pc = nx + im; break;
      case 27: { const v = D[--sp]; if (v === 0) pc = nx + im; break; }
      case 28: { const v = D[--sp]; if (v !== 0) pc = nx + im; break; }
      case 29:
        if (csp === 64) return done(7);
        C[csp++] = nx;
        pc = im;
        break;
      case 30:
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 31: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 32: {
        const a = D[sp - 1];
        const v = D[sp - 2];
        if (a < 0 || a >= 256) return done(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 33: {
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 34:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 35: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 36: return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
