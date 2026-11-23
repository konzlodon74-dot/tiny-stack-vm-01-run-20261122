// A tiny stack-machine interpreter for make.fun's stack ISA, v1.
// Executes every instance's bytecode in the input directory and
// writes back the bytes it printed plus its exit code.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const SRC = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const DST = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

const STACK_CAP = 256;
const CALL_CAP = 64;
const MEM_WORDS = 256;
const STEP_CAP = 1_000_000;
const OUT_CAP = 65_536;

// Immediate length per opcode byte; most carry none.
const IMM = new Int8Array(256);
IMM[0x01] = 1;
IMM[0x02] = 4;
IMM[0x30] = IMM[0x31] = IMM[0x32] = IMM[0x33] = 2;

// Per-opcode stack traffic (checked before executing) and validity.
const NEED = new Int8Array(256);
const GIVE = new Int8Array(256);
const KNOWN = new Uint8Array(256);
function mark(bytes, pops, pushes) {
  for (const b of bytes) { NEED[b] = pops; GIVE[b] = pushes; KNOWN[b] = 1; }
}
mark([0x00, 0x30, 0x33, 0x34], 0, 0); // HALT, JMP, CALL, RET
mark([0x01, 0x02, 0x52], 0, 1); // PUSH8, PUSH32, IN
mark([0x03, 0x31, 0x32, 0x50, 0x51, 0x53], 1, 0); // POP, JZ, JNZ, PRINT, PUTC, EXIT
mark([0x04], 1, 2);
mark([0x05], 2, 2);
mark([0x06], 2, 3);
mark([0x07], 3, 3);
mark([0x17, 0x1b, 0x40], 1, 1); // NEG, NOT, LOAD
mark([0x41], 2, 0);
for (let b = 0x10; b <= 0x22; b++) { // two-operand operators
  if (b === 0x17 || b === 0x1b || b === 0x1f) continue;
  NEED[b] = 2; GIVE[b] = 1; KNOWN[b] = 1;
}
// Executes one program to its end; a trap's code is its exit code.
function runVm(prog, inp) {
  const len = prog.length;
  const stack = new Int32Array(STACK_CAP);
  const calls = new Int32Array(CALL_CAP);
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_CAP);
  let sp = 0, csp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const finish = (code) => ({ bytes: out.subarray(0, olen), code });
  for (;;) {
    if (steps >= STEP_CAP) return finish(10);
    if (pc < 0 || pc >= len) return finish(9);
    const op = prog[pc];
    if (!KNOWN[op]) return finish(5);
    const imm = IMM[op];
    if (pc + imm >= len) return finish(9);
    steps++;
    if (sp < NEED[op]) return finish(2);
    if (sp - NEED[op] + GIVE[op] > STACK_CAP) return finish(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00: return finish(0); // HALT
      case 0x01: // PUSH8, sign-extended
        stack[sp++] = (prog[nx - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        stack[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break; // DUP
      case 0x05: { // SWAP
        const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t;
        break;
      }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break; // OVER
      case 0x07: { // ROT
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
        break;
      }
      case 0x17: stack[sp - 1] = (-stack[sp - 1]) | 0; break; // NEG
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break; // NOT
      case 0x30: case 0x31: case 0x32: { // jumps: signed offset
        const off = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let go = op === 0x30;
        if (!go) { const v = stack[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
        if (go) pc = nx + off;
        break;
      }
      case 0x33: // CALL
        if (csp >= CALL_CAP) return finish(7);
        calls[csp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return finish(8);
        pc = calls[--csp];
        break;
      case 0x40: { // LOAD
        const a = stack[sp - 1];
        if (a < 0 || a >= MEM_WORDS) return finish(6);
        stack[sp - 1] = mem[a];
        break;
      }
      case 0x41: { // STORE
        const a = stack[sp - 1];
        if (a < 0 || a >= MEM_WORDS) return finish(6);
        mem[a] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT
        const s = String(stack[sp - 1]);
        if (olen + s.length > OUT_CAP) return finish(11);
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51: // PUTC
        if (olen >= OUT_CAP) return finish(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52: stack[sp++] = ipos < inp.length ? inp[ipos++] : -1; break; // IN
      case 0x53: return finish(stack[--sp] & 255); // EXIT, low byte
      default: { // the two-operand operators: b is the top, a below it
        const b = stack[sp - 1], a = stack[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // low 32 bits of the product
          case 0x13: // DIV: truncated toward zero; the overflowing pair wraps
            if (b === 0) return finish(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: // MOD: the remainder takes the sign of a
            if (b === 0) return finish(4);
            r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: // DIVU: operands read as unsigned
            if (b === 0) return finish(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: // MODU
            if (b === 0) return finish(4);
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // low 5 bits of the count only
          case 0x1d: r = a >> (b & 31); break; // arithmetic shift
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical shift
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU
        }
        sp -= 2;
        stack[sp++] = r;
      }
    }
  }
}
for (const id of readdirSync(SRC).sort()) {
  const prog = readFileSync(join(SRC, id, "program.bin"));
  let inp = new Uint8Array(0);
  try { inp = readFileSync(join(SRC, id, "input.bin")); } catch { /* no input file */ }
  const { bytes, code } = runVm(prog, inp);
  mkdirSync(join(DST, id), { recursive: true });
  writeFileSync(join(DST, id, "stdout.bin"), bytes);
  writeFileSync(join(DST, id, "exit.txt"), code + "\n");
}
