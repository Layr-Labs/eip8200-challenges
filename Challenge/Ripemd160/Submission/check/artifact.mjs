import {readFileSync} from 'node:fs';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
const read = name => readFileSync(new URL('../' + name, import.meta.url), 'utf8');
const hex = read('bytecode.hex');
const code = Buffer.from(hex.trim(), 'hex');
const chunks = [...read('Bytes.lean').matchAll(/abbrev submissionByteChunk\d+ : ByteArray := ByteArray.mk #\[([\s\S]*?)\]/g)];
const bytes = chunks.flatMap(m => [...m[1].matchAll(/0x([\da-f]{2})/g)].map(x => parseInt(x[1], 16)));
const instructions = [...read('Proofs/Bytecode/Artifact.lean').matchAll(/private def submissionInstructionsChunk\d+ : List Instr :=\s*\[([\s\S]*?)\]/g)];
const assembled = [];
let count = 0;
for (const chunk of instructions) {
  for (const instruction of chunk[1].matchAll(/op 0x([\da-f]{2})|\.push (\d+) (\d+)/g)) {
    ++count;
    if (instruction[1]) assembled.push(parseInt(instruction[1], 16));
    else {
      const width = Number(instruction[2]);
      const value = BigInt(instruction[3]);
      assembled.push(0x5f + width);
      for (let i = width - 1; i >= 0; --i) assembled.push(Number((value >> BigInt(i * 8)) & 255n));
    }
  }
}
assert.equal(code.length, 5268);
assert.equal(count, 3167);
assert.deepEqual(Buffer.from(bytes), code);
assert.deepEqual(Buffer.from(assembled), code);
const certificates = [...read('Proofs/Bytecode/Artifact.lean').matchAll(/private theorem submissionInstructionsChunk\d+_assemble : assembleBytes submissionInstructionsChunk\d+ = \[([\s\S]*?)\]/g)];
const certifiedBytes = certificates.flatMap(m => [...m[1].matchAll(/0x([\da-f]{2})/g)].map(x => parseInt(x[1], 16)));
assert.deepEqual(Buffer.from(certifiedBytes), code);
assert.equal(code.subarray(4962, 4969).toString('hex'), '5b50611368505b');
console.log('All four artifact representations agree; 5268 bytes, 3167 instructions.');
console.log('Raw SHA-256:', createHash('sha256').update(code).digest('hex'));
console.log('Hex SHA-256:', createHash('sha256').update(hex).digest('hex'));
