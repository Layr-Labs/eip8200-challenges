"""Rebind instruction and byte certificates from the submitted raw artifact.
Preserves the inherited instruction chunk partition, PCs outside the rewrite,
and the code/data division. This generator is not a correctness argument.
"""
from pathlib import Path
import re
root = Path(__file__).resolve().parent
b = bytes.fromhex((root / 'bytecode.hex').read_text().strip())
p = root / 'Proofs/Bytecode/Artifact.lean'
s = p.read_text()
counts = [int(n) for n in re.findall(r'submissionInstructionsChunk\d+\.length = (\d+)', s)]
assert len(counts) == 21
pc = 0
instr = []
ends = []
for _ in range(sum(counts)):
    op = b[pc]
    n = op - 95 if 96 <= op <= 127 else 0
    if op == 95: row = '  .push 0 0'
    elif n: row = f'  .push {n} {int.from_bytes(b[pc+1:pc+1+n], "big")}'
    else: row = f'  op 0x{op:02x}'
    instr.append(row)
    pc += 1 + n
    ends.append(pc)
assert pc == 4968 and len(b) == 5248
bs = (root / 'Bytes.lean').read_text()
offset = 0
idx = 0
def literals(values):
    return ',\n'.join('  ' + ', '.join(f'0x{x:02x}' for x in values[i:i+12]) for i in range(0,len(values),12))
for i,n in enumerate(counts):
    rows = ',\n'.join(instr[idx:idx+n]); idx += n
    end = ends[idx-1]
    executable = b[offset:end]
    chunk = b[offset:] if i == 20 else executable
    s = re.sub(rf'(private def submissionInstructionsChunk{i} : List Instr :=\s*\[).*?(\n\])',lambda m:m[1]+'\n'+rows+m[2],s,count=1,flags=re.S)
    s = re.sub(rf'(private theorem submissionInstructionsChunk{i}_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk{i} = \[).*?(\n\] := by decide)',lambda m:m[1]+'\n'+literals(executable)+m[2],s,count=1,flags=re.S)
    bs = re.sub(rf'(abbrev submissionByteChunk{i} : ByteArray := ByteArray.mk #\[).*?(\n\])',lambda m:m[1]+'\n'+literals(chunk)+m[2],bs,count=1,flags=re.S)
    bs = re.sub(rf'(submissionByteChunk{i}\.size = )\d+',rf'\g<1>{len(chunk)}',bs)
    offset = end
p.write_text(s)
(root / 'Bytes.lean').write_text(bs)
# Reflect the normal schedule's exact encoding certificate as well.
p = root / 'Proofs/Bytecode/Pair13NormalTrace.lean'
s = p.read_text()
s = re.sub(r'(theorem exact_bytes : Challenge.EvmProof.PcEncoding.assembleBytes normalTemplate = \[).*?(\] := by decide)',lambda m:m[1]+', '.join(str(x) for x in b[458:808])+m[2],s,count=1,flags=re.S)
p.write_text(s)
