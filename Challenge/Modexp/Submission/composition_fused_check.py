"""Cheap exact-byte component check; not a Lean proof or official scorer.
Composition credit: PR533 fused-window on PR536 leading-bit/word-unroll.
Run from this isolated worktree root with python3; no third-party dependencies.
"""
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess

ROOT = Path(__file__).resolve().parent
BASE = '2ae3ad32a3da0512846461c47f70408679688a9a'
DONOR = '7d31b5f1254c37e2da591460c9727007594bd9fe'
REL = 'Challenge/Modexp/Submission/'
SQUARES = [3215, 3255, 3300, 3340, 3385, 3425, 3470, 3510]
TABLES = [3053, 3063, 3073, 3083, 3093, 3103, 3114, 3125, 3136, 3147, 3158, 3169, 3180]
OLD_SQUARE = bytes.fromhex('858580099450' * 4)
NEW_SQUARE = bytes.fromhex('85858009' + '86908009' * 3 + '9450' + '5b' * 6)
OLD_TABLE = bytes.fromhex('828282099050')
NEW_TABLE = bytes.fromhex('818391095b5b')

def at(ref, name):
    return subprocess.check_output(['git', 'show', ref + ':' + REL + name], text=True)

def run(code, stack):
    s = stack.copy()
    gas = 0
    for op in code:
        if 0x80 <= op <= 0x8f:
            s.insert(0, s[op - 0x80]); gas += 3
        elif 0x90 <= op <= 0x9f:
            k = op - 0x8f
            s[0], s[k] = s[k], s[0]; gas += 3
        elif op == 0x09:
            a, b, m = s[:3]
            s[:3] = [(a * b) % m if m else 0]; gas += 8
        elif op == 0x50:
            s.pop(0); gas += 2
        elif op == 0x5b:
            gas += 1
        else:
            raise AssertionError(hex(op))
    return s, gas

def check():
    base = bytes.fromhex(at(BASE, 'bytecode.hex'))
    donor = bytes.fromhex(at(DONOR, 'bytecode.hex'))
    candidate = bytes.fromhex((ROOT / 'bytecode.hex').read_text())
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() == BASE
    expected = bytearray(base)
    for pcs, old, new in [(SQUARES, OLD_SQUARE, NEW_SQUARE), (TABLES, OLD_TABLE, NEW_TABLE)]:
        for pc in pcs:
            assert base[pc:pc + len(old)] == old
            assert donor[pc:pc + len(new)] == new
            expected[pc:pc + len(new)] = new
    assert candidate == expected, 'missing selective fused-window composition (or unrelated byte change)'
    assert len(candidate) == len(base) == 3892
    rng = random.Random(533536)
    checks = 0
    for _ in range(256):
        words = [rng.getrandbits(256) for _ in range(12)]
        for modulus in [0, 1, 2, (1 << 256) - 1, rng.getrandbits(256)]:
            # nibbleState: [nibble, byte, word, pointer, accumulator, modulus] ++ rest
            square_stack = [rng.randrange(16), *words[:4], modulus, *words[4:]]
            for pc in SQUARES:
                old_result, old_gas = run(base[pc:pc + 24], square_stack)
                result, gas = run(candidate[pc:pc + 24], square_stack)
                assert result == old_result
                assert result[4] == (pow(square_stack[4], 16, modulus) if modulus else 0)
                assert old_gas - gas == 9
                checks += 1
            # table update: [previous power, base, modulus] ++ rest
            table_stack = [words[0], words[1], modulus, *words[2:]]
            for pc in TABLES:
                old_result, old_gas = run(base[pc:pc + 6], table_stack)
                result, gas = run(candidate[pc:pc + 6], table_stack)
                assert result == old_result
                assert result[0] == (words[0] * words[1] % modulus if modulus else 0)
                assert old_gas - gas == 3
                checks += 1
    chunks = re.findall(r'private abbrev submissionChunk(\d+) : ByteArray := ByteArray.mk #\[(.*?)\]', (ROOT / 'Bytes.lean').read_text(), re.S)
    assert [int(i) for i, _ in chunks] == list(range(len(chunks)))
    rebuilt = b''.join(bytes(int(x, 16) for x in re.findall(r'0x([0-9a-fA-F]{2})', body)) for _, body in chunks)
    assert rebuilt == candidate, 'Bytes.lean binding mismatch'
    artifact = (ROOT / 'Proofs/Bytecode/Artifact.lean').read_text()
    instructions = artifact.split('def submissionInstructions : List Instr :=\n[', 1)[1].split('\n\ntheorem submissionInstructions_count', 1)[0]
    ops = dict(ADD=0x01, MUL=0x02, SUB=0x03, MOD=0x06, ADDMOD=0x08, MULMOD=0x09, LT=0x10, GT=0x11, EQ=0x14, ISZERO=0x15, AND=0x16, OR=0x17, XOR=0x18, NOT=0x19, BYTE=0x1a, SHL=0x1b, SHR=0x1c, CALLDATALOAD=0x35, CALLDATASIZE=0x36, CALLDATACOPY=0x37, POP=0x50, MLOAD=0x51, MSTORE=0x52, MSTORE8=0x53, JUMP=0x56, JUMPI=0x57, JUMPDEST=0x5b, MCOPY=0x5e, RETURN=0xf3, INVALID=0xfe)
    assembled = bytearray()
    count = 0
    for line in instructions.splitlines():
        if not line.strip():
            continue
        push = re.search(r'Instr.push (\d+) (\d+)', line)
        indexed = re.search(r'Operation.(Dup|Swap) \{ idx := (\d+) \}', line)
        plain = re.search(r'Instr.op EvmSemantics.Operation.(\w+)', line)
        if push:
            width, value = map(int, push.groups())
            assembled.append(0x5f + width)
            assembled.extend(value.to_bytes(width, 'big'))
        elif indexed:
            name, index = indexed.groups()
            assembled.append((0x80 if name == 'Dup' else 0x90) + int(index))
        elif plain:
            assembled.append(ops[plain[1]])
        else:
            raise AssertionError(line)
        count += 1
    assert bytes(assembled) == candidate, 'Artifact instruction binding mismatch'
    declaration = re.search(r'submissionInstructions.length = (\d+)', artifact)
    assert declaration is not None
    declared = int(declaration[1])
    assert count == declared
    for name in ['WindowNibbleDefs.lean', 'WindowNibbleSquare.lean', 'WindowHitPaths.lean']:
        assert (ROOT / 'Proofs/Bytecode' / name).read_text() == at(DONOR, 'Proofs/Bytecode/' + name)
    # Every unchanged proof, including the leading-bit and word-unroll modules,
    # stays at the incumbent. Import resolution is checked for all local modules.
    missing = []
    for file in ROOT.rglob('*.lean'):
        for module in re.findall(r'^import (Challenge\.[\w.]+)', file.read_text(), re.M):
            if not Path(module.replace('.', '/') + '.lean').is_file():
                missing.append(module)
    # Benchmark.Artifact is generated by the protected hosted benchmark.
    # It is absent on a fresh exact-base worktree, not a candidate-local module.
    assert set(missing) <= {'Challenge.Modexp.Benchmark.Artifact'}, missing
    if missing:
        assert 'atomic_write(artifact_module, render_artifact(track, artifact))' in Path('scripts/yukon_benchmark.py').read_text()
    print(json.dumps(dict(base=BASE, donor=DONOR, bytecode_sha256=hashlib.sha256(candidate).hexdigest(), byte_length=len(candidate), instruction_count=count, component_checks=checks, square_pcs=SQUARES, table_pcs=TABLES, gas_saved_per_nibble=9, gas_saved_per_table_update=3, proof_compiled=False, official_score=None), indent=2))

if __name__ == '__main__':
    check()
