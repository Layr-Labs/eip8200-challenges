"""Search gas-neutral PUSH-width redistribution within fixed raw-template blocks.
Hypotheses only: block length and instruction count are preserved, but exact-byte
and universal execution certificates must be rebuilt before submission.
"""
from pathlib import Path
import re
import argparse

ROOT = Path(__file__).resolve().parent


def encode_source(text):
    match = re.search(r'def template : List Instr :=\s*\[(.*?)\]\s*def inputStack', text, re.S)
    if not match:
        return None
    result = bytearray()
    rows = re.findall(r'\.op \(\.(Dup|Swap) ⟨(\d+), by decide⟩\)|\.op \.(\w+)|\.push ⟨(\d+), by decide⟩ \(UInt256.ofNat (\d+)\)', match[1])
    opcodes = {'ADD': 1, 'MUL': 2, 'SUB': 3, 'DIV': 4, 'MULMOD': 9,
               'LT': 0x10, 'GT': 0x11, 'EQ': 0x14, 'ISZERO': 0x15,
               'AND': 0x16, 'OR': 0x17, 'XOR': 0x18, 'NOT': 0x19,
               'SHL': 0x1b, 'SHR': 0x1c, 'SAR': 0x1d, 'POP': 0x50,
               'MLOAD': 0x51, 'MSTORE': 0x52, 'PC': 0x58}
    for kind, index, op, width, value in rows:
        if kind:
            result.append((0x80 if kind == 'Dup' else 0x90) + int(index))
        elif width:
            w, v = int(width), int(value)
            result.append(0x5f + w)
            result.extend(v.to_bytes(w, 'big'))
        elif op in opcodes:
            result.append(opcodes[op])
        else:
            return None
    return bytes(result)


def instructions(data, begin, end):
    result = []
    pc = begin
    while pc < end:
        op = data[pc]
        width = op - 0x5f if 0x5f <= op <= 0x7f else None
        value = int.from_bytes(data[pc + 1:pc + 1 + width], 'big') if width is not None else None
        result.append((pc, width, value))
        pc += 1 + (width or 0)
    assert pc == end
    return result


def literal_cost(data):
    return len(data) + 8 * ((len(data) + 63) // 64) + sum(
        len(set(data[i:i + 64])) for i in range(0, len(data), 64))


def rewrite(data, edits):
    result = bytearray(data)
    for pc, width, value, new_width in sorted(edits, reverse=True):
        assert result[pc] == 0x5f + width
        assert int.from_bytes(result[pc + 1:pc + 1 + width], 'big') == value
        result[pc:pc + 1 + width] = bytes([0x5f + new_width]) + value.to_bytes(new_width, 'big')
    assert len(result) == len(data)
    return bytes(result)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--hex', default=str(ROOT / 'bytecode.hex'))
    args = parser.parse_args()
    data = bytes.fromhex(Path(args.hex).read_text())
    proposals = []
    for path in sorted((ROOT / 'Proofs/Bytecode').glob('Stagger*Raw.lean')):
        encoded = encode_source(path.read_text())
        if not encoded:
            continue
        begin = data.find(encoded)
        if begin < 0 or data.find(encoded, begin + 1) >= 0:
            continue
        end = begin + len(encoded)
        instrs = instructions(data, begin, end)
        chunks = range(begin // 64, (end - 1) // 64 + 1)
        old_cost = sum(len(set(data[i * 64:(i + 1) * 64])) for i in chunks)
        best = None
        for p, w, v in instrs:
            minimum = max(1, (v.bit_length() + 7) // 8) if w is not None else 33
            if w is None or w <= minimum:
                continue
            for q, width, value in instrs:
                if p == q or width is None or width == 0 or width == 32:
                    continue
                edits = [(p, w, v, w - 1), (q, width, value, width + 1)]
                candidate = rewrite(data, edits)
                new_cost = sum(len(set(candidate[i * 64:(i + 1) * 64])) for i in chunks)
                if new_cost < old_cost and (best is None or old_cost - new_cost > best[0]):
                    best = (old_cost - new_cost, path.name, begin, end, edits)
        if best:
            proposals.append(best)
    print('Base literal cost:', literal_cost(data))
    print('Best independent gas-neutral pair per uniquely located raw block:')
    for proposal in sorted(proposals, reverse=True):
        print(proposal)
    print('These reductions are not necessarily additive across shared chunks.')


if __name__ == '__main__':
    main()
