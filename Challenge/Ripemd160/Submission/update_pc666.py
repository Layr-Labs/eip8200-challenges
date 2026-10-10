"""Integrate the independently scored PC666 experiment after the PC738 checkpoint.
Run only when the earlier canonical run is finished and its candidate is submitted.
Byte and proof generation are not verification: rerun scorer, serial Lean, Yukon.
"""
from pathlib import Path
import re
import hashlib
import subprocess

ROOT = Path(__file__).resolve().parent
PROOFS = ROOT / 'Proofs/Bytecode'
BASE = 'b9182bbcc8258af8bc5e754e1c71c7c0fa52275e282da7d02049f55fe926e095'


def modify_writer(path, dual):
    source = path.read_text()
    # Only change executable templates and their execution-local write lists.
    # The public rawWrites / writerMemory specifications retain their old order.
    for name in ['template0', 'template1', 'template2', 'writes1', 'writes2']:
        start = source.index('def ' + name + ' ')
        end = source.index('\ndef ', start + 4)
        block = source[start:end]
        if name == 'template0':
            for value in [126, 216]:
                old = f'.push ⟨1, by decide⟩ (UInt256.ofNat {value})'
                assert block.count(old) == 1
                block = block.replace(old, old.replace('⟨1,', '⟨2,'))
        elif name == 'template1':
            needle = '    .push ⟨2, by decide⟩ (UInt256.ofNat 792),\n    .op .MSTORE,'
            assert block.count(needle) == 1
            block = block.replace(needle, needle + '\n    .op (.Dup ⟨15, by decide⟩),\n    .op .PC,\n    .op .MSTORE,')
        elif name == 'template2':
            needle = '    .op (.Dup ⟨13, by decide⟩),\n    .push ⟨2, by decide⟩ (UInt256.ofNat 666),\n    .op .MSTORE,\n'
            assert block.count(needle) == 1
            block = block.replace(needle, '')
        else:
            prefix = 'dualW words' if dual else 'words'
            if name == 'writes1':
                needle = f'    (792, {prefix} 1),'
                assert block.count(needle) == 1
                block = block.replace(needle, needle + f'\n    (666, {prefix} 14),')
            else:
                needle = f'    (666, {prefix} 14),\n'
                assert block.count(needle) == 1
                block = block.replace(needle, '')
        source = source[:start] + block + source[end:]

    start = source.index('theorem run_chunk1_of_small')
    end = source.index('\n#print axioms run_chunk1', start)
    block = source[start:end]
    block = block.replace('(hactive : 34 ≤ s.activeWords.toNat) :',
                          '(hactive : 34 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 646) :')
    block = block.replace('(hactive : 35 ≤ s.activeWords.toNat) :',
                          '(hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 646) :')
    block = block.replace('    [template1,', '    [hpc, add_literals, template1,')
    normalize = '''  have hactivePC : MachineState.activeWordsAfter s.activeWords.toNat 666 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 666 (by decide))
  have hactive540 : MachineState.activeWordsAfter s.activeWords.toNat 540 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 540 (by decide))
  have hactive756 : MachineState.activeWordsAfter s.activeWords.toNat 756 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 756 (by decide))
  norm_num [UInt256.size] at hactivePC hactive540 hactive756
'''
    block = block.replace('  simp (config :=', normalize + '  simp (config :=', 1)
    block = block.replace('  all_goals repeat first', '''  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactivePC, hactiveAt]
  all_goals try (rw [hactivePC])
  all_goals try (rw [hactive540, hactive756]; exact hactiveAt 522 (by decide))
  all_goals repeat first''', 1)
    block = block.replace('hstack hrun (by omega)', 'hstack hrun (by omega) hpc')
    source = source[:start] + block + source[end:]
    # The existing local literal-add lemma is below chunk3; move it before chunk1.
    lemma = '''private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b
'''
    assert source.count(lemma) == 1
    source = source.replace(lemma + '\n', '')
    source = source.replace('def template0', lemma + '\ndef template0', 1)

    # Fixed PC646 follows from writer PC606 and widened chunk0 (40 bytes).
    source = re.sub(r'(have h1 := run_chunk1(?:_of_small)? .*? hrun (?:hactive|ha))\n',
                    r'\1 (by simp only [pc1, pc0, hpc]; decide)\n', source)
    commutations = '''    rw [writeWord_comm _ 666 540 _ _ (by decide),
      writeWord_comm _ 666 756 _ _ (by decide),
      writeWord_comm _ 666 522 _ _ (by decide),
      writeWord_comm _ 666 90 _ _ (by decide),
      writeWord_comm _ 666 72 _ _ (by decide),
      writeWord_comm _ 666 54 _ _ (by decide)]
'''
    definitions = '''    simp only [memory0, memory1, memory2, memory3, memory4, memory5,
      writes0, writes1, writes2, writes3, writes4, writes5,
      writeChain, List.foldl_cons, List.foldl_nil]
'''
    if dual:
        old = '''    simpa only [memory0, memory1, memory2, memory3, memory4, memory5,
      writes0, writes1, writes2, writes3, writes4, writes5,
      writeChain, List.foldl_cons, List.foldl_nil] using h'''
        assert source.count(old) == 2
        source = source.replace(old, definitions.rstrip() + '\n' + commutations + '    exact h')
    else:
        old = '''      = writerMemory s.memory words := by
    rfl'''
        assert source.count(old) == 2
        replacement = '''      = writerMemory s.memory words := by
''' + definitions + '''    simp only [writerMemory, rawWrites, writeChain, List.foldl_cons, List.foldl_nil]
''' + commutations
        # The commutation theorem lives in the packed writer namespace.
        replacement = replacement.replace('writeWord_comm', 'Pair13WriterRaw.writeWord_comm')
        source = source.replace(old, replacement.rstrip())
    return source


def main():
    current = bytes.fromhex((ROOT / 'bytecode.hex').read_text())
    assert hashlib.sha256(current).hexdigest() == BASE, 'Expected immutable PC738 base'
    outputs = {}
    for name, dual in [('Pair13WriterRaw.lean', True), ('PoolRawWriter.lean', False)]:
        path = PROOFS / name
        outputs[path] = modify_writer(path, dual)
    path = PROOFS / 'StaggerRawPaired23Raw.lean'
    source = path.read_text()
    for width, value, new_width in [(3, 954, 2), (1, 20, 2)]:
        old = f'.push ⟨{width}, by decide⟩ (UInt256.ofNat {value})'
        assert source.count(old) == 1
        source = source.replace(old, old.replace(f'⟨{width},', f'⟨{new_width},'))
    outputs[path] = source
    candidate = bytes.fromhex((ROOT / 'pc666-experiment.hex').read_text())
    assert len(candidate) == len(current) == 5248
    assert candidate[666] == candidate[738] == 0x58
    for path, source in outputs.items():
        path.write_text(source)
    (ROOT / 'bytecode.hex').write_text(candidate.hex() + '\n')
    subprocess.run(['python3', '-B', str(ROOT / 'update_candidate.py')], check=True)
    print('Integrated PC666 experiment:', hashlib.sha256(candidate).hexdigest())
    print('Not yet verified; run the direct scorer, serial Lean proof and full Yukon gate.')


if __name__ == '__main__':
    main()
