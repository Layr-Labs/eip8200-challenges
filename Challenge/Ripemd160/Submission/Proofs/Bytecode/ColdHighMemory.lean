import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTablePad StaggerTableSparse PairedScheduleMemory PairStoreGap

theorem lowChain_size (memory : ByteArray) (n : UInt256) :
    (lowChain memory n).size = max memory.size 1112 := by
  simp only [lowChain, writeWord_size, zeroMemory_size]
  omega

theorem lowChain_outside (memory : ByteArray) (n : UInt256) (address : Nat) (ha : 1112≤address) :
    (lowChain memory n)[address]?.getD 0 = memory[address]?.getD 0 := by
  simp only [lowChain, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size, zeroMemory_getD]
  simp only [if_neg (by omega : ¬ (36≤address ∧ address<36+32)),
    if_neg (by omega : ¬ (54≤address ∧ address<54+32)),
    if_neg (by omega : ¬ (522≤address ∧ address<522+32)),
    if_neg (by omega : ¬ (144≤address ∧ address<144+32)),
    if_neg (by omega : ¬ (666≤address ∧ address<666+32)),
    if_neg (by omega : ¬ (162≤address ∧ address<162+32)),
    if_neg (by omega : ¬ address<1112)]

theorem lowChain_read_outside (memory : ByteArray) (n : UInt256) (address : Nat) (ha : 1112≤address) :
    MachineState.readWord (lowChain memory n) address = MachineState.readWord memory address := by
  unfold MachineState.readWord
  congr 2
  apply Memory.readPadded_congr
  intro i hi
  exact lowChain_outside memory n (address+i) (by omega)

theorem lowChain_low_bytes (memory : ByteArray) (n : UInt256) (address : Nat) (ha : address<32) :
    (lowChain memory n)[address]?.getD 0 = 0 := by
  simp only [lowChain, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size, zeroMemory_getD]
  simp only [if_neg (by omega : ¬ (36≤address ∧ address<36+32)),
    if_neg (by omega : ¬ (54≤address ∧ address<54+32)),
    if_neg (by omega : ¬ (522≤address ∧ address<522+32)),
    if_neg (by omega : ¬ (144≤address ∧ address<144+32)),
    if_neg (by omega : ¬ (666≤address ∧ address<666+32)),
    if_neg (by omega : ¬ (162≤address ∧ address<162+32)),
    if_pos (by omega : address<1112)]

theorem lowChain_read0 (memory : ByteArray) (n : UInt256) :
    MachineState.readWord (lowChain memory n) 0 = 0 := by
  have he : MachineState.readPadded (lowChain memory n) 0 32 = MachineState.readPadded ByteArray.empty 0 32 := by
    apply Memory.readPadded_congr
    intro i hi
    simp only [Nat.zero_add, lowChain_low_bytes memory n i hi]
    rfl
  unfold MachineState.readWord
  rw [he, ← Challenge.EvmProof.Bytes.bytesNat_toList, Challenge.EvmProof.Bytes.readPadded_toList]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem lowChain_gapClear (memory : ByteArray) (n : UInt256) (hn : n.toNat<2^64) :
    GapClear (lowChain memory n) := by
  have hv : (lowDirty n).toNat<2^112 := by
    rw [lowDirty, lowDirty_shift n hn]
    simp only [Nat.reducePow] at *
    omega
  have hz (i : Nat) (hi : i<18) := encoded_prefix_zero (lowDirty n) hv i hi
  intro j hj k hk0 hk1
  simp only [lowerPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals interval_cases k
  all_goals simp only [lowChain, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size, zeroMemory_getD]
  all_goals norm_num only
  all_goals first | exact hz _ (by decide) | rfl

#print axioms lowChain_size
#print axioms lowChain_outside
#print axioms lowChain_read0
#print axioms lowChain_gapClear
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighMemory
