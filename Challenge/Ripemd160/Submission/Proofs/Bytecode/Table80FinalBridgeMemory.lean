import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailMemory
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
open EvmSemantics Challenge.EvmProof Table80Tail Paired80WordRound

theorem writeWord_comm (memory : ByteArray) (a b : Nat) (va vb : UInt256)
    (hab : a + 32 ≤ b ∨ b + 32 ≤ a) :
    writeWord (writeWord memory a va) b vb =
      writeWord (writeWord memory b vb) a va := by
  apply ByteArray.ext_getElem
  · simp only [tail_writeWord_size]
    omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases ha : a ≤ i ∧ i < a + 32
    · have hb : ¬ (b ≤ i ∧ i < b + 32) := by omega
      simp only [if_pos ha, if_neg hb]
    · by_cases hb : b ≤ i ∧ i < b + 32
      · simp only [if_pos hb, if_neg ha]
      · simp only [if_neg ha, if_neg hb]

def rawHash (memory : ByteArray) (q : WordLane) : Compression.EvmHashState :=
  ⟨result0 memory q, result1 memory q, result2 memory q,
    result3 memory q, result4 memory q⟩

theorem resultMemory_eq_storeRaw (memory : ByteArray) (q : WordLane) :
    resultMemory memory q = StackMemory.storeHash memory (rawHash memory q) := by
  unfold resultMemory
  rw [writeWord_comm _ 960 928 _ _ (Or.inr (by decide)),
    writeWord_comm _ 960 896 _ _ (Or.inr (by decide)),
    writeWord_comm _ 960 864 _ _ (Or.inr (by decide)),
    writeWord_comm _ 928 896 _ _ (Or.inr (by decide)),
    writeWord_comm _ 928 864 _ _ (Or.inr (by decide)),
    writeWord_comm _ 896 864 _ _ (Or.inr (by decide))]
  rfl

theorem rawHash_eq_combine (memory : ByteArray) (q : WordLane)
    (h : Compression.HashState)
    (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    rawHash memory q = Compression.embedHash (Paired80Compression.combine h q) := by
  have hx := hashAt_resultMemory memory q h hh
  rw [resultMemory_eq_storeRaw, StackMemory.hashAt_storeHash] at hx
  exact hx

theorem resultMemory_eq_storeHash (memory : ByteArray) (q : WordLane)
    (h : Compression.HashState)
    (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    resultMemory memory q = StackMemory.storeHash memory
      (Compression.embedHash (Paired80Compression.combine h q)) := by
  rw [resultMemory_eq_storeRaw, rawHash_eq_combine memory q h hh]

#print axioms writeWord_comm
#print axioms resultMemory_eq_storeHash
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
