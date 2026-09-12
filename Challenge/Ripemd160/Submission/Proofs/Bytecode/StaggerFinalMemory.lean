import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
import Challenge.EvmProof.Word
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalMemory
open EvmSemantics Challenge.EvmProof Paired80WordRound Paired80Compression StaggerCoreModel
open PairedScheduleMemory

theorem writeWord_comm (memory : ByteArray) (a b : Nat) (va vb : UInt256)
    (hab : a + 32 ≤ b ∨ b + 32 ≤ a) :
    writeWord (writeWord memory a va) b vb =
      writeWord (writeWord memory b vb) a va := by
  apply ByteArray.ext_getElem
  · simp only [PairedScheduleMemory.writeWord_size]
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

theorem tailMemory_eq_storeRaw (memory : ByteArray) (l r : WordLane) :
    tailMemory memory l r = StackMemory.storeHash memory (rawHash memory l r) := by
  dsimp only [tailMemory]
  rw [writeWord_comm _ 832 864 _ _ (Or.inl (by decide)),
    writeWord_comm _ 832 896 _ _ (Or.inl (by decide)),
    writeWord_comm _ 832 928 _ _ (Or.inl (by decide)),
    writeWord_comm _ 832 960 _ _ (Or.inl (by decide))]
  rfl

theorem addResult_normalized (memory : ByteArray) (l r : UInt256) (a : Nat) :
    addResult memory l r a = Word.ofUInt32
      (Word.toUInt32 (MachineState.readWord memory a) + (high32 r + low32 l)) := by
  change Word.mask32 ((l + UInt256.shiftRight r (UInt256.ofNat 80)) +
    MachineState.readWord memory a) = _
  rw [Word.mask32_eq_ofUInt32, Word.toUInt32_add, Word.toUInt32_add]
  apply congrArg Word.ofUInt32
  change (low32 l + high32 r) + _ = _
  rw [UInt32.add_comm (low32 l) (high32 r), UInt32.add_comm]

theorem rawHash_eq_combine (memory : ByteArray) (l r : WordLane)
    (h : Compression.HashState) (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    rawHash memory l r = Compression.embedHash
      (PairedCompressionBridge.combineLanes h (unpackLeft l) (unpackRight r)) := by
  have h0 := congrArg Compression.EvmHashState.h0 hh
  have h1 := congrArg Compression.EvmHashState.h1 hh
  have h2 := congrArg Compression.EvmHashState.h2 hh
  have h3 := congrArg Compression.EvmHashState.h3 hh
  have h4 := congrArg Compression.EvmHashState.h4 hh
  simp only [StackMemory.hashAt, Compression.embedHash] at h0 h1 h2 h3 h4
  simp only [rawHash, addResult_normalized, h0, h1, h2, h3, h4, Word.toUInt32_ofUInt32]
  rfl

theorem resultMemory_eq_folds (memory : ByteArray) (words : Nat → UInt32)
    (h : Compression.HashState) (hh : StackMemory.hashAt memory = Compression.embedHash h)
    (hm : StaggerMessage.Ready memory words) :
    resultMemory memory = StackMemory.storeHash memory (Compression.embedHash
      (PairedCompressionBridge.combineLanes h
        (Paired80Algorithm.leftFold words 80 (StaggerRepresentation.initialCrypto h))
        (Paired80Algorithm.rightFold words 80 (StaggerRepresentation.initialCrypto h)))) := by
  have hp := StaggerCoreCorrect.paired_crypto memory words (StaggerRepresentation.initialCrypto h) hm
  unfold resultMemory
  rw [StaggerRepresentation.initial_eq memory h hh,
    tailMemory_eq_storeRaw, rawHash_eq_combine _ _ _ h hh,
    StaggerCoreCorrect.epilogue_crypto memory words _ hm, hp.1, hp.2,
    StaggerCoreCorrect.leftFinish_fold]

#print axioms tailMemory_eq_storeRaw
#print axioms addResult_normalized
#print axioms rawHash_eq_combine
#print axioms resultMemory_eq_folds
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalMemory
