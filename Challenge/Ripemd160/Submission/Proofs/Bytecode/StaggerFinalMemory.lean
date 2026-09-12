import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
import Challenge.EvmProof.Word
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalMemory
open EvmSemantics Challenge.EvmProof Paired144WordRound StaggerCoreModel
open Paired80Compression (low32 unpackLeft)
open PairedScheduleMemory

def high32 (x : UInt256) : UInt32 := low32 (UInt256.shiftRight x (UInt256.ofNat 144))
def unpackRight (q : WordLane) : CryptoLane :=
  ⟨high32 q.a, high32 q.b, high32 q.c, high32 q.d, high32 q.e⟩

theorem high32_packWord (a b : UInt32) :
    high32 (PairedLaneUInt256Bridge.word (Paired144Core.pack a.toBitVec b.toBitVec)) = b := by
  apply UInt32.eq_of_toBitVec_eq
  change (PairedLaneUInt256Bridge.bits
    (UInt256.shiftRight (PairedLaneUInt256Bridge.word
      (Paired144Core.pack a.toBitVec b.toBitVec)) (UInt256.ofNat 144))).setWidth 32 = _
  rw [PairedLaneUInt256Bridge.bits_shr _ 144 (by decide),
    PairedLaneUInt256Bridge.bits_word, BitVec.setWidth_ushiftRight_eq_extractLsb]
  exact Paired144Core.high_pack a.toBitVec b.toBitVec

theorem unpackRight_packCrypto (l r : CryptoLane) : unpackRight (packCrypto l r) = r := by
  cases l; cases r
  simp only [unpackRight, packCrypto, high32_packWord]

theorem high32_pairMask (x : UInt256) :
    high32 (UInt256.land x Paired144WordRound.pairWord) = high32 x := by
  apply UInt32.eq_of_toBitVec_eq
  change (PairedLaneUInt256Bridge.bits (UInt256.shiftRight (UInt256.land x _)
    (UInt256.ofNat 144))).setWidth 32 =
      (PairedLaneUInt256Bridge.bits (UInt256.shiftRight x (UInt256.ofNat 144))).setWidth 32
  rw [PairedLaneUInt256Bridge.bits_shr _ 144 (by decide),
    PairedLaneUInt256Bridge.bits_shr _ 144 (by decide),
    BitVec.setWidth_ushiftRight_eq_extractLsb,BitVec.setWidth_ushiftRight_eq_extractLsb,
    PairedLaneUInt256Bridge.bits_land,Paired144WordRound.pairWord,
    PairedLaneUInt256Bridge.bits_word,←Paired144Core.normalize_eq_and]
  exact Paired144Core.high_pack _ _

theorem unpackRight_dirtyDE (l r : CryptoLane) (dd de : UInt256)
    (hd : UInt256.land dd Paired144WordRound.pairWord = (packCrypto l r).d)
    (he : UInt256.land de Paired144WordRound.pairWord = (packCrypto l r).e) :
    unpackRight {packCrypto l r with d:=dd, e:=de} = r := by
  have hhighd : high32 dd = high32 (packCrypto l r).d :=
    (high32_pairMask dd).symm.trans (congrArg high32 hd)
  have hhighe : high32 de = high32 (packCrypto l r).e :=
    (high32_pairMask de).symm.trans (congrArg high32 he)
  change (⟨high32 (packCrypto l r).a, high32 (packCrypto l r).b, high32 (packCrypto l r).c,
    high32 dd, high32 de⟩ : CryptoLane) = r
  rw [hhighd, hhighe]
  exact unpackRight_packCrypto l r

#print axioms unpackRight_dirtyDE

#print axioms high32_packWord
#print axioms unpackRight_packCrypto

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
  change Word.mask32 ((l + UInt256.shiftRight r (UInt256.ofNat 144)) +
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
  obtain ⟨dd,de,hp,hd,he⟩ := StaggerCoreCorrect.paired_crypto memory words
    (StaggerRepresentation.initialCrypto h) hm
  unfold resultMemory
  rw [StaggerRepresentation.initial_eq memory h hh,hp,
    tailMemory_eq_storeRaw,rawHash_eq_combine _ _ _ h hh,
    StaggerCoreCorrect.epilogue_dirtyDE memory words _ _ hm dd de hd he,
    unpackRight_dirtyDE _ _ dd de hd he,StaggerCoreCorrect.leftFinish_fold]

#print axioms tailMemory_eq_storeRaw
#print axioms addResult_normalized
#print axioms rawHash_eq_combine
#print axioms resultMemory_eq_folds
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalMemory
