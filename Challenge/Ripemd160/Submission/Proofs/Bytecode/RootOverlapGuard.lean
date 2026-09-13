import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RootOverlapGuard
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open KnownInputCompactState

def finalAcc (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (MachineState.readWord input 968) (referenceWord input))
    (loopAcc input 30)

theorem fullOverlap_implies_tail (input : ByteArray)
    (h : MachineState.readWord input 968 = KnownInputData.fullWord) :
    UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192) =
      UInt256.shiftRight KnownInputData.fullWord (UInt256.ofNat 192) := by
  have hh := congrArg UInt256.toNat h
  rw [Bytes.readWord_toNat] at hh
  have hs : Precompile.bytesToNatPadded input 968 32 =
      Precompile.bytesToNatPadded input 968 24 * 256 ^ 8 +
      Precompile.bytesToNatPadded input 992 8 :=
    Bytes.bytesToNatPadded_add input 968 24 8
  rw [hs] at hh
  have hmod := congrArg (fun x : Nat => x % (256 ^ 8)) hh
  have hsmall := Bytes.bytesToNatPadded_lt_pow input 992 8
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
    Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hsmall] at hmod
  have hc : KnownInputData.fullWord.toNat % (256 ^ 8) = 7016996765293437281 := by decide
  rw [hc] at hmod
  have hs' : UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192) =
      UInt256.ofNat (Precompile.bytesToNatPadded input 992 8) :=
    Bytes.shiftRight_readWord input 992 8 (by omega) (by omega)
  rw [hs', hmod]
  decide

#print axioms fullOverlap_implies_tail

theorem target_overlap :
    MachineState.readWord KnownInputData.targetInput 968 = KnownInputData.fullWord := by
  have hread : MachineState.readPadded KnownInputData.targetInput 968 32 =
      ByteArray.mk (Array.replicate 32 0x61) := by
    apply ByteArray.ext_getElem
    · rw [Memory.readPadded_size]
      norm_num [ByteArray.size]
    · intro j hj₁ hj₂
      have hj : j < 32 := by
        rw [Memory.readPadded_size] at hj₁
        exact hj₁
      have hsource : 968 + j < KnownInputData.targetInput.size := by
        rw [KnownInputData.targetInput_size]
        omega
      rw [← Memory.getD0_eq_getElem _ _ hj₁,
        Memory.readPadded_getElem?_getD]
      rw [if_pos hj, Memory.getD0_eq_getElem _ _ hsource,
        KnownInputData.targetInput_getElem _ hsource]
      change (0x61 : UInt8) = (Array.replicate 32 0x61)[j]
      rw [Array.getElem_replicate]
  unfold MachineState.readWord
  rw [hread]
  apply Word.word_ext
  have h97 : UInt8.toNat (97 : UInt8) = 97 := by decide
  norm_num [Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, Array.toList_replicate,
    List.replicate_succ, List.foldl, h97, KnownInputData.fullWord,
    Word.word_toNat_ofNat]

#print axioms target_overlap

theorem finalAcc_zero_iff_target (input : ByteArray) (hsize : input.size = 1000) :
    finalAcc input = 0 ↔ input = KnownInputData.targetInput := by
  constructor
  · intro h
    rcases (KnownInputLogic.wordOr_eq_zero_iff _ _).1 h with ⟨hover, hloop⟩
    have heq := (KnownInputLogic.wordXor_eq_zero_iff _ _).1 hover
    have href := ((KnownInputCompactLogic.loopAcc_zero_iff input 30).1 hloop).1
    have ht := fullOverlap_implies_tail input (heq.trans href)
    apply (KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1
    apply (KnownInputLogic.wordOr_eq_zero_iff _ _).2
    refine ⟨?_, hloop⟩
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).2
    rw [href]
    exact ht
  · intro h
    subst input
    have hold := (KnownInputCompactLogic.finalAcc_zero_iff_target
      KnownInputData.targetInput hsize).2 rfl
    have hloop := ((KnownInputLogic.wordOr_eq_zero_iff _ _).1 hold).2
    have href := ((KnownInputCompactLogic.loopAcc_zero_iff _ 30).1 hloop).1
    apply (KnownInputLogic.wordOr_eq_zero_iff _ _).2
    refine ⟨?_, hloop⟩
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).2
    rw [href]
    exact target_overlap

theorem finalAcc_zero_iff_old (input : ByteArray) (hsize : input.size = 1000) :
    finalAcc input = 0 ↔ KnownInputCompactState.finalAcc input = 0 := by
  rw [finalAcc_zero_iff_target input hsize,
    KnownInputCompactLogic.finalAcc_zero_iff_target input hsize]

#print axioms finalAcc_zero_iff_target
#print axioms finalAcc_zero_iff_old
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RootOverlapGuard
