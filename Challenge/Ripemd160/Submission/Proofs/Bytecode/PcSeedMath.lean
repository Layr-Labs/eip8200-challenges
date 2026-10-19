import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedCoverage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedMath
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open KnownInputCompactState UnrolledRepeatRaw DirectGuard PcSeedRaw TerminalMulRaw
private theorem eq_one_iff (w r : UInt256) : UInt256.eq w r = 1 ↔ w = r := by
  unfold UInt256.eq
  split
  · rename_i h
    exact ⟨fun _ => Word.word_ext h, fun _ => rfl⟩
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro h0
      exact absurd h0 (by decide : (0 : UInt256) ≠ 1)
    · intro heq
      exact absurd (congrArg UInt256.toNat heq) h

private theorem isZero_eq_one_iff (a : UInt256) : UInt256.isZero a = 1 ↔ a = 0 := by
  unfold UInt256.isZero
  split
  · rename_i h
    exact ⟨fun _ => Word.word_ext h, fun _ => rfl⟩
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro h0
      exact absurd h0 (by decide : (0 : UInt256) ≠ 1)
    · intro hz
      exact absurd (congrArg UInt256.toNat hz) h

private theorem land_eq_one {a b : UInt256} (ha : BooleanWord a) (hb : BooleanWord b) :
    UInt256.land a b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem foldAcc_eq_one_iff (input : ByteArray) (r a : UInt256) (xs : List Nat)
    (ha : BooleanWord a) :
    foldAcc input r a xs = 1 ↔
      a = 1 ∧ ∀ offset ∈ xs, MachineState.readWord input offset = r := by
  induction xs generalizing a with
  | nil =>
    simp [foldAcc]
  | cons offset rest ih =>
    rw [foldAcc, List.foldl_cons, ← foldAcc]
    have hstep := step_boolean input r a offset ha
    rw [ih _ hstep]
    unfold step
    rw [land_eq_one (eq_boolean _ _) ha, eq_one_iff]
    constructor
    · rintro ⟨⟨hw, ha1⟩, hrest⟩
      refine ⟨ha1, ?_⟩
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hw
      · exact hrest o ho
    · rintro ⟨ha1, hall⟩
      refine ⟨⟨hall offset (List.mem_cons.mpr (Or.inl rfl)), ha1⟩, ?_⟩
      intro o ho
      exact hall o (List.mem_cons.mpr (Or.inr ho))

private theorem reference_ne_zero (input : ByteArray) (hcond : Low64RepeatMath.condition input = 0) :
    referenceWord input ≠ 0 := by
  intro hz
  have hshl : UInt256.shiftLeft
      (UInt256.xor (UInt256.ofNat Low64Anchor.low64) (referenceWord input))
      (UInt256.ofNat 192) = 0 := by
    simpa [Low64RepeatMath.condition, referenceWord, Low64Anchor.low64] using hcond
  have hmod := Low64Anchor.low64_of_shl (referenceWord input) hshl
  rw [hz] at hmod
  have hzero : (0 : UInt256).toNat = 0 := by
    rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl, Word.word_toNat_ofNat]
    exact Nat.zero_mod _
  simp [hzero, Low64Anchor.B, Nat.zero_mod] at hmod


private theorem seed_boolean (input : ByteArray) : BooleanWord (seed input) :=
  eq_boolean _ _

theorem mismatch_zero_words (input : ByteArray)
    (hcond : Low64RepeatMath.condition input = 0) (hm : mismatch input = 0) :
    MachineState.readWord input 48 = MachineState.readWord input 0 ∧
      ∀ off ∈ PcSeedRaw.offsets, MachineState.readWord input off = MachineState.readWord input 0 := by
  have hfbool := foldAcc_boolean input (MachineState.readWord input 0) (seed input)
    PcSeedRaw.offsets.dropLast (seed_boolean input)
  have hmprod := (KnownInputLogic.wordXor_eq_zero_iff _ _).1 hm
  change UInt256.mul (MachineState.readWord input 16)
    (foldAcc input (MachineState.readWord input 0) (seed input) PcSeedRaw.offsets.dropLast) =
      MachineState.readWord input 0 at hmprod
  have hf : foldAcc input (MachineState.readWord input 0) (seed input) PcSeedRaw.offsets.dropLast = 1 := by
    rcases hfbool with hf | hf
    · rw [hf, TerminalMulRaw.mul_zero] at hmprod
      exact absurd hmprod.symm (reference_ne_zero input hcond)
    · exact hf
  have hall := (foldAcc_eq_one_iff input (MachineState.readWord input 0)
    (seed input) PcSeedRaw.offsets.dropLast (seed_boolean input)).1 hf
  refine ⟨((eq_one_iff _ _).1 hall.1).symm, ?_⟩
  intro off ho
  have hh : off ∈ PcSeedRaw.offsets.dropLast ∨ off = 16 := by
    change off ∈ [968,944,912,880,848,816,784,752,720,688,656,624,592,560,528,
      496,464,432,400,368,336,304,272,240,208,176,144,112,80] ∨ off = 16
    simpa only [PcSeedRaw.offsets, List.mem_cons, List.not_mem_nil, or_false, or_assoc] using ho
  rcases hh with ho | rfl
  · exact hall.2 off ho
  · simpa only [hf, TerminalMulRaw.mul_one] using hmprod

theorem mismatch_zero_target (input : ByteArray) (hsize : input.size = 1000)
    (hcond : Low64RepeatMath.condition input = 0) (hm : mismatch input = 0) :
    input = KnownInputData.targetInput := by
  have hall := mismatch_zero_words input hcond hm
  have hmain (k : Nat) (hk : k < 30) :
      MachineState.readWord input (16+32*k) = MachineState.readWord input 0 := by
    by_cases h1 : k = 1
    · subst k; exact hall.1
    · apply hall.2
      interval_cases k <;> simp_all [PcSeedRaw.offsets]
  have h968 := hall.2 968 (by decide)
  have hmod := Low64Anchor.low64_of_shl (MachineState.readWord input 0) hcond
  have hb := PcSeedCoverage.all_bytes input hmain h968 hmod
  apply ByteArray.ext_getElem
  · exact hsize.trans KnownInputData.targetInput_size.symm
  · intro j hj hjtarget
    have hh := hb j (by omega)
    have hbyte : YulSemantics.EVM.byteFrom input.toList j = 0x61 := by
      apply UInt8.ext
      have hv := congrArg UInt256.toNat hh
      rw [PcSeedCoverage.byte, Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans
          (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
        Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hv
      exact hv
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList] at hbyte
    rw [Array.getElem?_eq_getElem (by simpa using hj)] at hbyte
    simp only [Option.getD_some] at hbyte
    rw [KnownInputData.targetInput_getElem j hjtarget]
    exact hbyte
theorem target_readWord (off : Nat) (ho : off ≤ 968) :
    MachineState.readWord KnownInputData.targetInput off = KnownInputData.fullWord := by
  have hread : MachineState.readPadded KnownInputData.targetInput off 32 =
      ByteArray.mk (Array.replicate 32 0x61) := by
    apply ByteArray.ext_getElem
    · rw [Memory.readPadded_size]; norm_num [ByteArray.size]
    · intro j hj₁ hj₂
      have hj : j < 32 := by simpa only [Memory.readPadded_size] using hj₁
      have hsource : off+j < KnownInputData.targetInput.size := by
        rw [KnownInputData.targetInput_size]; omega
      rw [← Memory.getD0_eq_getElem _ _ hj₁, Memory.readPadded_getElem?_getD,
        if_pos hj, Memory.getD0_eq_getElem _ _ hsource,
        KnownInputData.targetInput_getElem _ hsource]
      change (0x61 : UInt8) = (Array.replicate 32 0x61)[j]
      rw [Array.getElem_replicate]
  unfold MachineState.readWord
  rw [hread]
  apply Word.word_ext
  have h97 : UInt8.toNat (97 : UInt8) = 97 := by decide
  norm_num [Data.Bytes.bytesToBigEndianNat,
    Bytecode.toList_eq_data, Array.toList_replicate, List.replicate_succ,
    List.foldl, h97, KnownInputData.fullWord, Word.word_toNat_ofNat]

theorem mismatch_target : mismatch KnownInputData.targetInput = 0 := by
  have hseed : seed KnownInputData.targetInput = 1 := by
    unfold seed
    rw [target_readWord 0 (by decide), target_readWord 48 (by decide)]
    decide
  have hfold : foldAcc KnownInputData.targetInput KnownInputData.fullWord 1
      PcSeedRaw.offsets.dropLast = 1 := by
    apply (foldAcc_eq_one_iff _ _ _ _ (Or.inr rfl)).2
    refine ⟨rfl, ?_⟩
    intro off ho
    apply target_readWord
    have hh : ∀ n ∈ PcSeedRaw.offsets.dropLast, n ≤ 968 := by decide
    exact hh off ho
  unfold mismatch
  rw [target_readWord 16 (by decide), target_readWord 0 (by decide), hseed, hfold]
  decide

#print axioms mismatch_target
#print axioms mismatch_zero_words
#print axioms mismatch_zero_target
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedMath
