import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedSizeFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseSerializeReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace StackRoundTemplate

private def shortTemplate : List Instr := [
 .op .JUMPDEST, .push 0 0, .push 32 28948022349768971278010700369584604374341282260324016856826403983149888438272,
 .op .CALLDATASIZE, .op .SHL, .op .SLT,
 .push 2 8191, .op .CALLDATASIZE, .push 7 34711266746334640,
 .op .DIV, .op .AND, .op .JUMPI]
private def longTemplate (n target : Nat) : List Instr := [
 .op .CALLDATASIZE, .push 2 (UInt256.ofNat n), .op .EQ,
 .push 2 (UInt256.ofNat target), .op .JUMPI]
private theorem short_slice : (Artifact.submissionArtifact.instructions.drop 3388).take shortTemplate.length = shortTemplate := by rfl
private theorem long256_slice : (Artifact.submissionArtifact.instructions.drop 3421).take (longTemplate 256 7805).length = longTemplate 256 7805 := by rfl
private theorem long376_slice : (Artifact.submissionArtifact.instructions.drop 3426).take (longTemplate 376 6883).length = longTemplate 376 6883 := by rfl
private theorem code_bound : Artifact.submissionArtifact.code.size < 2^256 := by
 change submissionBytecode.size < 2^256
 rw [referenceBytecode_size]
 decide
private def shortSite : GenericRoundSite Artifact.submissionArtifact .Osaka shortTemplate :=
 StackSiteBuilder.ofSlice shortTemplate 3388 short_slice
  (by change 3388 + shortTemplate.length ≤ Artifact.submissionInstructions.length; rw [Artifact.referenceInstructions_count]; decide)
  code_bound (StackRoundData.templateWellFormed_mem (instructions := shortTemplate) (by decide)) (by decide)
private def long256Site : GenericRoundSite Artifact.submissionArtifact .Osaka (longTemplate 256 7805) :=
 StackSiteBuilder.ofSlice (longTemplate 256 7805) 3421 long256_slice
  (by change 3421 + (longTemplate 256 7805).length ≤ Artifact.submissionInstructions.length; rw [Artifact.referenceInstructions_count]; decide)
  code_bound (StackRoundData.templateWellFormed_mem (instructions := longTemplate 256 7805) (by decide)) (by decide)
private def long376Site : GenericRoundSite Artifact.submissionArtifact .Osaka (longTemplate 376 6883) :=
 StackSiteBuilder.ofSlice (longTemplate 376 6883) 3426 long376_slice
  (by change 3426 + (longTemplate 376 6883).length ≤ Artifact.submissionInstructions.length; rw [Artifact.referenceInstructions_count]; decide)
  code_bound (StackRoundData.templateWellFormed_mem (instructions := longTemplate 376 6883) (by decide)) (by decide)
private theorem short_pc : shortSite.startPC = UInt256.ofNat 4565 := by
 change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3388) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem long256_pc : long256Site.startPC = UInt256.ofNat 4685 := by
 change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3421) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem long376_pc : long376Site.startPC = UInt256.ofNat 4694 := by
 change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3426) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def sizeBit (input : ByteArray) : UInt256 :=
 UInt256.slt (UInt256.shiftLeft SignedSizeFlag.reversedMask (UInt256.ofNat input.size)) 0
private def source (input : ByteArray) : UInt256 := DirectDigestRaw.selected 8191 input.size
private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
 unfold sizeBit
 rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl, SignedSizeFlag.flag]
 have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
 rw [SizeLookupFlag.mask_literal] at h
 simpa only [sizeFlag,Word.literal_eq_ofNat] using h
private theorem hdiv (a b : UInt256) : a / b = UInt256.div a b := rfl
private theorem short_raw (input : ByteArray) :
 runInstrSeq shortTemplate (PatternedScan.stS input 4565 []) =
  if UInt256.isTrue (sizeBit input) then
   if Decode.isValidJumpDest submissionBytecode (source input).toNat then
    some (PatternedScan.patternedEntry input) else none
  else some (PatternedScan.stS input 4618 []) := by
 simp (config := {maxSteps := 400000}) [shortTemplate,runInstrSeq,DataStepper.runInstr,
  sizeBit,source,DirectDigestRaw.selected,PatternedScan.stS,PatternedScan.patternedEntry,PatternedScan.entryRho,
  initialState,Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat,hdiv,
  RawExpressionAC.land_comm]
 split_ifs <;> simp_all
private theorem long_raw (input : ByteArray) (n target pc : Nat) :
 runInstrSeq (longTemplate n target) (PatternedScan.stS input pc []) =
  if UInt256.isTrue (UInt256.eq (UInt256.ofNat n) (UInt256.ofNat input.size)) then
   if Decode.isValidJumpDest submissionBytecode (UInt256.ofNat target).toNat then
    some (PatternedScan.stS input target []) else none
  else some (PatternedScan.stS input (pc+9) []) := by
 simp (config := {maxSteps := 400000}) [longTemplate,runInstrSeq,DataStepper.runInstr,
  PatternedScan.stS,initialState,Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat, Nat.add_assoc]
 split_ifs <;> simp_all

private def soundShort (input : ByteArray) (t : State) (hr : runInstrSeq shortTemplate (PatternedScan.stS input 4565 []) = some t) :
 GasSteps (PatternedScan.stS input 4565 []) t :=
 RecognitionLift.gasSteps_of_raw shortSite _ _ rfl rfl rfl deployAddress_not_precompile short_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
private def sound256 (input : ByteArray) (t : State) (hr : runInstrSeq (longTemplate 256 7805) (PatternedScan.stS input 4685 []) = some t) :
 GasSteps (PatternedScan.stS input 4685 []) t :=
 RecognitionLift.gasSteps_of_raw long256Site _ _ rfl rfl rfl deployAddress_not_precompile long256_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
private def sound376 (input : ByteArray) (t : State) (hr : runInstrSeq (longTemplate 376 6883) (PatternedScan.stS input 4694 []) = some t) :
 GasSteps (PatternedScan.stS input 4694 []) t :=
 RecognitionLift.gasSteps_of_raw long376Site _ _ rfl rfl rfl deployAddress_not_precompile long376_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
private theorem selected_valid (input : ByteArray) (hn : RecognitionAccumulator.Allowed input.size)
  (hne : input.size ≠ 1000) :
 Decode.isValidJumpDest submissionBytecode (source input).toNat = true := by
 obtain ⟨i,hi⟩ := ReverseLiteralScan.allowed_index input.size hn hne
 change Decode.isValidJumpDest submissionBytecode (DirectDigestRaw.selected 8191 input.size).toNat = true
 rw [← hi]
 exact ReverseSerializeReturn.storeSite.valid i
private theorem short_false (input : ByteArray) (hfit : CalldataFits input)
 (hn : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) :
 ¬ UInt256.isTrue (sizeBit input) := by
 have h : UInt256.isZero (sizeBit input) = UInt256.ofNat 1 := (sizeBit_flag input).trans (sizeFlag_fail input hfit hn)
 intro ht
 change (sizeBit input).toNat ≠ 0 at ht
 rw [UInt256.isZero,if_neg ht] at h
 exact (by decide : UInt256.ofNat 0 ≠ UInt256.ofNat 1) h
private theorem long_false (input : ByteArray) (hfit : CalldataFits input) (n : Nat) (hn : n < 2^256) (hs : input.size ≠ n) :
 ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat n) (UInt256.ofNat input.size)) := by
 rw [DirectGuard.size_eq_zero input n (Nat.lt_trans hfit (by norm_num)) hn hs]
 decide

def gasSteps_allowed (input : ByteArray) (hfit : CalldataFits input) (hn : RecognitionAccumulator.Allowed input.size) (_h1000 : input.size ≠ 1000) :
 GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) := by
 by_cases hs : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32
 · have hc : UInt256.isTrue (sizeBit input) := by
    have h := (sizeBit_flag input).trans (sizeFlag_hit input hs)
    change (sizeBit input).toNat ≠ 0
    intro hz
    rw [UInt256.isZero,if_pos hz] at h
    exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) h
   exact soundShort input _ (by rw [short_raw,if_pos hc,if_pos (selected_valid input hn _h1000)])
 · have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by tauto
   have gs := soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)])
   have hl : input.size = 256 ∨ input.size = 376 := by unfold RecognitionAccumulator.Allowed at hn; omega
   have hw : AbcArm.wordCond input ≠ 0 := by
    intro hw
    have hsmall := AbcArm.size_lt_four_of_wordCond input hfit hw
    omega
   have g0 := gs.trans (AbcArm.gasSteps_miss input hw)
   by_cases h : input.size = 256
   · have hv : Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 7805).toNat = true := by
      have hp : source input = UInt256.ofNat 7805 := by
       unfold source
       rw [h]
       decide
      simpa only [hp] using selected_valid input hn _h1000
     have gj := sound256 input (PatternedScan.stS input 7805 []) (by rw [long_raw,DirectGuard.size_eq_one input 256 h]; simp only [show UInt256.isTrue (UInt256.ofNat 1) from by decide,if_true,hv])
     have he : PatternedScan.stS input 7805 [] = PatternedScan.patternedEntry input := by
      simp [PatternedScan.stS,PatternedScan.patternedEntry,PatternedScan.entryRho,h]; decide
     exact g0.trans (GasSteps.cast gj rfl he)
   · have h256 : input.size ≠ 256 := h
     have h : input.size = 376 := by omega
     have g1 := sound256 input _ (by rw [long_raw,if_neg (long_false input hfit 256 (by decide) h256)])
     have hv : Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 6883).toNat = true := by
      have hp : source input = UInt256.ofNat 6883 := by
       unfold source
       rw [h]
       decide
      simpa only [hp] using selected_valid input hn _h1000
     have gj := sound376 input (PatternedScan.stS input 6883 []) (by rw [long_raw,DirectGuard.size_eq_one input 376 h]; simp only [show UInt256.isTrue (UInt256.ofNat 1) from by decide,if_true,hv])
     have he : PatternedScan.stS input 6883 [] = PatternedScan.patternedEntry input := by
      simp [PatternedScan.stS,PatternedScan.patternedEntry,PatternedScan.entryRho,h]; decide
     exact g0.trans (g1.trans (GasSteps.cast gj rfl he))

def gasSteps_to_arm (input : ByteArray) (hfit : CalldataFits input) (hn : ¬ RecognitionAccumulator.Allowed input.size) (_h1000 : input.size ≠ 1000) :
 GasSteps (DirectGuard.guardEntry input) (AbcArm.armEntry input) := by
 have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by unfold RecognitionAccumulator.Allowed at hn; omega
 exact soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)]; rfl)

private def fallbackTemplate : List Instr := [.push 1 245, .op .JUMP]
private def genericTemplate : List Instr := [.op .JUMPDEST]
private theorem fallback_slice : (Artifact.submissionArtifact.instructions.drop 3431).take fallbackTemplate.length = fallbackTemplate := by rfl
private theorem generic_slice : (Artifact.submissionArtifact.instructions.drop 130).take genericTemplate.length = genericTemplate := by rfl
private def fallbackSite : GenericRoundSite Artifact.submissionArtifact .Osaka fallbackTemplate :=
 StackSiteBuilder.ofSlice fallbackTemplate 3431 fallback_slice
  (by change 3431 + fallbackTemplate.length ≤ Artifact.submissionInstructions.length; rw [Artifact.referenceInstructions_count]; decide)
  code_bound (StackRoundData.templateWellFormed_mem (instructions := fallbackTemplate) (by decide)) (by decide)
private def genericSite : GenericRoundSite Artifact.submissionArtifact .Osaka genericTemplate :=
 StackSiteBuilder.ofSlice genericTemplate 130 generic_slice
  (by change 130 + genericTemplate.length ≤ Artifact.submissionInstructions.length; rw [Artifact.referenceInstructions_count]; decide)
  code_bound (StackRoundData.templateWellFormed_mem (instructions := genericTemplate) (by decide)) (by decide)
private theorem fallback_pc : fallbackSite.startPC = UInt256.ofNat 4703 := by
 change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3431) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem generic_pc : genericSite.startPC = UInt256.ofNat 245 := by
 change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 130) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def gasSteps_fallback (input : ByteArray) :
 GasSteps (PatternedScan.stS input 4703 []) (PatternedScan.stS input 246 []) := by
 have hj : runInstrSeq fallbackTemplate (PatternedScan.stS input 4703 []) = some (PatternedScan.stS input 245 []) := by
  simp [fallbackTemplate,runInstrSeq,DataStepper.runInstr,PatternedScan.stS,initialState,
   Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat,DirectGuard.generic_dest]
 have hg : runInstrSeq genericTemplate (PatternedScan.stS input 245 []) = some (PatternedScan.stS input 246 []) := by
  simp [genericTemplate,runInstrSeq,DataStepper.runInstr,PatternedScan.stS,initialState,
   Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat]
 have gj := RecognitionLift.gasSteps_of_raw fallbackSite _ _ rfl rfl rfl deployAddress_not_precompile fallback_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hj
 have gd := RecognitionLift.gasSteps_of_raw genericSite _ _ rfl rfl rfl deployAddress_not_precompile generic_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hg
 exact gj.trans gd

/-- Tiny misses resume the long-size gates; unsupported lengths then enter the generic compressor. -/
def gasSteps_after_arm_miss (input : ByteArray) (hfit : CalldataFits input)
 (hn : ¬ RecognitionAccumulator.Allowed input.size) :
 GasSteps (AbcArm.fallbackState input) (Execution.atPC input 246) := by
 have h256 : input.size ≠ 256 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have h376 : input.size ≠ 376 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have g1 := sound256 input _ (by rw [long_raw,if_neg (long_false input hfit 256 (by decide) h256)])
 have g2 := sound376 input _ (by rw [long_raw,if_neg (long_false input hfit 376 (by decide) h376)])
 exact g1.trans (g2.trans (gasSteps_fallback input))


#print axioms gasSteps_allowed
#print axioms gasSteps_to_arm
#print axioms gasSteps_after_arm_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
