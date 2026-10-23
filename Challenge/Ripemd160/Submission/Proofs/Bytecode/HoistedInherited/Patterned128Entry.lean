import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.AbcArm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedSizeFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ReverseSerializeReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Patterned128Entry
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace StackRoundTemplate

private def shortTemplate : List Instr := [
 .op .JUMPDEST, .push 0 0, .push 32 86844066968427068989796192873928558300976274593144298876555195987106453258240,
 .op .CALLDATASIZE, .op .SHL, .op .SLT,
 .push 2 8191, .push 18 1805781487605728127014015497632372731427691, .op .CALLDATASIZE,
 .op .SHR, .op .AND, .op .JUMPI]
private def longTemplate (n target : Nat) : List Instr := [
 .op .CALLDATASIZE, .push 2 (UInt256.ofNat n), .op .EQ,
 .push 2 (UInt256.ofNat target), .op .JUMPI]
private theorem short_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3383).take shortTemplate.length = shortTemplate := by rfl
private theorem long256_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3395).take (longTemplate 256 7805).length = longTemplate 256 7805 := by rfl
private theorem long376_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3400).take (longTemplate 376 5666).length = longTemplate 376 5666 := by rfl
private theorem code_bound : HoistedInherited.Artifact.submissionArtifact.code.size < 2^256 := by
 change submissionBytecode.size < 2^256
 rw [referenceBytecode_size]
 decide
private def shortSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka shortTemplate :=
 StackSiteBuilder.ofSlice shortTemplate 3383 short_slice
  (by change 3383 + shortTemplate.length ≤ HoistedInherited.Artifact.submissionInstructions.length; rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
  code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := shortTemplate) (by decide)) (by decide)
private def long256Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (longTemplate 256 7805) :=
 StackSiteBuilder.ofSlice (longTemplate 256 7805) 3395 long256_slice
  (by change 3395 + (longTemplate 256 7805).length ≤ HoistedInherited.Artifact.submissionInstructions.length; rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
  code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := longTemplate 256 7805) (by decide)) (by decide)
private def long376Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (longTemplate 376 5666) :=
 StackSiteBuilder.ofSlice (longTemplate 376 5666) 3400 long376_slice
  (by change 3400 + (longTemplate 376 5666).length ≤ HoistedInherited.Artifact.submissionInstructions.length; rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
  code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := longTemplate 376 5666) (by decide)) (by decide)
private theorem short_pc : shortSite.startPC = UInt256.ofNat 4565 := by
 change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3383) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem long256_pc : long256Site.startPC = UInt256.ofNat 4629 := by
 change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3395) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem long376_pc : long376Site.startPC = UInt256.ofNat 4638 := by
 change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3400) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def sizeBit (input : ByteArray) : UInt256 :=
 UInt256.slt (UInt256.shiftLeft SignedSizeFlag.reversedMask (UInt256.ofNat input.size)) 0
private def shortSource (input : ByteArray) : UInt256 := DirectDigestRaw.shortSelected input.size
private def source (input : ByteArray) : UInt256 := DirectDigestRaw.selected 8191 input.size
private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
 unfold sizeBit
 rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl, SignedSizeFlag.flag]
 have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
 rw [SizeLookupFlag.mask_literal] at h
 simpa only [sizeFlag,Word.literal_eq_ofNat] using h
private theorem short_raw (input : ByteArray) :
 runInstrSeq shortTemplate (PatternedScan.stS input 4565 []) =
  if UInt256.isTrue (sizeBit input) then
   if Decode.isValidJumpDest submissionBytecode (shortSource input).toNat then
    some { initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } else none
  else some (PatternedScan.stS input 4629 []) := by
 simp (config := {maxSteps := 400000}) [shortTemplate,runInstrSeq,DataStepper.runInstr,
  sizeBit,shortSource,DirectDigestRaw.shortSelected,DirectDigestRaw.selectorConst,PatternedScan.stS,PatternedScan.entryRho,
  initialState,Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat,
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
private def sound256 (input : ByteArray) (t : State) (hr : runInstrSeq (longTemplate 256 7805) (PatternedScan.stS input 4629 []) = some t) :
 GasSteps (PatternedScan.stS input 4629 []) t :=
 RecognitionLift.gasSteps_of_raw long256Site _ _ rfl rfl rfl deployAddress_not_precompile long256_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
private def sound376 (input : ByteArray) (t : State) (hr : runInstrSeq (longTemplate 376 5666) (PatternedScan.stS input 4638 []) = some t) :
 GasSteps (PatternedScan.stS input 4638 []) t :=
 RecognitionLift.gasSteps_of_raw long376Site _ _ rfl rfl rfl deployAddress_not_precompile long376_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
private theorem selected_valid (input : ByteArray) (hn : RecognitionAccumulator.Allowed input.size)
  (hne : input.size ≠ 1000) :
 Decode.isValidJumpDest submissionBytecode (source input).toNat = true := by
 obtain ⟨i,hi⟩ := HoistedInherited.ReverseLiteralScan.allowed_index input.size hn hne
 change Decode.isValidJumpDest submissionBytecode (DirectDigestRaw.selected 8191 input.size).toNat = true
 rw [← hi]
 exact HoistedInherited.ReverseSerializeReturn.storeSite.valid i
private theorem short_false (input : ByteArray) (hfit : CalldataFits input)
 (hn : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0) :
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
 · have hs0 : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32 ∨ input.size = 0 := by tauto
   have hc : UInt256.isTrue (sizeBit input) := by
    have h := (sizeBit_flag input).trans (sizeFlag_hit input hs0)
    change (sizeBit input).toNat ≠ 0
    intro hz
    rw [UInt256.isZero,if_pos hz] at h
    exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) h
   have hsrc : shortSource input = source input := by
    unfold shortSource source DirectDigestRaw.selected
    rcases hs with h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> rfl
   have hv : Decode.isValidJumpDest submissionBytecode (shortSource input).toNat = true := by
    rw [hsrc]
    exact selected_valid input hn _h1000
   have hent : ({ initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } : State) = PatternedScan.patternedEntry input := by
    change ({ initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } : State) =
     { initialState submissionBytecode input 0 with pc := source input, stack := PatternedScan.entryRho input.size }
    rw [hsrc]
   exact GasSteps.cast (soundShort input _ (by rw [short_raw,if_pos hc,if_pos hv])) rfl hent
 · have h0 : input.size ≠ 0 := by unfold RecognitionAccumulator.Allowed at hn; omega
   have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0 := by tauto
   have gs := soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)])
   have hl : input.size = 256 ∨ input.size = 376 := by unfold RecognitionAccumulator.Allowed at hn; omega
   by_cases h : input.size = 256
   · have hv : Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 7805).toNat = true := by
      have hp : source input = UInt256.ofNat 7805 := by
       unfold source
       rw [h]
       decide
      simpa only [hp] using selected_valid input hn _h1000
     have gj := sound256 input (PatternedScan.stS input 7805 []) (by rw [long_raw,DirectGuard.size_eq_one input 256 h]; simp only [show UInt256.isTrue (UInt256.ofNat 1) from by decide,if_true,hv])
     have he : PatternedScan.stS input 7805 [] = PatternedScan.patternedEntry input := by
      simp [PatternedScan.stS,PatternedScan.patternedEntry,PatternedScan.entryRho,h]
     exact gs.trans (GasSteps.cast gj rfl he)
   · have h256 : input.size ≠ 256 := h
     have h : input.size = 376 := by omega
     have g1 := sound256 input _ (by rw [long_raw,if_neg (long_false input hfit 256 (by decide) h256)])
     have hv : Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 5666).toNat = true := by
      have hp : source input = UInt256.ofNat 5666 := by
       unfold source
       rw [h]
       decide
      simpa only [hp] using selected_valid input hn _h1000
     have gj := sound376 input (PatternedScan.stS input 5666 []) (by rw [long_raw,DirectGuard.size_eq_one input 376 h]; simp only [show UInt256.isTrue (UInt256.ofNat 1) from by decide,if_true,hv])
     have he : PatternedScan.stS input 5666 [] = PatternedScan.patternedEntry input := by
      simp [PatternedScan.stS,PatternedScan.patternedEntry,PatternedScan.entryRho,h]
     exact gs.trans (g1.trans (GasSteps.cast gj rfl he))

private theorem valid_empty : Decode.isValidJumpDest submissionBytecode 7019 = true := by
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 4379 (by rfl)
  rw [HoistedInherited.AbcArm.pc_emptyDest] at h
  exact h

def gasSteps_to_empty (input : ByteArray) (hz : input.size = 0) :
 GasSteps (DirectGuard.guardEntry input) (HoistedInherited.AbcArm.emptyEntry input) := by
 have hs0 : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32 ∨ input.size = 0 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz))))))))))
 have hc : UInt256.isTrue (sizeBit input) := by
  have h := (sizeBit_flag input).trans (sizeFlag_hit input hs0)
  change (sizeBit input).toNat ≠ 0
  intro hzero
  rw [UInt256.isZero,if_pos hzero] at h
  exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) h
 have hsrc : shortSource input = UInt256.ofNat 7019 := by
  unfold shortSource DirectDigestRaw.shortSelected
  rw [hz]
  decide
 have hv : Decode.isValidJumpDest submissionBytecode (shortSource input).toNat = true := by
  rw [hsrc]
  exact valid_empty
 have hent : ({ initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } : State) = HoistedInherited.AbcArm.emptyEntry input := by
  change ({ initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } : State) =
   { initialState submissionBytecode input 0 with pc := UInt256.ofNat 7019, stack := [] }
  rw [hsrc]; rfl
 exact GasSteps.cast (soundShort input _ (by rw [short_raw,if_pos hc,if_pos hv])) rfl hent

def gasSteps_to_arm (input : ByteArray) (hfit : CalldataFits input) (hn : ¬ RecognitionAccumulator.Allowed input.size) (_h1000 : input.size ≠ 1000) (h0 : input.size ≠ 0) :
 GasSteps (DirectGuard.guardEntry input) (HoistedInherited.AbcArm.armEntry input) := by
 have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have h256 : input.size ≠ 256 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have h376 : input.size ≠ 376 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have g0 := soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)])
 have g1 := sound256 input _ (by rw [long_raw,if_neg (long_false input hfit 256 (by decide) h256)])
 have g2 := sound376 input _ (by rw [long_raw,if_neg (long_false input hfit 376 (by decide) h376)])
 exact g0.trans (g1.trans g2)

private def fallbackTemplate : List Instr := [.push 1 245, .op .JUMP]
private def genericTemplate : List Instr := [.op .JUMPDEST]
private theorem fallback_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3541).take fallbackTemplate.length = fallbackTemplate := by rfl
private theorem generic_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 125).take genericTemplate.length = genericTemplate := by rfl
private def fallbackSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka fallbackTemplate :=
 StackSiteBuilder.ofSlice fallbackTemplate 3541 fallback_slice
  (by change 3541 + fallbackTemplate.length ≤ HoistedInherited.Artifact.submissionInstructions.length; rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
  code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := fallbackTemplate) (by decide)) (by decide)
private def genericSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka genericTemplate :=
 StackSiteBuilder.ofSlice genericTemplate 125 generic_slice
  (by change 125 + genericTemplate.length ≤ HoistedInherited.Artifact.submissionInstructions.length; rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
  code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := genericTemplate) (by decide)) (by decide)
private theorem fallback_pc : fallbackSite.startPC = UInt256.ofNat 4906 := by
 change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3541) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem generic_pc : genericSite.startPC = UInt256.ofNat 245 := by
 change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 125) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def gasSteps_fallback (input : ByteArray) :
 GasSteps (PatternedScan.stS input 4906 []) (PatternedScan.stS input 246 []) := by
 have hj : runInstrSeq fallbackTemplate (PatternedScan.stS input 4906 []) = some (PatternedScan.stS input 245 []) := by
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

/-- Tiny misses enter the generic compressor directly. -/
def gasSteps_after_arm_miss (input : ByteArray) (_hfit : CalldataFits input)
 (_hn : ¬ RecognitionAccumulator.Allowed input.size) :
 GasSteps (HoistedInherited.AbcArm.fallbackState input) (HoistedInherited.Execution.atPC input 246) :=
 gasSteps_fallback input


#print axioms gasSteps_allowed
#print axioms gasSteps_to_arm
#print axioms gasSteps_after_arm_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Patterned128Entry
