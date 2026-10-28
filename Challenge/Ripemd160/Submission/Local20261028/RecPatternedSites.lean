import Challenge.Ripemd160.Submission.Local20261028.RecDirectGuardSize
import Challenge.Ripemd160.Submission.Local20261028.RecAbcArm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedSizeFlag
import Challenge.Ripemd160.Submission.Local20261028.RecShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Local20261028.ColdCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Patterned128Entry
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace StackRoundTemplate

def shortTemplate : List Instr := [
 .op .JUMPDEST, .push 0 0, .push 32 86844066968427068989796192873928558300976274593144298876555195987106453258240,
 .op .CALLDATASIZE, .op .SHL, .op .SLT,
 .push 2 8191, .push 18 2754871544244090618950329610157160902180841, .op .CALLDATASIZE,
 .op .SHR, .op .AND, .op .JUMPI]
def longTemplate (n target : Nat) : List Instr := [
 .op .CALLDATASIZE, .push 2 (UInt256.ofNat n), .op .EQ,
 .push 2 (UInt256.ofNat target), .op .JUMPI]
theorem short_slice : (Control.Artifact.submissionArtifact.instructions.drop 6182).take shortTemplate.length = shortTemplate := by rfl
theorem long256_slice : (Control.Artifact.submissionArtifact.instructions.drop 6194).take (longTemplate 256 9302).length = longTemplate 256 9302 := by rfl
theorem long376_slice : (Control.Artifact.submissionArtifact.instructions.drop 6199).take (longTemplate 376 9331).length = longTemplate 376 9331 := by rfl
theorem code_bound : Control.Artifact.submissionArtifact.code.size < 2^256 := by
 change submissionBytecode.size < 2^256
 rw [referenceBytecode_size]
 decide
def shortSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka shortTemplate :=
 StackSiteBuilder.ofSlice shortTemplate 6182 short_slice
  (by change 6182 + shortTemplate.length ≤ Control.Artifact.submissionInstructions.length; rw [CandidateArtifact.instruction_count]; decide)
  code_bound (Control.StackRoundData.templateWellFormed_mem (instructions := shortTemplate) (by decide)) (by decide)
def long256Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (longTemplate 256 9302) :=
 StackSiteBuilder.ofSlice (longTemplate 256 9302) 6194 long256_slice
  (by change 6194 + (longTemplate 256 9302).length ≤ Control.Artifact.submissionInstructions.length; rw [CandidateArtifact.instruction_count]; decide)
  code_bound (Control.StackRoundData.templateWellFormed_mem (instructions := longTemplate 256 9302) (by decide)) (by decide)
def long376Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (longTemplate 376 9331) :=
 StackSiteBuilder.ofSlice (longTemplate 376 9331) 6199 long376_slice
  (by change 6199 + (longTemplate 376 9331).length ≤ Control.Artifact.submissionInstructions.length; rw [CandidateArtifact.instruction_count]; decide)
  code_bound (Control.StackRoundData.templateWellFormed_mem (instructions := longTemplate 376 9331) (by decide)) (by decide)
theorem short_pc : shortSite.startPC = UInt256.ofNat 8247 := by
 change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6182) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem long256_pc : long256Site.startPC = UInt256.ofNat 8311 := by
 change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6194) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem long376_pc : long376Site.startPC = UInt256.ofNat 8320 := by
 change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6199) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def sizeBit (input : ByteArray) : UInt256 :=
 UInt256.slt (UInt256.shiftLeft SignedSizeFlag.reversedMask (UInt256.ofNat input.size)) 0
def shortSelectorConst : Nat := 2754871544244090618950329610157160902180841
def shortSource (input : ByteArray) : UInt256 :=
 UInt256.land (UInt256.shiftRight (UInt256.ofNat shortSelectorConst) (UInt256.ofNat input.size))
   (UInt256.ofNat 8191)
theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
 unfold sizeBit
 rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl, SignedSizeFlag.flag]
 have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
 rw [SizeLookupFlag.mask_literal] at h
 simpa only [sizeFlag,Word.literal_eq_ofNat] using h
theorem short_raw (input : ByteArray) :
 runInstrSeq shortTemplate (PatternedScan.stS input 8247 []) =
  if UInt256.isTrue (sizeBit input) then
   if Decode.isValidJumpDest submissionBytecode (shortSource input).toNat then
    some { initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } else none
  else some (PatternedScan.stS input 8311 []) := by
 simp (config := {maxSteps := 400000}) [shortTemplate,runInstrSeq,DataStepper.runInstr,
  sizeBit,shortSource,shortSelectorConst,PatternedScan.stS,PatternedScan.entryRho,
  initialState,Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat,
  RawExpressionAC.land_comm]
 split_ifs <;> simp_all
theorem long_raw (input : ByteArray) (n target pc : Nat) :
 runInstrSeq (longTemplate n target) (PatternedScan.stS input pc []) =
  if UInt256.isTrue (UInt256.eq (UInt256.ofNat n) (UInt256.ofNat input.size)) then
   if Decode.isValidJumpDest submissionBytecode (UInt256.ofNat target).toNat then
    some (PatternedScan.stS input target []) else none
  else some (PatternedScan.stS input (pc+9) []) := by
 simp (config := {maxSteps := 400000}) [longTemplate,runInstrSeq,DataStepper.runInstr,
  PatternedScan.stS,initialState,Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat, Nat.add_assoc]
 split_ifs <;> simp_all

def soundShort (input : ByteArray) (t : State) (hr : runInstrSeq shortTemplate (PatternedScan.stS input 8247 []) = some t) :
 GasSteps (PatternedScan.stS input 8247 []) t :=
 RecognitionLift.gasSteps_of_raw shortSite _ _ rfl rfl rfl deployAddress_not_precompile short_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
def sound256 (input : ByteArray) (t : State) (hr : runInstrSeq (longTemplate 256 9302) (PatternedScan.stS input 8311 []) = some t) :
 GasSteps (PatternedScan.stS input 8311 []) t :=
 RecognitionLift.gasSteps_of_raw long256Site _ _ rfl rfl rfl deployAddress_not_precompile long256_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
def sound376 (input : ByteArray) (t : State) (hr : runInstrSeq (longTemplate 376 9331) (PatternedScan.stS input 8320 []) = some t) :
 GasSteps (PatternedScan.stS input 8320 []) t :=
 RecognitionLift.gasSteps_of_raw long376Site _ _ rfl rfl rfl deployAddress_not_precompile long376_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) hr
theorem short_false (input : ByteArray) (hfit : CalldataFits input)
 (hn : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0) :
 ¬ UInt256.isTrue (sizeBit input) := by
 have h : UInt256.isZero (sizeBit input) = UInt256.ofNat 1 := (sizeBit_flag input).trans (sizeFlag_fail input hfit hn)
 intro ht
 change (sizeBit input).toNat ≠ 0 at ht
 rw [UInt256.isZero,if_neg ht] at h
 exact (by decide : UInt256.ofNat 0 ≠ UInt256.ofNat 1) h
theorem long_false (input : ByteArray) (hfit : CalldataFits input) (n : Nat) (hn : n < 2^256) (hs : input.size ≠ n) :
 ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat n) (UInt256.ofNat input.size)) := by
 rw [DirectGuard.size_eq_zero input n (Nat.lt_trans hfit (by norm_num)) hn hs]
 decide

/-- Sizes in the short table jump to their table entry. -/
def gasSteps_short (input : ByteArray)
 (hs0 : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32 ∨ input.size = 0)
 (hv : Decode.isValidJumpDest submissionBytecode (shortSource input).toNat = true) :
 GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input (shortSource input).toNat []) := by
 have hc : UInt256.isTrue (sizeBit input) := by
  have h := (sizeBit_flag input).trans (sizeFlag_hit input hs0)
  change (sizeBit input).toNat ≠ 0
  intro hzero
  rw [UInt256.isZero,if_pos hzero] at h
  exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) h
 have hent : ({ initialState submissionBytecode input 0 with pc := shortSource input, stack := PatternedScan.entryRho input.size } : State) = PatternedScan.stS input (shortSource input).toNat [] := by
  simp only [PatternedScan.stS, PatternedScan.entryRho]
  rw [← Word.word_eq_ofNat_toNat]
 exact GasSteps.cast (soundShort input _ (by rw [short_raw,if_pos hc,if_pos hv])) rfl hent

theorem shortSource_eq (input : ByteArray) (n target : Nat) (h : input.size = n)
 (ht : (UInt256.land (UInt256.shiftRight (UInt256.ofNat shortSelectorConst) (UInt256.ofNat n))
   (UInt256.ofNat 8191)) = UInt256.ofNat target) : shortSource input = UInt256.ofNat target := by
 unfold shortSource
 rw [h, ht]

def gasSteps_256 (input : ByteArray) (hfit : CalldataFits input) (h : input.size = 256)
 (hv : Decode.isValidJumpDest submissionBytecode 9302 = true) :
 GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 9302 []) := by
 have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0 := by omega
 have gs := soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)])
 have gj := sound256 input (PatternedScan.stS input 9302 []) (by rw [long_raw,DirectGuard.size_eq_one input 256 h]; simp only [show UInt256.isTrue (UInt256.ofNat 1) from by decide,if_true,Word.word_toNat_ofNat]; rw [if_pos (by simpa using hv)])
 exact gs.trans gj

def gasSteps_376 (input : ByteArray) (hfit : CalldataFits input) (h : input.size = 376)
 (hv : Decode.isValidJumpDest submissionBytecode 9331 = true) :
 GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 9331 []) := by
 have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0 := by omega
 have gs := soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)])
 have g1 := sound256 input _ (by rw [long_raw,if_neg (long_false input hfit 256 (by decide) (by omega))])
 have gj := sound376 input (PatternedScan.stS input 9331 []) (by rw [long_raw,DirectGuard.size_eq_one input 376 h]; simp only [show UInt256.isTrue (UInt256.ofNat 1) from by decide,if_true,Word.word_toNat_ofNat]; rw [if_pos (by simpa using hv)])
 exact gs.trans (g1.trans gj)

def gasSteps_to_arm (input : ByteArray) (hfit : CalldataFits input) (hn : ¬ RecognitionAccumulator.Allowed input.size) (_h1000 : input.size ≠ 1000) (h0 : input.size ≠ 0) :
 GasSteps (DirectGuard.guardEntry input) (Control.AbcArm.armEntry input) := by
 have hns : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 ∧ input.size ≠ 0 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have h256 : input.size ≠ 256 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have h376 : input.size ≠ 376 := by unfold RecognitionAccumulator.Allowed at hn; omega
 have g0 := soundShort input _ (by rw [short_raw,if_neg (short_false input hfit hns)])
 have g1 := sound256 input _ (by rw [long_raw,if_neg (long_false input hfit 256 (by decide) h256)])
 have g2 := sound376 input _ (by rw [long_raw,if_neg (long_false input hfit 376 (by decide) h376)])
 exact g0.trans (g1.trans g2)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Patterned128Entry
