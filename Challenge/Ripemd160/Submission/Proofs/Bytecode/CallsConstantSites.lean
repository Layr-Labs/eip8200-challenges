import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace
open CallsConstantGroup CallsConstantParams

abbrev A := Artifact.submissionArtifact

theorem code_bound : A.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide

private theorem left2_slice :
    (A.instructions.drop 914).take left2Code.length = left2Code := by
  rfl

private theorem left2_wellFormed : ∀ instruction ∈ left2Code,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2 : GenericRoundSite A .Osaka left2Code :=
  StackSiteBuilder.ofSlice _ 914 left2_slice (by
    change 914 + left2Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound left2_wellFormed (by decide)

theorem left2_start : left2.startPC = UInt256.ofNat 1490 := by
  rfl

theorem left2_end : left2.endPC = UInt256.ofNat 1992 := by
  rfl

private theorem left4_slice :
    (A.instructions.drop 1537).take left4Code.length = left4Code := by
  rfl

private theorem left4_wellFormed : ∀ instruction ∈ left4Code,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4 : GenericRoundSite A .Osaka left4Code :=
  StackSiteBuilder.ofSlice _ 1537 left4_slice (by
    change 1537 + left4Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound left4_wellFormed (by decide)

theorem left4_start : left4.startPC = UInt256.ofNat 2311 := by
  rfl

theorem left4_end : left4.endPC = UInt256.ofNat 2813 := by
  rfl

private theorem right0_slice :
    (A.instructions.drop 1998).take right0Code.length = right0Code := by
  rfl

private theorem right0_wellFormed : ∀ instruction ∈ right0Code,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def right0 : GenericRoundSite A .Osaka right0Code :=
  StackSiteBuilder.ofSlice _ 1998 right0_slice (by
    change 1998 + right0Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound right0_wellFormed (by decide)

theorem right0_start : right0.startPC = UInt256.ofNat 2829 := by
  rfl

theorem right0_end : right0.endPC = UInt256.ofNat 3331 := by
  rfl

private theorem right1_slice :
    (A.instructions.drop 2448).take right1Code.length = right1Code := by
  rfl

private theorem right1_wellFormed : ∀ instruction ∈ right1Code,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def right1 : GenericRoundSite A .Osaka right1Code :=
  StackSiteBuilder.ofSlice _ 2448 right1_slice (by
    change 2448 + right1Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound right1_wellFormed (by decide)

theorem right1_start : right1.startPC = UInt256.ofNat 3331 := by
  rfl

theorem right1_end : right1.endPC = UInt256.ofNat 3849 := by
  rfl

private theorem right2_slice :
    (A.instructions.drop 2914).take right2Code.length = right2Code := by
  rfl

private theorem right2_wellFormed : ∀ instruction ∈ right2Code,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def right2 : GenericRoundSite A .Osaka right2Code :=
  StackSiteBuilder.ofSlice _ 2914 right2_slice (by
    change 2914 + right2Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound right2_wellFormed (by decide)

theorem right2_start : right2.startPC = UInt256.ofNat 3849 := by
  rfl

theorem right2_end : right2.endPC = UInt256.ofNat 4351 := by
  rfl

theorem left2_advances :
    ∀ instruction ∈ left2Code, PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  simp [left2Code, cachedFourCode, setupCode, keepCode, finishCode,
    CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
    CallsConstantCache.rewrite, CachedMaskHoistInline.template,
    PairMultiplyLift.Advances, SharedCallTrace.Advances] at hmem ⊢
  aesop (add safe constructors StraightLine)

theorem left4_advances :
    ∀ instruction ∈ left4Code, PairMultiplyLift.Advances instruction := by
  decide

theorem right0_advances :
    ∀ instruction ∈ right0Code, PairMultiplyLift.Advances instruction := by
  decide

theorem right1_advances :
    ∀ instruction ∈ right1Code, PairMultiplyLift.Advances instruction := by
  decide

theorem right2_advances :
    ∀ instruction ∈ right2Code, PairMultiplyLift.Advances instruction := by
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantSites
