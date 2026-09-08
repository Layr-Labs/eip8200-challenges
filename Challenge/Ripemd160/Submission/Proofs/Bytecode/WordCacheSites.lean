import Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheGroups
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WordCacheGroups

abbrev A := Artifact.submissionArtifact

private def advancesCheck : Instr → Bool
  | .push _ _ => true
  | .op .ADD => true
  | .op .AND => true
  | .op .OR => true
  | .op .XOR => true
  | .op .NOT => true
  | .op .SHR => true
  | .op .POP => true
  | .op .MLOAD => true
  | .op (.Dup _) => true
  | .op (.Swap _) => true
  | .op .MUL => true
  | _ => false

private theorem advancesCheck_sound (instruction : Instr)
    (h : advancesCheck instruction = true) : PairMultiplyLift.Advances instruction := by
  unfold advancesCheck at h
  split at h <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;> constructor

private theorem advances_of_all (code : List Instr)
    (h : code.all advancesCheck = true) :
    ∀ instruction ∈ code, PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  exact advancesCheck_sound instruction (List.all_eq_true.mp h instruction hmem)

def left0 : GenericRoundSite A .Osaka left0Code :=
  StackSiteBuilder.ofSlice _ 352 (by rfl) (by
    change 352 + left0Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem left0_advances :
    ∀ instruction ∈ left0Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

def left2 : GenericRoundSite A .Osaka left2Code :=
  StackSiteBuilder.ofSlice _ 922 (by rfl) (by
    change 922 + left2Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem left2_advances :
    ∀ instruction ∈ left2Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

def left4 : GenericRoundSite A .Osaka left4Code :=
  StackSiteBuilder.ofSlice _ 1542 (by rfl) (by
    change 1542 + left4Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem left4_advances :
    ∀ instruction ∈ left4Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

def right0 : GenericRoundSite A .Osaka right0Code :=
  StackSiteBuilder.ofSlice _ 2000 (by rfl) (by
    change 2000 + right0Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem right0_advances :
    ∀ instruction ∈ right0Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

def right1 : GenericRoundSite A .Osaka right1Code :=
  StackSiteBuilder.ofSlice _ 2447 (by rfl) (by
    change 2447 + right1Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem right1_advances :
    ∀ instruction ∈ right1Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

def right2 : GenericRoundSite A .Osaka right2Code :=
  StackSiteBuilder.ofSlice _ 2910 (by rfl) (by
    change 2910 + right2Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem right2_advances :
    ∀ instruction ∈ right2Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

def right4 : GenericRoundSite A .Osaka right4Code :=
  StackSiteBuilder.ofSlice _ 3530 (by rfl) (by
    change 3530 + right4Code.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem right4_advances :
    ∀ instruction ∈ right4Code, PairMultiplyLift.Advances instruction := by
  exact advances_of_all _ (by decide)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheSites
