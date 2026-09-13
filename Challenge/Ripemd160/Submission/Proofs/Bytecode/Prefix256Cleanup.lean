import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

@[simp] private theorem branchPC0 : Artifact.submissionArtifact.instructionPC 155 = 409 := rfl
@[simp] private theorem branchPC1 : Artifact.submissionArtifact.instructionPC 156 = 410 := rfl
@[simp] private theorem branchPC2 : Artifact.submissionArtifact.instructionPC 157 = 411 := rfl
@[simp] private theorem cleanupDupPC : Artifact.submissionArtifact.instructionPC 159 = 415 := rfl
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 423 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 167 (by rfl)

@[simp] private theorem e4PC165 : Artifact.submissionArtifact.instructionPC 159 = 415 := rfl
@[simp] private theorem e4PC166 : Artifact.submissionArtifact.instructionPC 160 = 416 := rfl
@[simp] private theorem e4PC167 : Artifact.submissionArtifact.instructionPC 161 = 266 := rfl
@[simp] private theorem e4PC168 : Artifact.submissionArtifact.instructionPC 162 = 418 := rfl
@[simp] private theorem e4PC169 : Artifact.submissionArtifact.instructionPC 163 = 419 := rfl
@[simp] private theorem e4PC170 : Artifact.submissionArtifact.instructionPC 164 = 420 := rfl
@[simp] private theorem e4PC171 : Artifact.submissionArtifact.instructionPC 165 = 270 := rfl
@[simp] private theorem e4PC172 : Artifact.submissionArtifact.instructionPC 166 = 422 := rfl
@[simp] private theorem e4PC173 : Artifact.submissionArtifact.instructionPC 167 = 423 := rfl

@[simp] private theorem branchJumpPC : Artifact.submissionArtifact.instructionPC 158 = 414 := rfl
@[simp] private theorem selectorDest : Decode.isValidJumpDest submissionBytecode 4837 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 3854 (by rfl)

def branchPath : List Located :=
  [opAt 155 (.Dup ⟨2, by decide⟩), opAt 156 .ISZERO,
   pushAt 157 2 4837, opAt 158 .JUMPI]

def cleanupPath : List Located :=
  [opAt 159 .POP, opAt 160 .POP, opAt 161 .POP,
   opAt 162 .POP, opAt 163 .POP, opAt 164 .POP, opAt 165 .POP, opAt 166 .POP]

theorem run_branch (input : ByteArray) (sv ov acc : UInt256) :
    run branchPath (stS input 409 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (stS input (if UInt256.isTrue acc then 415 else 4834)
        [sv, ov, acc, P7, M, m7, P, m8]) := by
  have ht : acc.isTrue ↔ acc.toNat ≠ 0 := Iff.rfl
  have hz : (UInt256.isZero acc).isTrue ↔ acc.toNat = 0 := by
    by_cases h : acc.toNat = 0 <;>
      simp [UInt256.isZero, UInt256.isTrue, h, Word.word_toNat_ofNat]
  by_cases hc : acc.toNat = 0 <;>
    simp (config := { maxSteps := 400000 })
      [branchPath, opAt, pushAt, stS, atPC, hc, ht, hz,
       Challenge.Ripemd160.initialState_stack,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat]

theorem run_cleanup (input : ByteArray) (sv ov acc : UInt256)
    (_hc : UInt256.isTrue acc) :
    run cleanupPath (stS input 415 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (fallbackState input) := by
  simp (config := { maxSteps := 400000 })
    [cleanupPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange,
     Challenge.Ripemd160.initialState_stack,
     Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat]

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 409 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  have h := run_branch input sv ov acc
  rw [if_pos hc] at h
  have branch := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka branchPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile
  have cleanup := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka cleanupPath
    (by rfl) (by rfl) (run_cleanup input sv ov acc hc) (by rfl) deployAddress_not_precompile
  exact branch.trans cleanup

def gasSteps_hit (input : ByteArray) (sv ov : UInt256) :
    GasSteps (stS input 409 [sv, ov, 0, P7, M, m7, P, m8])
      (stS input 4837 [sv, ov, 0, P7, M, m7, P, m8]) := by
  have h := run_branch input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka branchPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
