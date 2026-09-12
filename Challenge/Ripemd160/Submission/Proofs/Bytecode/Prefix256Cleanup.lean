import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

@[simp] private theorem branchPC0 : Artifact.submissionArtifact.instructionPC 164 = 258 := rfl
@[simp] private theorem branchPC1 : Artifact.submissionArtifact.instructionPC 165 = 259 := rfl
@[simp] private theorem branchPC2 : Artifact.submissionArtifact.instructionPC 166 = 262 := rfl
@[simp] private theorem cleanupDupPC : Artifact.submissionArtifact.instructionPC 274 = 445 := rfl
@[simp] private theorem cleanupDest : Decode.isValidJumpDest submissionBytecode 444 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 273 (by rfl)
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 453 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 282 (by rfl)

@[simp] private theorem e4PC164 : Artifact.submissionArtifact.instructionPC 273 = 444 := rfl
@[simp] private theorem e4PC165 : Artifact.submissionArtifact.instructionPC 274 = 445 := rfl
@[simp] private theorem e4PC166 : Artifact.submissionArtifact.instructionPC 275 = 446 := rfl
@[simp] private theorem e4PC167 : Artifact.submissionArtifact.instructionPC 276 = 447 := rfl
@[simp] private theorem e4PC168 : Artifact.submissionArtifact.instructionPC 277 = 448 := rfl
@[simp] private theorem e4PC169 : Artifact.submissionArtifact.instructionPC 278 = 449 := rfl
@[simp] private theorem e4PC170 : Artifact.submissionArtifact.instructionPC 279 = 450 := rfl
@[simp] private theorem e4PC171 : Artifact.submissionArtifact.instructionPC 280 = 451 := rfl
@[simp] private theorem e4PC172 : Artifact.submissionArtifact.instructionPC 281 = 452 := rfl
@[simp] private theorem e4PC173 : Artifact.submissionArtifact.instructionPC 282 = 453 := rfl

def branchPath : List Located :=
  [opAt 164 (.Dup ⟨2, by decide⟩), pushAt 165 2 444, opAt 166 .JUMPI]

def cleanupPath : List Located :=
  [opAt 273 .JUMPDEST, opAt 274 .POP, opAt 275 .POP, opAt 276 .POP,
   opAt 277 .POP, opAt 278 .POP, opAt 279 .POP, opAt 280 .POP, opAt 281 .POP]

theorem run_branch (input : ByteArray) (sv ov acc : UInt256) :
    run branchPath (stS input 258 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (stS input (if UInt256.isTrue acc then 444 else 263)
        [sv, ov, acc, P7, M, m7, P, m8]) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [branchPath, opAt, pushAt, stS, atPC, hc,
       Challenge.Ripemd160.initialState_stack,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat]

theorem run_cleanup (input : ByteArray) (sv ov acc : UInt256)
    (_hc : UInt256.isTrue acc) :
    run cleanupPath (stS input 444 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (fallbackState input) := by
  simp (config := { maxSteps := 400000 })
    [cleanupPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange,
     Challenge.Ripemd160.initialState_stack,
     Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat]

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 258 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) := by
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
    GasSteps (stS input 258 [sv, ov, 0, P7, M, m7, P, m8])
      (stS input 263 [sv, ov, 0, P7, M, m7, P, m8]) := by
  have h := run_branch input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka branchPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
