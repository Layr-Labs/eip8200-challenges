import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

@[simp] private theorem branchPC0 : Artifact.submissionArtifact.instructionPC 159 = 250 := rfl
@[simp] private theorem branchPC1 : Artifact.submissionArtifact.instructionPC 160 = 251 := rfl
@[simp] private theorem branchPC2 : Artifact.submissionArtifact.instructionPC 161 = 254 := rfl
@[simp] private theorem cleanupDupPC : Artifact.submissionArtifact.instructionPC 187 = 347 := rfl
@[simp] private theorem cleanupDest : Decode.isValidJumpDest submissionBytecode 346 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 186 (by rfl)
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 363 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 201 (by rfl)

def branchPath : List Located :=
  [opAt 159 (.Dup ⟨2, by decide⟩), pushAt 160 2 346, opAt 161 .JUMPI]

def cleanupPath : List Located :=
  [opAt 186 .JUMPDEST, opAt 187 (.Dup ⟨2, by decide⟩),
   opAt 188 (.Swap ⟨2, by decide⟩), opAt 189 .POP,
   opAt 190 (.Swap ⟨1, by decide⟩), opAt 191 (.Swap ⟨6, by decide⟩),
   opAt 192 .POP, opAt 193 .POP, opAt 194 .POP, opAt 195 .POP,
   opAt 196 .POP, opAt 197 .POP, opAt 198 .POP,
   pushAt 199 2 363, opAt 200 .JUMPI]

theorem run_branch (input : ByteArray) (sv ov acc : UInt256) :
    run branchPath (stS input 250 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (stS input (if UInt256.isTrue acc then 346 else 255)
        [sv, ov, acc, P7, M, m7, P, m8]) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [branchPath, opAt, pushAt, stS, atPC, hc,
       Challenge.Ripemd160.initialState_stack,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat]

theorem run_cleanup (input : ByteArray) (sv ov acc : UInt256)
    (hc : UInt256.isTrue acc) :
    run cleanupPath (stS input 346 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (fallbackState input) := by
  simp (config := { maxSteps := 400000 })
    [cleanupPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
     Challenge.Ripemd160.initialState_stack,
     Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat]

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 250 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) := by
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
    GasSteps (stS input 250 [sv, ov, 0, P7, M, m7, P, m8])
      (stS input 255 [sv, ov, 0, P7, M, m7, P, m8]) := by
  have h := run_branch input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka branchPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
