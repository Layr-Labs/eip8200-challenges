import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

@[simp] private theorem helperPC0 : Artifact.submissionArtifact.instructionPC 97 = 168 := rfl
@[simp] private theorem helperPC1 : Artifact.submissionArtifact.instructionPC 98 = 169 := rfl
@[simp] private theorem helperPC2 : Artifact.submissionArtifact.instructionPC 99 = 170 := rfl
@[simp] private theorem helperPC3 : Artifact.submissionArtifact.instructionPC 100 = 173 := rfl
@[simp] private theorem cleanupPC : Artifact.submissionArtifact.instructionPC 257 = 458 := rfl
@[simp] private theorem cleanupDest : Decode.isValidJumpDest submissionBytecode 389 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 231 (by rfl)
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 3 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2 (by rfl)

@[simp] private theorem directExitPC : Artifact.submissionArtifact.instructionPC 230 = 388 := by rfl

def exitPath : List Located :=
  [opAt 230 (.Dup ⟨2, by decide⟩),
   opAt 231 .JUMPDEST,
   opAt 232 (.Swap ⟨2, by decide⟩),
   opAt 233 .POP,
   opAt 234 (.Swap ⟨1, by decide⟩),
   opAt 235 (.Swap ⟨6, by decide⟩),
   opAt 236 .POP,
   opAt 237 .POP,
   opAt 238 .POP,
   opAt 239 .POP,
   opAt 240 .POP,
   opAt 241 .POP,
   opAt 242 .POP,
   pushAt 243 1 3,
   opAt 244 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 388 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 404 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Challenge.Ripemd160.initialState_stack,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat]

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 388 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  have h := run_exit input sv ov acc
  rw [if_pos hc] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka exitPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

def gasSteps_hit (input : ByteArray) (sv ov : UInt256) :
    GasSteps (stS input 388 [sv, ov, 0, P7, M, m7, P, m8]) (stS input 404 []) := by
  have h := run_exit input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka exitPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
