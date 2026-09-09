import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

@[simp] private theorem helperPC0 : Artifact.submissionArtifact.instructionPC 4313 = 5302 := rfl
@[simp] private theorem helperPC1 : Artifact.submissionArtifact.instructionPC 4314 = 5303 := rfl
@[simp] private theorem helperPC2 : Artifact.submissionArtifact.instructionPC 4315 = 5304 := rfl
@[simp] private theorem helperPC3 : Artifact.submissionArtifact.instructionPC 4316 = 5307 := rfl
@[simp] private theorem cleanupPC : Artifact.submissionArtifact.instructionPC 239 = 408 := rfl
@[simp] private theorem cleanupDest : Decode.isValidJumpDest submissionBytecode 408 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 239 (by rfl)
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 3 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2 (by rfl)

def exitPath : List Located :=
  [opAt 4313 .JUMPDEST, opAt 4314 (.Dup ⟨2, by decide⟩),
   pushAt 4315 2 408, opAt 4316 .JUMP,
   opAt 239 .JUMPDEST, opAt 240 (.Swap ⟨2, by decide⟩), opAt 241 .POP,
   opAt 242 (.Swap ⟨1, by decide⟩), opAt 243 (.Swap ⟨6, by decide⟩),
   opAt 244 .POP, opAt 245 .POP, opAt 246 .POP, opAt 247 .POP,
   opAt 248 .POP, opAt 249 .POP, opAt 250 .POP,
   pushAt 251 1 3, opAt 252 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5302 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 423 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Challenge.Ripemd160.initialState_stack,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat]

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5302 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) := by
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
    GasSteps (stS input 5302 [sv, ov, 0, P7, M, m7, P, m8]) (stS input 423 []) := by
  have h := run_exit input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka exitPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
