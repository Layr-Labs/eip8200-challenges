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
@[simp] private theorem branchPC2 : Artifact.submissionArtifact.instructionPC 161 = 252 := rfl
@[simp] private theorem branchPC3 : Artifact.submissionArtifact.instructionPC 162 = 257 := rfl
@[simp] private theorem cleanupPadPC : Artifact.submissionArtifact.instructionPC 163 = 258 := rfl
@[simp] private theorem cleanupDupPC : Artifact.submissionArtifact.instructionPC 165 = 260 := rfl
@[simp] private theorem cleanupDest : Decode.isValidJumpDest submissionBytecode 258 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 163 (by rfl)
@[simp] private theorem digestDest : Decode.isValidJumpDest submissionBytecode 4842 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4047 (by rfl)
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 268 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 173 (by rfl)

@[simp] private theorem e4PC164 : Artifact.submissionArtifact.instructionPC 164 = 259 := rfl
@[simp] private theorem e4PC165 : Artifact.submissionArtifact.instructionPC 165 = 260 := rfl
@[simp] private theorem e4PC166 : Artifact.submissionArtifact.instructionPC 166 = 261 := rfl
@[simp] private theorem e4PC167 : Artifact.submissionArtifact.instructionPC 167 = 262 := rfl
@[simp] private theorem e4PC168 : Artifact.submissionArtifact.instructionPC 168 = 263 := rfl
@[simp] private theorem e4PC169 : Artifact.submissionArtifact.instructionPC 169 = 264 := rfl
@[simp] private theorem e4PC170 : Artifact.submissionArtifact.instructionPC 170 = 265 := rfl
@[simp] private theorem e4PC171 : Artifact.submissionArtifact.instructionPC 171 = 266 := rfl
@[simp] private theorem e4PC172 : Artifact.submissionArtifact.instructionPC 172 = 267 := rfl
@[simp] private theorem e4PC173 : Artifact.submissionArtifact.instructionPC 173 = 268 := rfl

def branchPath : List Located :=
  [opAt 159 (.Dup ⟨2, by decide⟩), opAt 160 .ISZERO, pushAt 161 4 4842,
   opAt 162 .JUMPI]

def cleanupPath : List Located :=
  [opAt 163 .JUMPDEST, opAt 164 .JUMPDEST, opAt 165 .POP, opAt 166 .POP,
   opAt 167 .POP, opAt 168 .POP, opAt 169 .POP, opAt 170 .POP,
   opAt 171 .POP, opAt 172 .POP]

theorem isTrue_isZero (a : UInt256) :
    UInt256.isTrue (UInt256.isZero a) ↔ ¬ UInt256.isTrue a := by
  unfold UInt256.isTrue UInt256.isZero
  by_cases h : a.toNat = 0 <;>
    simp [h, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_branch (input : ByteArray) (sv ov acc : UInt256) :
    run branchPath (stS input 250 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (stS input (if UInt256.isTrue acc then 258 else 4842)
        [sv, ov, acc, P7, M, m7, P, m8]) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [branchPath, opAt, pushAt, stS, atPC, hc, isTrue_isZero,
       Challenge.Ripemd160.initialState_stack,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat]

theorem run_cleanup (input : ByteArray) (sv ov acc : UInt256)
    (_hc : UInt256.isTrue acc) :
    run cleanupPath (stS input 258 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (fallbackState input) := by
  simp (config := { maxSteps := 400000 })
    [cleanupPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange,
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
      (stS input 4842 [sv, ov, 0, P7, M, m7, P, m8]) := by
  have h := run_branch input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka branchPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
