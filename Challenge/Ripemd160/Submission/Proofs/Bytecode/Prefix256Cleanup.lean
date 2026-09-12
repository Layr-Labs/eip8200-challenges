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
@[simp] private theorem branchPC2 : Artifact.submissionArtifact.instructionPC 166 = 260 := rfl
@[simp] private theorem cleanupDupPC : Artifact.submissionArtifact.instructionPC 168 = 264 := rfl
@[simp] private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 272 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 176 (by rfl)

@[simp] private theorem e4PC165 : Artifact.submissionArtifact.instructionPC 168 = 264 := rfl
@[simp] private theorem e4PC166 : Artifact.submissionArtifact.instructionPC 169 = 265 := rfl
@[simp] private theorem e4PC167 : Artifact.submissionArtifact.instructionPC 170 = 266 := rfl
@[simp] private theorem e4PC168 : Artifact.submissionArtifact.instructionPC 171 = 267 := rfl
@[simp] private theorem e4PC169 : Artifact.submissionArtifact.instructionPC 172 = 268 := rfl
@[simp] private theorem e4PC170 : Artifact.submissionArtifact.instructionPC 173 = 269 := rfl
@[simp] private theorem e4PC171 : Artifact.submissionArtifact.instructionPC 174 = 270 := rfl
@[simp] private theorem e4PC172 : Artifact.submissionArtifact.instructionPC 175 = 271 := rfl
@[simp] private theorem e4PC173 : Artifact.submissionArtifact.instructionPC 176 = 272 := rfl

@[simp] private theorem branchJumpPC : Artifact.submissionArtifact.instructionPC 167 = 263 := rfl
@[simp] private theorem selectorDest : Decode.isValidJumpDest submissionBytecode 4810 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 3948 (by rfl)

def branchPath : List Located :=
  [opAt 164 (.Dup ⟨2, by decide⟩), opAt 165 .ISZERO,
   pushAt 166 2 4810, opAt 167 .JUMPI]

def cleanupPath : List Located :=
  [opAt 168 .POP, opAt 169 .POP, opAt 170 .POP,
   opAt 171 .POP, opAt 172 .POP, opAt 173 .POP, opAt 174 .POP, opAt 175 .POP]

theorem run_branch (input : ByteArray) (sv ov acc : UInt256) :
    run branchPath (stS input 258 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (stS input (if UInt256.isTrue acc then 264 else 4810)
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
    run cleanupPath (stS input 264 [sv, ov, acc, P7, M, m7, P, m8]) =
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
      (stS input 4810 [sv, ov, 0, P7, M, m7, P, m8]) := by
  have h := run_branch input sv ov 0
  rw [if_neg (by decide)] at h
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka branchPath
    (by rfl) (by rfl) h (by rfl) deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
