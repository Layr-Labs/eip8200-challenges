import Challenge.Ripemd160.Submission.H39Memo.A1000PCs
import Challenge.Ripemd160.Submission.H39Memo.A1000Paths
import Challenge.Ripemd160.Submission.H39Memo.Step
import Challenge.Ripemd160.Submission.H39Memo.Logic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem isTrue_iff_ne_zero (w : UInt256) : UInt256.isTrue w ↔ w ≠ 0 := by
  constructor
  · intro ht he
    apply ht
    rw [he]
    rfl
  · intro hn ht
    apply hn
    apply Challenge.EvmProof.Word.word_ext
    exact ht

theorem xor_true_iff (a b : UInt256) :
    UInt256.isTrue (UInt256.xor a b) ↔ a ≠ b := by
  simp only [isTrue_iff_ne_zero, ne_eq, Logic.wordXor_eq_zero_iff]

theorem artifact_code : Artifact.h39Artifact.code = h39Bytecode := by rfl

theorem jump_loop :
    Decode.isValidJumpDest h39Bytecode 3161 = true := by
  have h := Artifact.h39Artifact.isValidJumpDest_index 1121 (by rfl)
  simpa only [pc1121, artifact_code] using h

theorem jump_fail :
    Decode.isValidJumpDest h39Bytecode 3251 = true := by
  have h := Artifact.h39Artifact.isValidJumpDest_index 1149 (by rfl)
  simpa only [pc1149, artifact_code] using h

theorem jump_notA :
    Decode.isValidJumpDest h39Bytecode 3258 = true := by
  have h := Artifact.h39Artifact.isValidJumpDest_index 1154 (by rfl)
  simpa only [pc1154, artifact_code] using h

theorem jump_fallback :
    Decode.isValidJumpDest h39Bytecode 1006 = true := by
  have hpc : Artifact.h39Artifact.instructionPC 682 = 1006 := by decide
  have h := Artifact.h39Artifact.isValidJumpDest_index 682 (by rfl)
  simpa only [hpc, artifact_code] using h

theorem jump_pattern :
    Decode.isValidJumpDest h39Bytecode 1696 = true := by
  have hpc : Artifact.h39Artifact.instructionPC 847 = 1696 := by decide
  have h := Artifact.h39Artifact.isValidJumpDest_index 847 (by rfl)
  simpa only [hpc, artifact_code] using h

theorem branch_false (loc : Located) (s : State) (pc dest : Nat)
    (cond : UInt256) (rest : List UInt256)
    (hins : loc.instruction = .op .JUMPI)
    (hpc : Artifact.h39Artifact.instructionPC loc.index = pc)
    (hpcfit : pc < 2 ^ 256) (hlen : rest.length < 1022)
    (hcond : ¬ UInt256.isTrue cond) :
    Stepper.runLocated loc (atPC s pc (UInt256.ofNat dest :: cond :: rest)) =
      some (atPC s (pc + 1) rest) := by
  have hp : (UInt256.ofNat pc).toNat = pc := Logic.toNat_ofNat_self hpcfit
  have h := Step.runLocated_jumpi_not_taken loc hins
    (atPC s pc (UInt256.ofNat dest :: cond :: rest)) dest cond rest
    (hp.trans hpc.symm) rfl hlen hcond
  simpa [atPC, Challenge.EvmProof.Word.succ_ofNat_mod] using h

theorem branch_true (loc : Located) (s : State) (pc dest : Nat)
    (cond : UInt256) (rest : List UInt256)
    (hins : loc.instruction = .op .JUMPI)
    (hpc : Artifact.h39Artifact.instructionPC loc.index = pc)
    (hpcfit : pc < 2 ^ 256) (hdestfit : dest < 2 ^ 256)
    (hlen : rest.length < 1022) (hcond : UInt256.isTrue cond)
    (hcode : s.executionEnv.code = h39Bytecode)
    (hdest : Decode.isValidJumpDest h39Bytecode dest = true) :
    Stepper.runLocated loc (atPC s pc (UInt256.ofNat dest :: cond :: rest)) =
      some (atPC s dest rest) := by
  have hp : (UInt256.ofNat pc).toNat = pc := Logic.toNat_ofNat_self hpcfit
  have h := Step.runLocated_jumpi_taken loc hins
    (atPC s pc (UInt256.ofNat dest :: cond :: rest)) h39Bytecode dest cond rest
    (hp.trans hpc.symm) rfl hlen hcond hcode hdestfit hdest
  simpa [atPC] using h

end Challenge.Ripemd160.Submission.H39Memo.A1000
