import Challenge.Ripemd160.Submission.H39Memo.A1000Advance
import Challenge.Ripemd160.Submission.H39Memo.A1000Single

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem run_fail (s : State) (offset : UInt256)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock failPath (failEntry s offset) = some (fallback s) := by
  have hp : (atPC s 3257 [1006]).pc.toNat =
      Artifact.h39Artifact.instructionPC (opAt 1153 .JUMP).index := by
    change (UInt256.ofNat 3257).toNat = Artifact.h39Artifact.instructionPC 1153
    rw [pc1153]
    decide
  have hbranch := Step.runLocated_jump (opAt 1153 .JUMP) rfl
    (atPC s 3257 [1006]) h39Bytecode 1006 [] hp rfl (by simp) hcode (by decide) jump_fallback
  change Stepper.runLocatedBlock (failPath.take 4 ++ [opAt 1153 .JUMP])
    (failEntry s offset) = some (fallback s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_failPrefix s offset hrun) hrun
  rw [run_singleton]
  simpa only [fallback, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_notA (s : State)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock notAPath (notAEntry s) = some (pattern s) := by
  have hp : (atPC s 3263 [1696, 1000]).pc.toNat =
      Artifact.h39Artifact.instructionPC (opAt 1157 .JUMP).index := by
    change (UInt256.ofNat 3263).toNat = Artifact.h39Artifact.instructionPC 1157
    rw [pc1157]
    decide
  have hbranch := Step.runLocated_jump (opAt 1157 .JUMP) rfl
    (atPC s 3263 [1696, 1000]) h39Bytecode 1696 [1000] hp rfl (by simp) hcode (by decide) jump_pattern
  change Stepper.runLocatedBlock (notAPath.take 3 ++ [opAt 1157 .JUMP])
    (notAEntry s) = some (pattern s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_notAPrefix s hrun) hrun
  rw [run_singleton]
  simpa only [pattern, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

end Challenge.Ripemd160.Submission.H39Memo.A1000
