import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1106 : Artifact.h39Artifact.instructionPC 1106 = 3109 := by decide
@[simp] private theorem pc1107 : Artifact.h39Artifact.instructionPC 1107 = 3110 := by decide
@[simp] private theorem pc1108 : Artifact.h39Artifact.instructionPC 1108 = 3111 := by decide
@[simp] private theorem pc1109 : Artifact.h39Artifact.instructionPC 1109 = 3114 := by decide

private def pre3109 : List Located :=
  [opAt 1106 (.JUMPDEST),
   opAt 1107 (.POP),
   pushAt 1108 2 1006]

private theorem run_pre3109 (s : State) (bytes : ByteArray) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre3109 (stateAt s bytes 3109) =
      some (atPC s 3114 (UInt256.ofNat 1006 :: [])) := by
  simp [pre3109, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

 theorem cleanup3109 (s : State) (bytes : ByteArray) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    Trace (stateAt s bytes 3109) (fallback s) := by
  have hp : (atPC s 3114 (UInt256.ofNat 1006 :: [])).pc.toNat =
      Artifact.h39Artifact.instructionPC 1109 := by
    change (UInt256.ofNat 3114).toNat = _
    rw [pc1109]
    decide
  have hb := Step.runLocated_jump (opAt 1109 .JUMP) rfl
    (atPC s 3114 (UInt256.ofNat 1006 :: [])) h39Bytecode 1006 []
    hp rfl (by simp) hcode (by decide) jump_fallback
  apply join_branch pre3109 (opAt 1109 .JUMP) (run_pre3109 s bytes hrun) hrun
  simpa only [stateAt, fallback, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

