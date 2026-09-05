import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1104 : Artifact.h39Artifact.instructionPC 1104 = 3105 := by decide
@[simp] private theorem pc1105 : Artifact.h39Artifact.instructionPC 1105 = 3108 := by decide

private def pre3105 : List Located :=
  [pushAt 1104 2 3109]

private theorem run_pre3105 (s : State) (bytes : ByteArray) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre3105 (stateAt s bytes 3105) =
      some (atPC s 3108 (UInt256.ofNat 3109 :: [UInt256.ofNat bytes.size])) := by
  simp [pre3105, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

 theorem cleanup3105 (s : State) (bytes : ByteArray) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    Trace (stateAt s bytes 3105) (stateAt s bytes 3109) := by
  have hp : (atPC s 3108 (UInt256.ofNat 3109 :: [UInt256.ofNat bytes.size])).pc.toNat =
      Artifact.h39Artifact.instructionPC 1105 := by
    change (UInt256.ofNat 3108).toNat = _
    rw [pc1105]
    decide
  have hb := Step.runLocated_jump (opAt 1105 .JUMP) rfl
    (atPC s 3108 (UInt256.ofNat 3109 :: [UInt256.ofNat bytes.size])) h39Bytecode 3109 [UInt256.ofNat bytes.size]
    hp rfl (by simp) hcode (by decide) jump3109
  apply join_branch pre3105 (opAt 1105 .JUMP) (run_pre3105 s bytes hrun) hrun
  simpa only [stateAt, fallback, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

