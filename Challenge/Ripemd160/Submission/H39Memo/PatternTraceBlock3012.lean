import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1087 : Artifact.h39Artifact.instructionPC 1087 = 3012 := by decide
@[simp] private theorem pc1088 : Artifact.h39Artifact.instructionPC 1088 = 3015 := by decide
@[simp] private theorem pc1089 : Artifact.h39Artifact.instructionPC 1089 = 3016 := by decide
@[simp] private theorem pc1090 : Artifact.h39Artifact.instructionPC 1090 = 3049 := by decide
@[simp] private theorem pc1091 : Artifact.h39Artifact.instructionPC 1091 = 3050 := by decide
@[simp] private theorem pc1092 : Artifact.h39Artifact.instructionPC 1092 = 3053 := by decide

private def pre3012 : List Located :=
  [pushAt 1087 2 928,
   opAt 1088 (.CALLDATALOAD),
   pushAt 1089 32 (PatternFacts.prefixWord 29),
   opAt 1090 (.XOR),
   pushAt 1091 2 3109]

private theorem run_pre3012 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre3012 (stateAt s bytes 3012) =
      some (atPC s 3053 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 29) (MachineState.readWord bytes 928), UInt256.ofNat bytes.size]) := by
  simp [pre3012, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases3012 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 928 = PatternFacts.prefixWord 29 ∧
      Trace (stateAt s bytes 3012) (stateAt s bytes 3054)) ∨
      Trace (stateAt s bytes 3012) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 928 = PatternFacts.prefixWord 29
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 29) (MachineState.readWord bytes 928)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1092 .JUMPI) s 3053 3109
      (UInt256.xor (PatternFacts.prefixWord 29) (MachineState.readWord bytes 928)) [UInt256.ofNat bytes.size] rfl pc1092
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre3012 (opAt 1092 .JUMPI) (run_pre3012 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 29) (MachineState.readWord bytes 928)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1092 .JUMPI) s 3053 3109
      (UInt256.xor (PatternFacts.prefixWord 29) (MachineState.readWord bytes 928)) [UInt256.ofNat bytes.size] rfl pc1092
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre3012 (opAt 1092 .JUMPI) (run_pre3012 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
