import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1069 : Artifact.h39Artifact.instructionPC 1069 = 2886 := by decide
@[simp] private theorem pc1070 : Artifact.h39Artifact.instructionPC 1070 = 2889 := by decide
@[simp] private theorem pc1071 : Artifact.h39Artifact.instructionPC 1071 = 2890 := by decide
@[simp] private theorem pc1072 : Artifact.h39Artifact.instructionPC 1072 = 2923 := by decide
@[simp] private theorem pc1073 : Artifact.h39Artifact.instructionPC 1073 = 2924 := by decide
@[simp] private theorem pc1074 : Artifact.h39Artifact.instructionPC 1074 = 2927 := by decide

private def pre2886 : List Located :=
  [pushAt 1069 2 832,
   opAt 1070 (.CALLDATALOAD),
   pushAt 1071 32 (PatternFacts.prefixWord 26),
   opAt 1072 (.XOR),
   pushAt 1073 2 3109]

private theorem run_pre2886 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2886 (stateAt s bytes 2886) =
      some (atPC s 2927 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 26) (MachineState.readWord bytes 832), UInt256.ofNat bytes.size]) := by
  simp [pre2886, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2886 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 832 = PatternFacts.prefixWord 26 ∧
      Trace (stateAt s bytes 2886) (stateAt s bytes 2928)) ∨
      Trace (stateAt s bytes 2886) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 832 = PatternFacts.prefixWord 26
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 26) (MachineState.readWord bytes 832)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1074 .JUMPI) s 2927 3109
      (UInt256.xor (PatternFacts.prefixWord 26) (MachineState.readWord bytes 832)) [UInt256.ofNat bytes.size] rfl pc1074
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2886 (opAt 1074 .JUMPI) (run_pre2886 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 26) (MachineState.readWord bytes 832)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1074 .JUMPI) s 2927 3109
      (UInt256.xor (PatternFacts.prefixWord 26) (MachineState.readWord bytes 832)) [UInt256.ofNat bytes.size] rfl pc1074
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2886 (opAt 1074 .JUMPI) (run_pre2886 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
