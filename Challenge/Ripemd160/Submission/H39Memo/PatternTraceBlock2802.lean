import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1057 : Artifact.h39Artifact.instructionPC 1057 = 2802 := by decide
@[simp] private theorem pc1058 : Artifact.h39Artifact.instructionPC 1058 = 2805 := by decide
@[simp] private theorem pc1059 : Artifact.h39Artifact.instructionPC 1059 = 2806 := by decide
@[simp] private theorem pc1060 : Artifact.h39Artifact.instructionPC 1060 = 2839 := by decide
@[simp] private theorem pc1061 : Artifact.h39Artifact.instructionPC 1061 = 2840 := by decide
@[simp] private theorem pc1062 : Artifact.h39Artifact.instructionPC 1062 = 2843 := by decide

private def pre2802 : List Located :=
  [pushAt 1057 2 768,
   opAt 1058 (.CALLDATALOAD),
   pushAt 1059 32 (PatternFacts.prefixWord 24),
   opAt 1060 (.XOR),
   pushAt 1061 2 3109]

private theorem run_pre2802 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2802 (stateAt s bytes 2802) =
      some (atPC s 2843 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 24) (MachineState.readWord bytes 768), UInt256.ofNat bytes.size]) := by
  simp [pre2802, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2802 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 768 = PatternFacts.prefixWord 24 ∧
      Trace (stateAt s bytes 2802) (stateAt s bytes 2844)) ∨
      Trace (stateAt s bytes 2802) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 768 = PatternFacts.prefixWord 24
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 24) (MachineState.readWord bytes 768)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1062 .JUMPI) s 2843 3109
      (UInt256.xor (PatternFacts.prefixWord 24) (MachineState.readWord bytes 768)) [UInt256.ofNat bytes.size] rfl pc1062
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2802 (opAt 1062 .JUMPI) (run_pre2802 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 24) (MachineState.readWord bytes 768)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1062 .JUMPI) s 2843 3109
      (UInt256.xor (PatternFacts.prefixWord 24) (MachineState.readWord bytes 768)) [UInt256.ofNat bytes.size] rfl pc1062
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2802 (opAt 1062 .JUMPI) (run_pre2802 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
