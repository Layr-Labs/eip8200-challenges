import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1039 : Artifact.h39Artifact.instructionPC 1039 = 2676 := by decide
@[simp] private theorem pc1040 : Artifact.h39Artifact.instructionPC 1040 = 2679 := by decide
@[simp] private theorem pc1041 : Artifact.h39Artifact.instructionPC 1041 = 2680 := by decide
@[simp] private theorem pc1042 : Artifact.h39Artifact.instructionPC 1042 = 2713 := by decide
@[simp] private theorem pc1043 : Artifact.h39Artifact.instructionPC 1043 = 2714 := by decide
@[simp] private theorem pc1044 : Artifact.h39Artifact.instructionPC 1044 = 2717 := by decide

private def pre2676 : List Located :=
  [pushAt 1039 2 672,
   opAt 1040 (.CALLDATALOAD),
   pushAt 1041 32 (PatternFacts.prefixWord 21),
   opAt 1042 (.XOR),
   pushAt 1043 2 3109]

private theorem run_pre2676 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2676 (stateAt s bytes 2676) =
      some (atPC s 2717 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 21) (MachineState.readWord bytes 672), UInt256.ofNat bytes.size]) := by
  simp [pre2676, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2676 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 672 = PatternFacts.prefixWord 21 ∧
      Trace (stateAt s bytes 2676) (stateAt s bytes 2718)) ∨
      Trace (stateAt s bytes 2676) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 672 = PatternFacts.prefixWord 21
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 21) (MachineState.readWord bytes 672)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1044 .JUMPI) s 2717 3109
      (UInt256.xor (PatternFacts.prefixWord 21) (MachineState.readWord bytes 672)) [UInt256.ofNat bytes.size] rfl pc1044
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2676 (opAt 1044 .JUMPI) (run_pre2676 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 21) (MachineState.readWord bytes 672)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1044 .JUMPI) s 2717 3109
      (UInt256.xor (PatternFacts.prefixWord 21) (MachineState.readWord bytes 672)) [UInt256.ofNat bytes.size] rfl pc1044
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2676 (opAt 1044 .JUMPI) (run_pre2676 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
