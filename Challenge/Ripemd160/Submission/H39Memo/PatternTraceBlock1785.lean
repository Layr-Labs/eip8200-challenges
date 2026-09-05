import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc884 : Artifact.h39Artifact.instructionPC 884 = 1785 := by decide
@[simp] private theorem pc885 : Artifact.h39Artifact.instructionPC 885 = 1787 := by decide
@[simp] private theorem pc886 : Artifact.h39Artifact.instructionPC 886 = 1788 := by decide
@[simp] private theorem pc887 : Artifact.h39Artifact.instructionPC 887 = 1821 := by decide
@[simp] private theorem pc888 : Artifact.h39Artifact.instructionPC 888 = 1822 := by decide
@[simp] private theorem pc889 : Artifact.h39Artifact.instructionPC 889 = 1825 := by decide

private def pre1785 : List Located :=
  [pushAt 884 1 32,
   opAt 885 (.CALLDATALOAD),
   pushAt 886 32 (PatternFacts.prefixWord 1),
   opAt 887 (.XOR),
   pushAt 888 2 3109]

private theorem run_pre1785 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1785 (stateAt s bytes 1785) =
      some (atPC s 1825 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 1) (MachineState.readWord bytes 32), UInt256.ofNat bytes.size]) := by
  simp [pre1785, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases1785 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 32 = PatternFacts.prefixWord 1 ∧
      Trace (stateAt s bytes 1785) (stateAt s bytes 1826)) ∨
      Trace (stateAt s bytes 1785) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 32 = PatternFacts.prefixWord 1
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 1) (MachineState.readWord bytes 32)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 889 .JUMPI) s 1825 3109
      (UInt256.xor (PatternFacts.prefixWord 1) (MachineState.readWord bytes 32)) [UInt256.ofNat bytes.size] rfl pc889
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre1785 (opAt 889 .JUMPI) (run_pre1785 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 1) (MachineState.readWord bytes 32)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 889 .JUMPI) s 1825 3109
      (UInt256.xor (PatternFacts.prefixWord 1) (MachineState.readWord bytes 32)) [UInt256.ofNat bytes.size] rfl pc889
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre1785 (opAt 889 .JUMPI) (run_pre1785 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
