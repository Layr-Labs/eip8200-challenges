import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc858 : Artifact.h39Artifact.instructionPC 858 = 1713 := by decide
@[simp] private theorem pc859 : Artifact.h39Artifact.instructionPC 859 = 1714 := by decide
@[simp] private theorem pc860 : Artifact.h39Artifact.instructionPC 860 = 1715 := by decide
@[simp] private theorem pc861 : Artifact.h39Artifact.instructionPC 861 = 1748 := by decide
@[simp] private theorem pc862 : Artifact.h39Artifact.instructionPC 862 = 1749 := by decide
@[simp] private theorem pc863 : Artifact.h39Artifact.instructionPC 863 = 1752 := by decide

private def pre1713 : List Located :=
  [pushAt 858 0 0,
   opAt 859 (.CALLDATALOAD),
   pushAt 860 32 (PatternFacts.prefixWord 0),
   opAt 861 (.XOR),
   pushAt 862 2 3109]

private theorem run_pre1713 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1713 (stateAt s bytes 1713) =
      some (atPC s 1752 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 0) (MachineState.readWord bytes 0), UInt256.ofNat bytes.size]) := by
  simp [pre1713, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
  all_goals rfl

theorem prefix_cases1713 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 0 = PatternFacts.prefixWord 0 ∧
      Trace (stateAt s bytes 1713) (stateAt s bytes 1753)) ∨
      Trace (stateAt s bytes 1713) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 0 = PatternFacts.prefixWord 0
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 0) (MachineState.readWord bytes 0)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 863 .JUMPI) s 1752 3109
      (UInt256.xor (PatternFacts.prefixWord 0) (MachineState.readWord bytes 0)) [UInt256.ofNat bytes.size] rfl pc863
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre1713 (opAt 863 .JUMPI) (run_pre1713 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 0) (MachineState.readWord bytes 0)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 863 .JUMPI) s 1752 3109
      (UInt256.xor (PatternFacts.prefixWord 0) (MachineState.readWord bytes 0)) [UInt256.ofNat bytes.size] rfl pc863
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre1713 (opAt 863 .JUMPI) (run_pre1713 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
