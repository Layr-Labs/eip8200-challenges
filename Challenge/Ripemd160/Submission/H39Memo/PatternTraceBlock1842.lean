import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc900 : Artifact.h39Artifact.instructionPC 900 = 1842 := by decide
@[simp] private theorem pc901 : Artifact.h39Artifact.instructionPC 901 = 1844 := by decide
@[simp] private theorem pc902 : Artifact.h39Artifact.instructionPC 902 = 1845 := by decide
@[simp] private theorem pc903 : Artifact.h39Artifact.instructionPC 903 = 1878 := by decide
@[simp] private theorem pc904 : Artifact.h39Artifact.instructionPC 904 = 1879 := by decide
@[simp] private theorem pc905 : Artifact.h39Artifact.instructionPC 905 = 1882 := by decide

private def pre1842 : List Located :=
  [pushAt 900 1 64,
   opAt 901 (.CALLDATALOAD),
   pushAt 902 32 (PatternFacts.prefixWord 2),
   opAt 903 (.XOR),
   pushAt 904 2 3109]

private theorem run_pre1842 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1842 (stateAt s bytes 1842) =
      some (atPC s 1882 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 2) (MachineState.readWord bytes 64), UInt256.ofNat bytes.size]) := by
  simp [pre1842, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases1842 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 64 = PatternFacts.prefixWord 2 ∧
      Trace (stateAt s bytes 1842) (stateAt s bytes 1883)) ∨
      Trace (stateAt s bytes 1842) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 64 = PatternFacts.prefixWord 2
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 2) (MachineState.readWord bytes 64)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 905 .JUMPI) s 1882 3109
      (UInt256.xor (PatternFacts.prefixWord 2) (MachineState.readWord bytes 64)) [UInt256.ofNat bytes.size] rfl pc905
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre1842 (opAt 905 .JUMPI) (run_pre1842 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 2) (MachineState.readWord bytes 64)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 905 .JUMPI) s 1882 3109
      (UInt256.xor (PatternFacts.prefixWord 2) (MachineState.readWord bytes 64)) [UInt256.ofNat bytes.size] rfl pc905
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre1842 (opAt 905 .JUMPI) (run_pre1842 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
