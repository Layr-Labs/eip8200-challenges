import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc956 : Artifact.h39Artifact.instructionPC 956 = 2121 := by decide
@[simp] private theorem pc957 : Artifact.h39Artifact.instructionPC 957 = 2124 := by decide
@[simp] private theorem pc958 : Artifact.h39Artifact.instructionPC 958 = 2125 := by decide
@[simp] private theorem pc959 : Artifact.h39Artifact.instructionPC 959 = 2158 := by decide
@[simp] private theorem pc960 : Artifact.h39Artifact.instructionPC 960 = 2159 := by decide
@[simp] private theorem pc961 : Artifact.h39Artifact.instructionPC 961 = 2162 := by decide

private def pre2121 : List Located :=
  [pushAt 956 2 256,
   opAt 957 (.CALLDATALOAD),
   pushAt 958 32 (PatternFacts.prefixWord 8),
   opAt 959 (.XOR),
   pushAt 960 2 3109]

private theorem run_pre2121 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2121 (stateAt s bytes 2121) =
      some (atPC s 2162 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 8) (MachineState.readWord bytes 256), UInt256.ofNat bytes.size]) := by
  simp [pre2121, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2121 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 256 = PatternFacts.prefixWord 8 ∧
      Trace (stateAt s bytes 2121) (stateAt s bytes 2163)) ∨
      Trace (stateAt s bytes 2121) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 256 = PatternFacts.prefixWord 8
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 8) (MachineState.readWord bytes 256)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 961 .JUMPI) s 2162 3109
      (UInt256.xor (PatternFacts.prefixWord 8) (MachineState.readWord bytes 256)) [UInt256.ofNat bytes.size] rfl pc961
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2121 (opAt 961 .JUMPI) (run_pre2121 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 8) (MachineState.readWord bytes 256)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 961 .JUMPI) s 2162 3109
      (UInt256.xor (PatternFacts.prefixWord 8) (MachineState.readWord bytes 256)) [UInt256.ofNat bytes.size] rfl pc961
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2121 (opAt 961 .JUMPI) (run_pre2121 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
