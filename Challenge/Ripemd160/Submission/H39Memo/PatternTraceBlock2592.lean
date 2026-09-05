import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1027 : Artifact.h39Artifact.instructionPC 1027 = 2592 := by decide
@[simp] private theorem pc1028 : Artifact.h39Artifact.instructionPC 1028 = 2595 := by decide
@[simp] private theorem pc1029 : Artifact.h39Artifact.instructionPC 1029 = 2596 := by decide
@[simp] private theorem pc1030 : Artifact.h39Artifact.instructionPC 1030 = 2629 := by decide
@[simp] private theorem pc1031 : Artifact.h39Artifact.instructionPC 1031 = 2630 := by decide
@[simp] private theorem pc1032 : Artifact.h39Artifact.instructionPC 1032 = 2633 := by decide

private def pre2592 : List Located :=
  [pushAt 1027 2 608,
   opAt 1028 (.CALLDATALOAD),
   pushAt 1029 32 (PatternFacts.prefixWord 19),
   opAt 1030 (.XOR),
   pushAt 1031 2 3109]

private theorem run_pre2592 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2592 (stateAt s bytes 2592) =
      some (atPC s 2633 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 19) (MachineState.readWord bytes 608), UInt256.ofNat bytes.size]) := by
  simp [pre2592, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2592 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 608 = PatternFacts.prefixWord 19 ∧
      Trace (stateAt s bytes 2592) (stateAt s bytes 2634)) ∨
      Trace (stateAt s bytes 2592) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 608 = PatternFacts.prefixWord 19
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 19) (MachineState.readWord bytes 608)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1032 .JUMPI) s 2633 3109
      (UInt256.xor (PatternFacts.prefixWord 19) (MachineState.readWord bytes 608)) [UInt256.ofNat bytes.size] rfl pc1032
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2592 (opAt 1032 .JUMPI) (run_pre2592 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 19) (MachineState.readWord bytes 608)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1032 .JUMPI) s 2633 3109
      (UInt256.xor (PatternFacts.prefixWord 19) (MachineState.readWord bytes 608)) [UInt256.ofNat bytes.size] rfl pc1032
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2592 (opAt 1032 .JUMPI) (run_pre2592 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
