import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1051 : Artifact.h39Artifact.instructionPC 1051 = 2760 := by decide
@[simp] private theorem pc1052 : Artifact.h39Artifact.instructionPC 1052 = 2763 := by decide
@[simp] private theorem pc1053 : Artifact.h39Artifact.instructionPC 1053 = 2764 := by decide
@[simp] private theorem pc1054 : Artifact.h39Artifact.instructionPC 1054 = 2797 := by decide
@[simp] private theorem pc1055 : Artifact.h39Artifact.instructionPC 1055 = 2798 := by decide
@[simp] private theorem pc1056 : Artifact.h39Artifact.instructionPC 1056 = 2801 := by decide

private def pre2760 : List Located :=
  [pushAt 1051 2 736,
   opAt 1052 (.CALLDATALOAD),
   pushAt 1053 32 (PatternFacts.prefixWord 23),
   opAt 1054 (.XOR),
   pushAt 1055 2 3109]

private theorem run_pre2760 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2760 (stateAt s bytes 2760) =
      some (atPC s 2801 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 23) (MachineState.readWord bytes 736), UInt256.ofNat bytes.size]) := by
  simp [pre2760, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2760 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 736 = PatternFacts.prefixWord 23 ∧
      Trace (stateAt s bytes 2760) (stateAt s bytes 2802)) ∨
      Trace (stateAt s bytes 2760) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 736 = PatternFacts.prefixWord 23
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 23) (MachineState.readWord bytes 736)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1056 .JUMPI) s 2801 3109
      (UInt256.xor (PatternFacts.prefixWord 23) (MachineState.readWord bytes 736)) [UInt256.ofNat bytes.size] rfl pc1056
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2760 (opAt 1056 .JUMPI) (run_pre2760 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 23) (MachineState.readWord bytes 736)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1056 .JUMPI) s 2801 3109
      (UInt256.xor (PatternFacts.prefixWord 23) (MachineState.readWord bytes 736)) [UInt256.ofNat bytes.size] rfl pc1056
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2760 (opAt 1056 .JUMPI) (run_pre2760 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
