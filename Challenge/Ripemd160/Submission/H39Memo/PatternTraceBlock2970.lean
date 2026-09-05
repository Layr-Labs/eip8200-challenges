import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1081 : Artifact.h39Artifact.instructionPC 1081 = 2970 := by decide
@[simp] private theorem pc1082 : Artifact.h39Artifact.instructionPC 1082 = 2973 := by decide
@[simp] private theorem pc1083 : Artifact.h39Artifact.instructionPC 1083 = 2974 := by decide
@[simp] private theorem pc1084 : Artifact.h39Artifact.instructionPC 1084 = 3007 := by decide
@[simp] private theorem pc1085 : Artifact.h39Artifact.instructionPC 1085 = 3008 := by decide
@[simp] private theorem pc1086 : Artifact.h39Artifact.instructionPC 1086 = 3011 := by decide

private def pre2970 : List Located :=
  [pushAt 1081 2 896,
   opAt 1082 (.CALLDATALOAD),
   pushAt 1083 32 (PatternFacts.prefixWord 28),
   opAt 1084 (.XOR),
   pushAt 1085 2 3109]

private theorem run_pre2970 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2970 (stateAt s bytes 2970) =
      some (atPC s 3011 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 28) (MachineState.readWord bytes 896), UInt256.ofNat bytes.size]) := by
  simp [pre2970, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2970 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 896 = PatternFacts.prefixWord 28 ∧
      Trace (stateAt s bytes 2970) (stateAt s bytes 3012)) ∨
      Trace (stateAt s bytes 2970) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 896 = PatternFacts.prefixWord 28
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 28) (MachineState.readWord bytes 896)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1086 .JUMPI) s 3011 3109
      (UInt256.xor (PatternFacts.prefixWord 28) (MachineState.readWord bytes 896)) [UInt256.ofNat bytes.size] rfl pc1086
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2970 (opAt 1086 .JUMPI) (run_pre2970 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 28) (MachineState.readWord bytes 896)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1086 .JUMPI) s 3011 3109
      (UInt256.xor (PatternFacts.prefixWord 28) (MachineState.readWord bytes 896)) [UInt256.ofNat bytes.size] rfl pc1086
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2970 (opAt 1086 .JUMPI) (run_pre2970 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
