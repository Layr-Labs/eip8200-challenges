import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1075 : Artifact.h39Artifact.instructionPC 1075 = 2928 := by decide
@[simp] private theorem pc1076 : Artifact.h39Artifact.instructionPC 1076 = 2931 := by decide
@[simp] private theorem pc1077 : Artifact.h39Artifact.instructionPC 1077 = 2932 := by decide
@[simp] private theorem pc1078 : Artifact.h39Artifact.instructionPC 1078 = 2965 := by decide
@[simp] private theorem pc1079 : Artifact.h39Artifact.instructionPC 1079 = 2966 := by decide
@[simp] private theorem pc1080 : Artifact.h39Artifact.instructionPC 1080 = 2969 := by decide

private def pre2928 : List Located :=
  [pushAt 1075 2 864,
   opAt 1076 (.CALLDATALOAD),
   pushAt 1077 32 (PatternFacts.prefixWord 27),
   opAt 1078 (.XOR),
   pushAt 1079 2 3109]

private theorem run_pre2928 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2928 (stateAt s bytes 2928) =
      some (atPC s 2969 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 27) (MachineState.readWord bytes 864), UInt256.ofNat bytes.size]) := by
  simp [pre2928, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2928 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 864 = PatternFacts.prefixWord 27 ∧
      Trace (stateAt s bytes 2928) (stateAt s bytes 2970)) ∨
      Trace (stateAt s bytes 2928) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 864 = PatternFacts.prefixWord 27
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 27) (MachineState.readWord bytes 864)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1080 .JUMPI) s 2969 3109
      (UInt256.xor (PatternFacts.prefixWord 27) (MachineState.readWord bytes 864)) [UInt256.ofNat bytes.size] rfl pc1080
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2928 (opAt 1080 .JUMPI) (run_pre2928 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 27) (MachineState.readWord bytes 864)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1080 .JUMPI) s 2969 3109
      (UInt256.xor (PatternFacts.prefixWord 27) (MachineState.readWord bytes 864)) [UInt256.ofNat bytes.size] rfl pc1080
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2928 (opAt 1080 .JUMPI) (run_pre2928 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
