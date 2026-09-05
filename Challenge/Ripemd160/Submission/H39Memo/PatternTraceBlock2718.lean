import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1045 : Artifact.h39Artifact.instructionPC 1045 = 2718 := by decide
@[simp] private theorem pc1046 : Artifact.h39Artifact.instructionPC 1046 = 2721 := by decide
@[simp] private theorem pc1047 : Artifact.h39Artifact.instructionPC 1047 = 2722 := by decide
@[simp] private theorem pc1048 : Artifact.h39Artifact.instructionPC 1048 = 2755 := by decide
@[simp] private theorem pc1049 : Artifact.h39Artifact.instructionPC 1049 = 2756 := by decide
@[simp] private theorem pc1050 : Artifact.h39Artifact.instructionPC 1050 = 2759 := by decide

private def pre2718 : List Located :=
  [pushAt 1045 2 704,
   opAt 1046 (.CALLDATALOAD),
   pushAt 1047 32 (PatternFacts.prefixWord 22),
   opAt 1048 (.XOR),
   pushAt 1049 2 3109]

private theorem run_pre2718 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2718 (stateAt s bytes 2718) =
      some (atPC s 2759 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 22) (MachineState.readWord bytes 704), UInt256.ofNat bytes.size]) := by
  simp [pre2718, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2718 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 704 = PatternFacts.prefixWord 22 ∧
      Trace (stateAt s bytes 2718) (stateAt s bytes 2760)) ∨
      Trace (stateAt s bytes 2718) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 704 = PatternFacts.prefixWord 22
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 22) (MachineState.readWord bytes 704)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1050 .JUMPI) s 2759 3109
      (UInt256.xor (PatternFacts.prefixWord 22) (MachineState.readWord bytes 704)) [UInt256.ofNat bytes.size] rfl pc1050
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2718 (opAt 1050 .JUMPI) (run_pre2718 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 22) (MachineState.readWord bytes 704)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1050 .JUMPI) s 2759 3109
      (UInt256.xor (PatternFacts.prefixWord 22) (MachineState.readWord bytes 704)) [UInt256.ofNat bytes.size] rfl pc1050
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2718 (opAt 1050 .JUMPI) (run_pre2718 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
