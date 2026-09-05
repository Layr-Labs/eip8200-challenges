import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc933 : Artifact.h39Artifact.instructionPC 933 = 1989 := by decide
@[simp] private theorem pc934 : Artifact.h39Artifact.instructionPC 934 = 1991 := by decide
@[simp] private theorem pc935 : Artifact.h39Artifact.instructionPC 935 = 1992 := by decide
@[simp] private theorem pc936 : Artifact.h39Artifact.instructionPC 936 = 2025 := by decide
@[simp] private theorem pc937 : Artifact.h39Artifact.instructionPC 937 = 2026 := by decide
@[simp] private theorem pc938 : Artifact.h39Artifact.instructionPC 938 = 2029 := by decide

private def pre1989 : List Located :=
  [pushAt 933 1 160,
   opAt 934 (.CALLDATALOAD),
   pushAt 935 32 (PatternFacts.prefixWord 5),
   opAt 936 (.XOR),
   pushAt 937 2 3109]

private theorem run_pre1989 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1989 (stateAt s bytes 1989) =
      some (atPC s 2029 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 5) (MachineState.readWord bytes 160), UInt256.ofNat bytes.size]) := by
  simp [pre1989, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases1989 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 160 = PatternFacts.prefixWord 5 ∧
      Trace (stateAt s bytes 1989) (stateAt s bytes 2030)) ∨
      Trace (stateAt s bytes 1989) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 160 = PatternFacts.prefixWord 5
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 5) (MachineState.readWord bytes 160)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 938 .JUMPI) s 2029 3109
      (UInt256.xor (PatternFacts.prefixWord 5) (MachineState.readWord bytes 160)) [UInt256.ofNat bytes.size] rfl pc938
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre1989 (opAt 938 .JUMPI) (run_pre1989 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 5) (MachineState.readWord bytes 160)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 938 .JUMPI) s 2029 3109
      (UInt256.xor (PatternFacts.prefixWord 5) (MachineState.readWord bytes 160)) [UInt256.ofNat bytes.size] rfl pc938
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre1989 (opAt 938 .JUMPI) (run_pre1989 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
