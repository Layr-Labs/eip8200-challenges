import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc916 : Artifact.h39Artifact.instructionPC 916 = 1899 := by decide
@[simp] private theorem pc917 : Artifact.h39Artifact.instructionPC 917 = 1901 := by decide
@[simp] private theorem pc918 : Artifact.h39Artifact.instructionPC 918 = 1902 := by decide
@[simp] private theorem pc919 : Artifact.h39Artifact.instructionPC 919 = 1935 := by decide
@[simp] private theorem pc920 : Artifact.h39Artifact.instructionPC 920 = 1936 := by decide
@[simp] private theorem pc921 : Artifact.h39Artifact.instructionPC 921 = 1939 := by decide

private def pre1899 : List Located :=
  [pushAt 916 1 96,
   opAt 917 (.CALLDATALOAD),
   pushAt 918 32 (PatternFacts.prefixWord 3),
   opAt 919 (.XOR),
   pushAt 920 2 3109]

private theorem run_pre1899 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1899 (stateAt s bytes 1899) =
      some (atPC s 1939 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 3) (MachineState.readWord bytes 96), UInt256.ofNat bytes.size]) := by
  simp [pre1899, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases1899 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 96 = PatternFacts.prefixWord 3 ∧
      Trace (stateAt s bytes 1899) (stateAt s bytes 1940)) ∨
      Trace (stateAt s bytes 1899) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 96 = PatternFacts.prefixWord 3
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 3) (MachineState.readWord bytes 96)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 921 .JUMPI) s 1939 3109
      (UInt256.xor (PatternFacts.prefixWord 3) (MachineState.readWord bytes 96)) [UInt256.ofNat bytes.size] rfl pc921
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre1899 (opAt 921 .JUMPI) (run_pre1899 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 3) (MachineState.readWord bytes 96)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 921 .JUMPI) s 1939 3109
      (UInt256.xor (PatternFacts.prefixWord 3) (MachineState.readWord bytes 96)) [UInt256.ofNat bytes.size] rfl pc921
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre1899 (opAt 921 .JUMPI) (run_pre1899 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
