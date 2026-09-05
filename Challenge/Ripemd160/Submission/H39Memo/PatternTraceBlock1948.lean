import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc927 : Artifact.h39Artifact.instructionPC 927 = 1948 := by decide
@[simp] private theorem pc928 : Artifact.h39Artifact.instructionPC 928 = 1950 := by decide
@[simp] private theorem pc929 : Artifact.h39Artifact.instructionPC 929 = 1951 := by decide
@[simp] private theorem pc930 : Artifact.h39Artifact.instructionPC 930 = 1984 := by decide
@[simp] private theorem pc931 : Artifact.h39Artifact.instructionPC 931 = 1985 := by decide
@[simp] private theorem pc932 : Artifact.h39Artifact.instructionPC 932 = 1988 := by decide

private def pre1948 : List Located :=
  [pushAt 927 1 128,
   opAt 928 (.CALLDATALOAD),
   pushAt 929 32 (PatternFacts.prefixWord 4),
   opAt 930 (.XOR),
   pushAt 931 2 3109]

private theorem run_pre1948 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1948 (stateAt s bytes 1948) =
      some (atPC s 1988 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 4) (MachineState.readWord bytes 128), UInt256.ofNat bytes.size]) := by
  simp [pre1948, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases1948 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 128 = PatternFacts.prefixWord 4 ∧
      Trace (stateAt s bytes 1948) (stateAt s bytes 1989)) ∨
      Trace (stateAt s bytes 1948) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 128 = PatternFacts.prefixWord 4
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 4) (MachineState.readWord bytes 128)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 932 .JUMPI) s 1988 3109
      (UInt256.xor (PatternFacts.prefixWord 4) (MachineState.readWord bytes 128)) [UInt256.ofNat bytes.size] rfl pc932
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre1948 (opAt 932 .JUMPI) (run_pre1948 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 4) (MachineState.readWord bytes 128)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 932 .JUMPI) s 1988 3109
      (UInt256.xor (PatternFacts.prefixWord 4) (MachineState.readWord bytes 128)) [UInt256.ofNat bytes.size] rfl pc932
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre1948 (opAt 932 .JUMPI) (run_pre1948 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
