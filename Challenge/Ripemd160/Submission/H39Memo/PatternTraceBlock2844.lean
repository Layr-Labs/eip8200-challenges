import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1063 : Artifact.h39Artifact.instructionPC 1063 = 2844 := by decide
@[simp] private theorem pc1064 : Artifact.h39Artifact.instructionPC 1064 = 2847 := by decide
@[simp] private theorem pc1065 : Artifact.h39Artifact.instructionPC 1065 = 2848 := by decide
@[simp] private theorem pc1066 : Artifact.h39Artifact.instructionPC 1066 = 2881 := by decide
@[simp] private theorem pc1067 : Artifact.h39Artifact.instructionPC 1067 = 2882 := by decide
@[simp] private theorem pc1068 : Artifact.h39Artifact.instructionPC 1068 = 2885 := by decide

private def pre2844 : List Located :=
  [pushAt 1063 2 800,
   opAt 1064 (.CALLDATALOAD),
   pushAt 1065 32 (PatternFacts.prefixWord 25),
   opAt 1066 (.XOR),
   pushAt 1067 2 3109]

private theorem run_pre2844 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2844 (stateAt s bytes 2844) =
      some (atPC s 2885 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 25) (MachineState.readWord bytes 800), UInt256.ofNat bytes.size]) := by
  simp [pre2844, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2844 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 800 = PatternFacts.prefixWord 25 ∧
      Trace (stateAt s bytes 2844) (stateAt s bytes 2886)) ∨
      Trace (stateAt s bytes 2844) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 800 = PatternFacts.prefixWord 25
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 25) (MachineState.readWord bytes 800)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1068 .JUMPI) s 2885 3109
      (UInt256.xor (PatternFacts.prefixWord 25) (MachineState.readWord bytes 800)) [UInt256.ofNat bytes.size] rfl pc1068
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2844 (opAt 1068 .JUMPI) (run_pre2844 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 25) (MachineState.readWord bytes 800)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1068 .JUMPI) s 2885 3109
      (UInt256.xor (PatternFacts.prefixWord 25) (MachineState.readWord bytes 800)) [UInt256.ofNat bytes.size] rfl pc1068
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2844 (opAt 1068 .JUMPI) (run_pre2844 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
