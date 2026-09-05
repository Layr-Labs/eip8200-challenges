import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc945 : Artifact.h39Artifact.instructionPC 945 = 2071 := by decide
@[simp] private theorem pc946 : Artifact.h39Artifact.instructionPC 946 = 2073 := by decide
@[simp] private theorem pc947 : Artifact.h39Artifact.instructionPC 947 = 2074 := by decide
@[simp] private theorem pc948 : Artifact.h39Artifact.instructionPC 948 = 2107 := by decide
@[simp] private theorem pc949 : Artifact.h39Artifact.instructionPC 949 = 2108 := by decide
@[simp] private theorem pc950 : Artifact.h39Artifact.instructionPC 950 = 2111 := by decide

private def pre2071 : List Located :=
  [pushAt 945 1 224,
   opAt 946 (.CALLDATALOAD),
   pushAt 947 32 (PatternFacts.prefixWord 7),
   opAt 948 (.XOR),
   pushAt 949 2 3109]

private theorem run_pre2071 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2071 (stateAt s bytes 2071) =
      some (atPC s 2111 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 7) (MachineState.readWord bytes 224), UInt256.ofNat bytes.size]) := by
  simp [pre2071, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2071 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 224 = PatternFacts.prefixWord 7 ∧
      Trace (stateAt s bytes 2071) (stateAt s bytes 2112)) ∨
      Trace (stateAt s bytes 2071) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 224 = PatternFacts.prefixWord 7
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 7) (MachineState.readWord bytes 224)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 950 .JUMPI) s 2111 3109
      (UInt256.xor (PatternFacts.prefixWord 7) (MachineState.readWord bytes 224)) [UInt256.ofNat bytes.size] rfl pc950
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2071 (opAt 950 .JUMPI) (run_pre2071 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 7) (MachineState.readWord bytes 224)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 950 .JUMPI) s 2111 3109
      (UInt256.xor (PatternFacts.prefixWord 7) (MachineState.readWord bytes 224)) [UInt256.ofNat bytes.size] rfl pc950
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2071 (opAt 950 .JUMPI) (run_pre2071 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
