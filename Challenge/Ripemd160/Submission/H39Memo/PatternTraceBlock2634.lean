import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1033 : Artifact.h39Artifact.instructionPC 1033 = 2634 := by decide
@[simp] private theorem pc1034 : Artifact.h39Artifact.instructionPC 1034 = 2637 := by decide
@[simp] private theorem pc1035 : Artifact.h39Artifact.instructionPC 1035 = 2638 := by decide
@[simp] private theorem pc1036 : Artifact.h39Artifact.instructionPC 1036 = 2671 := by decide
@[simp] private theorem pc1037 : Artifact.h39Artifact.instructionPC 1037 = 2672 := by decide
@[simp] private theorem pc1038 : Artifact.h39Artifact.instructionPC 1038 = 2675 := by decide

private def pre2634 : List Located :=
  [pushAt 1033 2 640,
   opAt 1034 (.CALLDATALOAD),
   pushAt 1035 32 (PatternFacts.prefixWord 20),
   opAt 1036 (.XOR),
   pushAt 1037 2 3109]

private theorem run_pre2634 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2634 (stateAt s bytes 2634) =
      some (atPC s 2675 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 20) (MachineState.readWord bytes 640), UInt256.ofNat bytes.size]) := by
  simp [pre2634, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2634 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 640 = PatternFacts.prefixWord 20 ∧
      Trace (stateAt s bytes 2634) (stateAt s bytes 2676)) ∨
      Trace (stateAt s bytes 2634) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 640 = PatternFacts.prefixWord 20
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 20) (MachineState.readWord bytes 640)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1038 .JUMPI) s 2675 3109
      (UInt256.xor (PatternFacts.prefixWord 20) (MachineState.readWord bytes 640)) [UInt256.ofNat bytes.size] rfl pc1038
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2634 (opAt 1038 .JUMPI) (run_pre2634 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 20) (MachineState.readWord bytes 640)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1038 .JUMPI) s 2675 3109
      (UInt256.xor (PatternFacts.prefixWord 20) (MachineState.readWord bytes 640)) [UInt256.ofNat bytes.size] rfl pc1038
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2634 (opAt 1038 .JUMPI) (run_pre2634 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
