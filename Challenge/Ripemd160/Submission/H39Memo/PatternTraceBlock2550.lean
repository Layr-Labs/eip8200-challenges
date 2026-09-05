import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1021 : Artifact.h39Artifact.instructionPC 1021 = 2550 := by decide
@[simp] private theorem pc1022 : Artifact.h39Artifact.instructionPC 1022 = 2553 := by decide
@[simp] private theorem pc1023 : Artifact.h39Artifact.instructionPC 1023 = 2554 := by decide
@[simp] private theorem pc1024 : Artifact.h39Artifact.instructionPC 1024 = 2587 := by decide
@[simp] private theorem pc1025 : Artifact.h39Artifact.instructionPC 1025 = 2588 := by decide
@[simp] private theorem pc1026 : Artifact.h39Artifact.instructionPC 1026 = 2591 := by decide

private def pre2550 : List Located :=
  [pushAt 1021 2 576,
   opAt 1022 (.CALLDATALOAD),
   pushAt 1023 32 (PatternFacts.prefixWord 18),
   opAt 1024 (.XOR),
   pushAt 1025 2 3109]

private theorem run_pre2550 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2550 (stateAt s bytes 2550) =
      some (atPC s 2591 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 18) (MachineState.readWord bytes 576), UInt256.ofNat bytes.size]) := by
  simp [pre2550, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2550 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 576 = PatternFacts.prefixWord 18 ∧
      Trace (stateAt s bytes 2550) (stateAt s bytes 2592)) ∨
      Trace (stateAt s bytes 2550) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 576 = PatternFacts.prefixWord 18
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 18) (MachineState.readWord bytes 576)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1026 .JUMPI) s 2591 3109
      (UInt256.xor (PatternFacts.prefixWord 18) (MachineState.readWord bytes 576)) [UInt256.ofNat bytes.size] rfl pc1026
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2550 (opAt 1026 .JUMPI) (run_pre2550 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 18) (MachineState.readWord bytes 576)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1026 .JUMPI) s 2591 3109
      (UInt256.xor (PatternFacts.prefixWord 18) (MachineState.readWord bytes 576)) [UInt256.ofNat bytes.size] rfl pc1026
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2550 (opAt 1026 .JUMPI) (run_pre2550 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
