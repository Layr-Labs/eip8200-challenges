import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1015 : Artifact.h39Artifact.instructionPC 1015 = 2508 := by decide
@[simp] private theorem pc1016 : Artifact.h39Artifact.instructionPC 1016 = 2511 := by decide
@[simp] private theorem pc1017 : Artifact.h39Artifact.instructionPC 1017 = 2512 := by decide
@[simp] private theorem pc1018 : Artifact.h39Artifact.instructionPC 1018 = 2545 := by decide
@[simp] private theorem pc1019 : Artifact.h39Artifact.instructionPC 1019 = 2546 := by decide
@[simp] private theorem pc1020 : Artifact.h39Artifact.instructionPC 1020 = 2549 := by decide

private def pre2508 : List Located :=
  [pushAt 1015 2 544,
   opAt 1016 (.CALLDATALOAD),
   pushAt 1017 32 (PatternFacts.prefixWord 17),
   opAt 1018 (.XOR),
   pushAt 1019 2 3109]

private theorem run_pre2508 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2508 (stateAt s bytes 2508) =
      some (atPC s 2549 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 17) (MachineState.readWord bytes 544), UInt256.ofNat bytes.size]) := by
  simp [pre2508, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2508 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 544 = PatternFacts.prefixWord 17 ∧
      Trace (stateAt s bytes 2508) (stateAt s bytes 2550)) ∨
      Trace (stateAt s bytes 2508) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 544 = PatternFacts.prefixWord 17
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 17) (MachineState.readWord bytes 544)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1020 .JUMPI) s 2549 3109
      (UInt256.xor (PatternFacts.prefixWord 17) (MachineState.readWord bytes 544)) [UInt256.ofNat bytes.size] rfl pc1020
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2508 (opAt 1020 .JUMPI) (run_pre2508 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 17) (MachineState.readWord bytes 544)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1020 .JUMPI) s 2549 3109
      (UInt256.xor (PatternFacts.prefixWord 17) (MachineState.readWord bytes 544)) [UInt256.ofNat bytes.size] rfl pc1020
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2508 (opAt 1020 .JUMPI) (run_pre2508 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
