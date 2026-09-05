import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc997 : Artifact.h39Artifact.instructionPC 997 = 2382 := by decide
@[simp] private theorem pc998 : Artifact.h39Artifact.instructionPC 998 = 2385 := by decide
@[simp] private theorem pc999 : Artifact.h39Artifact.instructionPC 999 = 2386 := by decide
@[simp] private theorem pc1000 : Artifact.h39Artifact.instructionPC 1000 = 2419 := by decide
@[simp] private theorem pc1001 : Artifact.h39Artifact.instructionPC 1001 = 2420 := by decide
@[simp] private theorem pc1002 : Artifact.h39Artifact.instructionPC 1002 = 2423 := by decide

private def pre2382 : List Located :=
  [pushAt 997 2 448,
   opAt 998 (.CALLDATALOAD),
   pushAt 999 32 (PatternFacts.prefixWord 14),
   opAt 1000 (.XOR),
   pushAt 1001 2 3109]

private theorem run_pre2382 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2382 (stateAt s bytes 2382) =
      some (atPC s 2423 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 14) (MachineState.readWord bytes 448), UInt256.ofNat bytes.size]) := by
  simp [pre2382, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2382 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 448 = PatternFacts.prefixWord 14 ∧
      Trace (stateAt s bytes 2382) (stateAt s bytes 2424)) ∨
      Trace (stateAt s bytes 2382) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 448 = PatternFacts.prefixWord 14
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 14) (MachineState.readWord bytes 448)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1002 .JUMPI) s 2423 3109
      (UInt256.xor (PatternFacts.prefixWord 14) (MachineState.readWord bytes 448)) [UInt256.ofNat bytes.size] rfl pc1002
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2382 (opAt 1002 .JUMPI) (run_pre2382 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 14) (MachineState.readWord bytes 448)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1002 .JUMPI) s 2423 3109
      (UInt256.xor (PatternFacts.prefixWord 14) (MachineState.readWord bytes 448)) [UInt256.ofNat bytes.size] rfl pc1002
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2382 (opAt 1002 .JUMPI) (run_pre2382 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
