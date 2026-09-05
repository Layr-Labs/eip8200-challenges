import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1009 : Artifact.h39Artifact.instructionPC 1009 = 2466 := by decide
@[simp] private theorem pc1010 : Artifact.h39Artifact.instructionPC 1010 = 2469 := by decide
@[simp] private theorem pc1011 : Artifact.h39Artifact.instructionPC 1011 = 2470 := by decide
@[simp] private theorem pc1012 : Artifact.h39Artifact.instructionPC 1012 = 2503 := by decide
@[simp] private theorem pc1013 : Artifact.h39Artifact.instructionPC 1013 = 2504 := by decide
@[simp] private theorem pc1014 : Artifact.h39Artifact.instructionPC 1014 = 2507 := by decide

private def pre2466 : List Located :=
  [pushAt 1009 2 512,
   opAt 1010 (.CALLDATALOAD),
   pushAt 1011 32 (PatternFacts.prefixWord 16),
   opAt 1012 (.XOR),
   pushAt 1013 2 3109]

private theorem run_pre2466 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2466 (stateAt s bytes 2466) =
      some (atPC s 2507 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 16) (MachineState.readWord bytes 512), UInt256.ofNat bytes.size]) := by
  simp [pre2466, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2466 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 512 = PatternFacts.prefixWord 16 ∧
      Trace (stateAt s bytes 2466) (stateAt s bytes 2508)) ∨
      Trace (stateAt s bytes 2466) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 512 = PatternFacts.prefixWord 16
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 16) (MachineState.readWord bytes 512)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1014 .JUMPI) s 2507 3109
      (UInt256.xor (PatternFacts.prefixWord 16) (MachineState.readWord bytes 512)) [UInt256.ofNat bytes.size] rfl pc1014
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2466 (opAt 1014 .JUMPI) (run_pre2466 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 16) (MachineState.readWord bytes 512)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1014 .JUMPI) s 2507 3109
      (UInt256.xor (PatternFacts.prefixWord 16) (MachineState.readWord bytes 512)) [UInt256.ofNat bytes.size] rfl pc1014
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2466 (opAt 1014 .JUMPI) (run_pre2466 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
