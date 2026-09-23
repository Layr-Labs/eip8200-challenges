import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryLoop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTraceCompose
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPrefix
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerIteration StaggerPersistentLoopInduction

noncomputable opaque gasSteps (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 342)) :
    GasSteps (initialState submissionBytecode input 0)
      {states input i with
        pc := UInt256.ofNat 4692
        stack := StaggerPersistentFrame.frame (hashes input i) (DriverTrace.blockOffsetWord i)
          (LoopCompletionControl.limit input) ColdHighTrace.maskRho} := by
  have gs := StaggerPersistentCorrect.gasSteps_start input hfit hpositive hn32 entryPrefix
  have ga : ∀ j, j ≤ i → Ambient input (states input j) := by
    intro j _
    exact ⟨states_code input j, states_fork input j, states_halt input j,
      states_noPrecompile input j, states_calldata input j⟩
  have gb := ColdOrdinaryLoop.run_until input (states input) (hashes input)
    ColdHighTrace.maskRho hfit (by decide) i hi ga (by
      intro j hj
      have hjc : j < DriverTrace.blockCount input := by omega
      have ho : input.size = DriverTrace.blockOffset j → input.size < 5203 := by
        intro h
        rw [DriverTrace.blockOffset] at h hh
        omega
      exact ColdOrdinaryBlock.gasSteps (states input j) input j (hashes input j)
        (LoopCompletionControl.limit input) ColdHighTrace.maskRho (by decide) [] rfl
        hfit hjc (states_context input hfit hpositive j (by omega)) ho
        (states_code input j) (states_fork input j) (states_halt input j)
        (states_noPrecompile input j))
  have hstart : GasSteps (initialState submissionBytecode input 0)
      (loopState input (states input 0) (hashes input 0) 0 (DriverTrace.blockCount input)
        ColdHighTrace.maskRho) := gs
  have hpc : LoopCompletionControl.blockPC input i = UInt256.ofNat 4692 := by
    unfold LoopCompletionControl.blockPC
    rw [show input.size = i * 64 by simpa [DriverTrace.blockOffset] using hh]
    simp
  exact (ColdTraceCompose.two hstart gb).cast rfl (by
    simp only [loopState, hpc, offsetWord, DriverTrace.blockOffsetWord, DriverTrace.blockOffset])

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPrefix
