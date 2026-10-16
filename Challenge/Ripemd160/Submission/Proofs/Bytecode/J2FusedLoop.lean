import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Loop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedLoop
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw J2Frame J2Moves J2Loop

private theorem allowed256 : RecognitionAccumulator.Allowed 256 := by
  unfold RecognitionAccumulator.Allowed; omega

/-- The first seven words use only normal steps: the first tail is at k=7,
offset 224, stop 251. No generic segment-boundary transition is used. -/
def prefix256 (s : State) (rho : List UInt256) (moves : Moves s rho)
    (hsize : s.executionEnv.calldata.size = 256) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (loopState s 256 7 rho) := by
  have words (k : Nat) (hk : k ≤ 7) :
      GasSteps (loopState s 256 0 rho) (loopState s 256 k rho) := by
    induction k with
    | zero => exact GasSteps.refl _
    | succ k ih =>
      have ht : ¬ isTail 256 k := by
        have h : ∀ j : Fin 7, ¬ isTail 256 j.val := by decide
        exact h ⟨k, by omega⟩
      have hk0 : k ≤ last 256 := by
        have hl : last 256 = 8 := by decide
        omega
      have hc := (chain 256 k allowed256 hk0).2.2.1 ht
      have g0 := moves.normal (blk 256 k) hc.1 (current s.executionEnv.calldata 256 k)
      have g1 : GasSteps (loopState s 256 k rho) (loopState s 256 (k+1) rho) := by
        simpa only [loopState, hc.2, normal_next s 256 k allowed256 hk0 ht] using g0
      exact (ih (by omega)).trans g1
  exact (start s rho moves 256 allowed256 hsize).trans (words 7 (by omega))

 theorem fusedAcc_current (s : State) :
    fusedAcc s (current s.executionEnv.calldata 256 7) =
      J2FusedAccumulator.resultAcc256 s.executionEnv.calldata := rfl

 def rest256 (s : State) (rho : List UInt256) : List UInt256 :=
  finishRest (current s.executionEnv.calldata 256 7) rho

 def boundary256 (s : State) (rho : List UInt256) (moves : Moves s rho)
    (hsize : s.executionEnv.calldata.size = 256) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s
        (if (J2FusedAccumulator.resultAcc256 s.executionEnv.calldata).toNat = 0
          then fusedReturnPC else 4565) (rest256 s rho)) := by
  have ht : isTail 256 7 := by decide
  have hf : (current s.executionEnv.calldata 256 7).stop.toNat ≠
      (current s.executionEnv.calldata 256 7).len.toNat := by
    change (UInt256.ofNat 251).toNat ≠ (UInt256.ofNat 256).toNat
    decide
  have g := moves.fusedBoundary (current s.executionEnv.calldata 256 7)
    (by simp only [current, hsize]) hf hsize
  have g' : GasSteps (loopState s 256 7 rho)
      (atState s
        (if (J2FusedAccumulator.resultAcc256 s.executionEnv.calldata).toNat = 0
          then fusedReturnPC else 4565) (rest256 s rho)) := by
    simp only [fusedAcc_current] at g
    change GasSteps (atState s 5017 _) _
    exact g
  exact (prefix256 s rho moves hsize).trans g'

 def gasSteps_hit256 (s : State) (rho : List UInt256) (moves : Moves s rho)
    (hsize : s.executionEnv.calldata.size = 256)
    (hz : J2FusedAccumulator.resultAcc256 s.executionEnv.calldata = 0) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s fusedReturnPC (rest256 s rho)) := by
  have hnat : (J2FusedAccumulator.resultAcc256 s.executionEnv.calldata).toNat = 0 := by rw [hz]; rfl
  simpa only [if_pos hnat] using boundary256 s rho moves hsize

 def gasSteps_miss256 (s : State) (rho : List UInt256) (moves : Moves s rho)
    (hsize : s.executionEnv.calldata.size = 256)
    (hz : J2FusedAccumulator.resultAcc256 s.executionEnv.calldata ≠ 0) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4565 (rest256 s rho)) := by
  have hnat : (J2FusedAccumulator.resultAcc256 s.executionEnv.calldata).toNat ≠ 0 := by
    intro h; apply hz; apply Word.word_ext; exact h
  simpa only [if_neg hnat] using boundary256 s rho moves hsize

#print axioms gasSteps_hit256
#print axioms gasSteps_miss256
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedLoop
