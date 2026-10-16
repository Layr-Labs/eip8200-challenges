import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2End
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Loop
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw J2Frame J2End J2Moves RecognitionAccumulator

def loopState (s : State) (n k : Nat) (rho : List UInt256) : State :=
  atState s (blockPC (blk n k)) (frame (current s.executionEnv.calldata n k) rho)

theorem finish_iff (s : State) (n k : Nat) (hn : Allowed n) (hk : k≤last n) (ht : isTail n k) :
    (tailResult s (current s.executionEnv.calldata n k)).len.toNat ≤
      (tailResult s (current s.executionEnv.calldata n k)).stop.toNat ↔ k=last n := by
  obtain ⟨ho,he,hl,hfin,_⟩ := facts n k hn hk
  simpa only [tailResult, current, he, hl] using hfin ht

theorem tail_pc (n k : Nat) (hn : Allowed n) (hk : k≤last n) (ht : isTail n k) :
    blockPC (blk n k) = 5082 := by
  rw [(chain n k hn hk).2.1 ht]; rfl

private theorem boundary_mask (n k : Nat) (hn : Allowed n) (hn256 : n ≠ 256)
    (hk : k < last n) (ht : isTail n k) : UInt256.land (UInt256.ofNat n) 32 ≠ 0 := by
  have hlong : n = 376 ∨ n = 1000 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | omega | (simp [isTail, last] at hk ht <;> omega)
  rcases hlong with rfl | rfl <;> decide

def one (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n k : Nat) (hn : Allowed n) (hk : k<last n)
    (hsize : s.executionEnv.calldata.size = n) (hn256 : n ≠ 256) :
    GasSteps (loopState s n k rho) (loopState s n (k+1) rho) := by
  by_cases ht : isTail n k
  · have hf : (current s.executionEnv.calldata n k).stop.toNat <
        (current s.executionEnv.calldata n k).len.toNat := by
      have h := facts n k hn (by omega)
      have hfin := h.2.2.2.1 ht
      simp only [current, h.2.1, h.2.2.1]
      have hnot := hfin.not.mpr (by omega)
      omega
    have g01 := moves.tailBoundary (current s.executionEnv.calldata n k)
      (by simp only [current, hsize]) hf (by simpa only [hsize] using hn256)
      (by simpa only [hsize] using boundary_mask n k hn hn256 hk ht)
    have g2 := moves.transition (tailResult s (current s.executionEnv.calldata n k))
      (by simp only [tailResult, current, hsize])
    have he := transition_chain n k hn hn256 hk ht
    have hpc : (transitionTarget (UInt256.ofNat s.executionEnv.calldata.size)).toNat = blockPC (blk n (k+1)) := by
      rw [hsize, he]
      have hc := (chain n (k+1) hn (by omega)).1
      have hb : ∀ j : Fin 8, (UInt256.ofNat (blockPC j.val)).toNat = blockPC j.val := by decide
      exact hb ⟨blk n (k+1), by omega⟩
    have g := g01.trans g2
    simpa only [transition_next s n k hn hk ht hn256, hpc, loopState, tail_pc n k hn (by omega) ht] using g
  · have hc := (chain n k hn (by omega)).2.2.1 ht
    have g0 := moves.normal (blk n k) hc.1 (current s.executionEnv.calldata n k)
    rw [normal_next s n k hn (by omega) ht, ← hc.2] at g0
    exact g0

def start (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho)) (loopState s n 0 rho) := by
  have g0 : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho)) (atState s 4877 (frame (current s.executionEnv.calldata n 0) rho)) := by
    simpa only [hsize, init_current s.executionEnv.calldata n hn] using moves.init
  have hc := chain n 0 hn (by omega)
  have g1 := moves.first (current s.executionEnv.calldata n 0) (blk n 0) hc.1 (hc.2.2.2 rfl)
  exact g0.trans g1

def words (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n m : Nat) (hn : Allowed n) (hm : m≤last n)
    (hsize : s.executionEnv.calldata.size = n) (hn256 : n ≠ 256) :
    GasSteps (loopState s n 0 rho) (loopState s n m rho) := by
  induction m with
  | zero => exact GasSteps.refl _
  | succ m ih => exact (ih (by omega)).trans (one s rho moves n m hn (by omega) hsize hn256)

def accumulate (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) (hn256 : n ≠ 256) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho)) (atState s 5102 (frame (endFrame s n) rho)) := by
  have g0 := (start s rho moves n hn hsize).trans (words s rho moves n (last n) hn (by omega) hsize hn256)
  have ht : isTail n (last n) := Or.inl rfl
  have hc := (finish_iff s n (last n) hn (by omega) ht).mpr rfl
  have hfinal : (current s.executionEnv.calldata n (last n)).len.toNat ≤
      (current s.executionEnv.calldata n (last n)).stop.toNat := hc
  have g1 : GasSteps (loopState s n (last n) rho) (atState s 5102 (frame (endFrame s n) rho)) := by
    simpa only [loopState, tail_pc n (last n) hn (by omega) ht, endFrame] using
      moves.tailFinal (current s.executionEnv.calldata n (last n))
        (by simp only [current, hsize]) hfinal
  exact g0.trans g1

def gasSteps_hit (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) (hn256 : n ≠ 256)
    (hzero : J2Accumulator.resultAcc s.executionEnv.calldata n=0) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho)) (atState s 5106 (finishRest (endFrame s n) rho)) := by
  have hc : (endFrame s n).acc.toNat=0 := by rw [end_acc s n hn, hzero]; rfl
  have g := moves.result (endFrame s n)
  have gr : GasSteps (atState s 5102 (frame (endFrame s n) rho)) (atState s 5106 (finishRest (endFrame s n) rho)) := by
    simpa only [if_pos hc] using g
  exact (accumulate s rho moves n hn hsize hn256).trans gr

def gasSteps_miss (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) (hn256 : n ≠ 256)
    (hzero : J2Accumulator.resultAcc s.executionEnv.calldata n≠0) :
    GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho)) (atState s 4565 (finishRest (endFrame s n) rho)) := by
  have hc : (endFrame s n).acc.toNat≠0 := by
    intro h; apply hzero; apply Word.word_ext
    change (J2Accumulator.resultAcc s.executionEnv.calldata n).toNat = 0
    simpa only [end_acc s n hn] using h
  have g := moves.result (endFrame s n)
  have gr : GasSteps (atState s 5102 (frame (endFrame s n) rho)) (atState s 4565 (finishRest (endFrame s n) rho)) := by
    simpa only [if_neg hc] using g
  exact (accumulate s rho moves n hn hsize hn256).trans gr

#print axioms gasSteps_hit
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Loop
