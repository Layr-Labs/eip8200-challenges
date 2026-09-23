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
  atState s (if isTail n k then 220 else 193) (frame (current s.executionEnv.calldata n k) rho)

theorem full_iff (input : ByteArray) (n k : Nat) (hn : Allowed n) (hk : k≤last n) :
    (current input n k).off.toNat < (current input n k).full.toNat ↔ ¬ isTail n k := by
  obtain ⟨ho,hf,he,hl,hr,_⟩ := facts n k hn hk
  simpa only [current, ho, hf] using hr

theorem finish_iff (s : State) (n k : Nat) (hn : Allowed n) (hk : k≤last n) (ht : isTail n k) :
    (tailResult s (current s.executionEnv.calldata n k)).stop.toNat =
      (tailResult s (current s.executionEnv.calldata n k)).len.toNat ↔ k=last n := by
  obtain ⟨ho,hf,he,hl,hr,hfin,_⟩ := facts n k hn hk
  simpa only [tailResult, current, he, hl] using hfin ht

def route_normal (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n k : Nat) (hn : Allowed n) (hk : k≤last n) :
    GasSteps (atState s 214 (frame (current s.executionEnv.calldata n k) rho)) (loopState s n k rho) := by
  have g := moves.normalGuard (current s.executionEnv.calldata n k)
  have h := full_iff s.executionEnv.calldata n k hn hk
  by_cases ht : isTail n k
  · have hc := h.not.mpr (not_not_intro ht)
    simpa only [if_neg hc, loopState, if_pos ht] using g
  · have hc := h.mpr ht
    simpa only [if_pos hc, loopState, if_neg ht] using g

def route_transition (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n k : Nat) (hn : Allowed n) (hk : k≤last n) :
    GasSteps (atState s 287 (frame (current s.executionEnv.calldata n k) rho)) (loopState s n k rho) := by
  have g := moves.transitionGuard (current s.executionEnv.calldata n k)
  have h := full_iff s.executionEnv.calldata n k hn hk
  by_cases ht : isTail n k
  · have hc := h.not.mpr (not_not_intro ht)
    have g0 : GasSteps (atState s 287 (frame (current s.executionEnv.calldata n k) rho))
        (atState s 293 (frame (current s.executionEnv.calldata n k) rho)) := by
      simpa only [if_neg hc] using g
    simpa only [loopState, if_pos ht] using g0.trans (moves.toTail _)
  · have hc := h.mpr ht
    simpa only [if_pos hc, loopState, if_neg ht] using g

def one (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n k : Nat) (hn : Allowed n) (hk : k<last n)
    (hsize : s.executionEnv.calldata.size = n) :
    GasSteps (loopState s n k rho) (loopState s n (k+1) rho) := by
  by_cases ht : isTail n k
  · have g0 := moves.tail (current s.executionEnv.calldata n k)
    have hf : ¬ (tailResult s (current s.executionEnv.calldata n k)).stop.toNat =
        (tailResult s (current s.executionEnv.calldata n k)).len.toNat :=
      (finish_iff s n k hn (by omega) ht).not.mpr (by omega)
    have g1 := moves.finish (tailResult s (current s.executionEnv.calldata n k)) (by simp only [tailResult, current, hsize])
    have g01 : GasSteps (atState s 220 (frame (current s.executionEnv.calldata n k) rho))
        (atState s 244 (frame (tailResult s (current s.executionEnv.calldata n k)) rho)) := by
      simpa only [if_neg hf] using g0.trans g1
    have g2 := moves.transition (tailResult s (current s.executionEnv.calldata n k)) (by simp only [tailResult, current, hsize])
    have g012 : GasSteps (atState s 220 (frame (current s.executionEnv.calldata n k) rho))
        (atState s 287 (frame (current s.executionEnv.calldata n (k+1)) rho)) := by
      simpa only [transition_next s n k hn hk ht] using g01.trans g2
    simpa only [loopState, if_pos ht] using g012.trans (route_transition s rho moves n (k+1) hn (by omega))
  · have g0 := moves.normal (current s.executionEnv.calldata n k)
    have g1 : GasSteps (atState s 193 (frame (current s.executionEnv.calldata n k) rho))
        (atState s 214 (frame (current s.executionEnv.calldata n (k+1)) rho)) := by
      simpa only [normal_next s n k hn (by omega) ht] using g0
    simpa only [loopState, if_neg ht] using g1.trans (route_normal s rho moves n (k+1) hn (by omega))

def start (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    GasSteps (atState s 123 rho) (loopState s n 0 rho) := by
  have g0 : GasSteps (atState s 123 rho) (atState s 188 (frame (current s.executionEnv.calldata n 0) rho)) := by
    simpa only [hsize, init_current s.executionEnv.calldata n hn] using moves.init
  have g1 := moves.first (current s.executionEnv.calldata n 0)
  have h := full_iff s.executionEnv.calldata n 0 hn (by omega)
  have ho : (current s.executionEnv.calldata n 0).off.toNat = 0 := by rfl
  rw [ho] at h
  by_cases ht : isTail n 0
  · have hc : (current s.executionEnv.calldata n 0).full.toNat=0 := by
      have := h.not.mpr (not_not_intro ht); omega
    simpa only [if_pos hc, loopState, if_pos ht] using g0.trans g1
  · have hc : (current s.executionEnv.calldata n 0).full.toNat≠0 := by have := h.mpr ht; omega
    simpa only [if_neg hc, loopState, if_neg ht] using g0.trans g1

def words (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n m : Nat) (hn : Allowed n) (hm : m≤last n)
    (hsize : s.executionEnv.calldata.size = n) :
    GasSteps (loopState s n 0 rho) (loopState s n m rho) := by
  induction m with
  | zero => exact GasSteps.refl _
  | succ m ih => exact (ih (by omega)).trans (one s rho moves n m hn (by omega) hsize)

def accumulate (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    GasSteps (atState s 123 rho) (atState s 4699 (frame (endFrame s n) rho)) := by
  have g0 := (start s rho moves n hn hsize).trans (words s rho moves n (last n) hn (by omega) hsize)
  have ht : isTail n (last n) := Or.inl rfl
  have g1 : GasSteps (loopState s n (last n) rho) (atState s 237 (frame (endFrame s n) rho)) := by
    simpa only [loopState, if_pos ht, endFrame] using moves.tail (current s.executionEnv.calldata n (last n))
  have hc := (finish_iff s n (last n) hn (by omega) ht).mpr rfl
  have g2 : GasSteps (atState s 237 (frame (endFrame s n) rho)) (atState s 4699 (frame (endFrame s n) rho)) := by
    simpa only [endFrame, if_pos hc] using moves.finish (endFrame s n) (by simp only [endFrame, tailResult, current, hsize])
  exact g0.trans (g1.trans g2)

def gasSteps_hit (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n)
    (hzero : J2Accumulator.resultAcc s.executionEnv.calldata n=0) :
    GasSteps (atState s 123 rho) (atState s 4704 (finishRest (endFrame s n) rho)) := by
  have hc : (endFrame s n).acc.toNat=0 := by rw [end_acc s n hn, hzero]; rfl
  have g := moves.result (endFrame s n)
  have gr : GasSteps (atState s 4699 (frame (endFrame s n) rho)) (atState s 4704 (finishRest (endFrame s n) rho)) := by
    simpa only [if_pos hc] using g
  exact (accumulate s rho moves n hn hsize).trans gr

def gasSteps_miss (s : State) (rho : List UInt256) (moves : Moves s rho)
    (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n)
    (hzero : J2Accumulator.resultAcc s.executionEnv.calldata n≠0) :
    GasSteps (atState s 123 rho) (atState s 310 (finishRest (endFrame s n) rho)) := by
  have hc : (endFrame s n).acc.toNat≠0 := by
    intro h; apply hzero; apply Word.word_ext
    change (J2Accumulator.resultAcc s.executionEnv.calldata n).toNat = 0
    simpa only [end_acc s n hn] using h
  have g := moves.result (endFrame s n)
  have gr : GasSteps (atState s 4699 (frame (endFrame s n) rho)) (atState s 310 (finishRest (endFrame s n) rho)) := by
    simpa only [if_neg hc] using g
  exact (accumulate s rho moves n hn hsize).trans gr

#print axioms gasSteps_hit
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Loop
