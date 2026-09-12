import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionMovement
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLoopFacts
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLoop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open RecognitionSites RecognitionMovement RecognitionBodyRaw RecognitionFrame RecognitionLoopFacts
open RecognitionAccumulator RecognitionRecurrence

def loopState (s : State) (n k : Nat) (rho : List UInt256) : State :=
  atState s (if k=n/32 then 291 else if boundary k then 223 else 185)
    (frame (fullFrame s.executionEnv.calldata n k) rho)

def gasSteps_route_head (s : State) (e : Env s) (n k : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hk : k ≤ n/32) :
    GasSteps (atState s 176 (frame (fullFrame s.executionEnv.calldata n k) rho))
      (loopState s n k rho) := by
  have hstop := lt_stop_iff s.executionEnv.calldata n k hn hk
  have hfull := off_lt_full_iff s.executionEnv.calldata n k hn hk
  by_cases hd : k=n/32
  · have he : (fullFrame s.executionEnv.calldata n k).stop.toNat ≤
        (fullFrame s.executionEnv.calldata n k).off.toNat := by
      have hnot : ¬ k<n/32 := by omega
      have := hstop.not.mpr (by simp [hnot])
      omega
    have g := (gasSteps_test0_exit s e _ rho hs he).trans (gasSteps_skip s e _ rho hs)
    have ge := gasSteps_segment_yes s e _ rho hs (hfull.not.mpr (by omega))
    simpa only [loopState, if_pos hd] using g.trans ge
  · have hlt : k<n/32 := by omega
    by_cases hb : boundary k=false
    · have g := gasSteps_test0_continue s e _ rho hs (hstop.mpr ⟨hlt,hb⟩)
      simpa only [loopState, if_neg hd, hb, Bool.false_eq_true, ↓reduceIte] using g
    · have hbtrue : boundary k=true := by cases h : boundary k <;> simp_all
      have he : (fullFrame s.executionEnv.calldata n k).stop.toNat ≤
          (fullFrame s.executionEnv.calldata n k).off.toNat := by
        have := hstop.not.mpr (by simp [hb])
        omega
      have g := (gasSteps_test0_exit s e _ rho hs he).trans (gasSteps_skip s e _ rho hs)
      have ge := gasSteps_segment_no s e _ rho hs (not_not_intro (hfull.mpr hlt))
      simpa only [loopState, if_neg hd, hbtrue, ↓reduceIte] using g.trans ge

def gasSteps_route_normal (s : State) (e : Env s) (n k : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hk : k ≤ n/32) :
    GasSteps (atState s 208 (frame (fullFrame s.executionEnv.calldata n k) rho))
      (loopState s n k rho) := by
  have hstop := lt_stop_iff s.executionEnv.calldata n k hn hk
  have hfull := off_lt_full_iff s.executionEnv.calldata n k hn hk
  by_cases hd : k=n/32
  · have he : (fullFrame s.executionEnv.calldata n k).stop.toNat ≤
        (fullFrame s.executionEnv.calldata n k).off.toNat := by
      have hnot : ¬ k<n/32 := by omega
      have := hstop.not.mpr (by simp [hnot])
      omega
    have g := (gasSteps_test_exit s e _ rho hs he)
    have ge := gasSteps_segment_yes s e _ rho hs (hfull.not.mpr (by omega))
    simpa only [loopState, if_pos hd] using g.trans ge
  · have hlt : k<n/32 := by omega
    by_cases hb : boundary k=false
    · have g := gasSteps_test_continue s e _ rho hs (hstop.mpr ⟨hlt,hb⟩)
      simpa only [loopState, if_neg hd, hb, Bool.false_eq_true, ↓reduceIte] using g
    · have hbtrue : boundary k=true := by cases h : boundary k <;> simp_all
      have he : (fullFrame s.executionEnv.calldata n k).stop.toNat ≤
          (fullFrame s.executionEnv.calldata n k).off.toNat := by
        have := hstop.not.mpr (by simp [hb])
        omega
      have g := (gasSteps_test_exit s e _ rho hs he)
      have ge := gasSteps_segment_no s e _ rho hs (not_not_intro (hfull.mpr hlt))
      simpa only [loopState, if_neg hd, hbtrue, ↓reduceIte] using g.trans ge

def gasSteps_one (s : State) (e : Env s) (n k : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hk : k<n/32) :
    GasSteps (loopState s n k rho) (loopState s n (k+1) rho) := by
  have hbnd := allowed_bounds n hn
  have hne : k ≠ n/32 := by omega
  by_cases hb : boundary k=true
  · have g0 := gasSteps_boundary s e (fullFrame s.executionEnv.calldata n k) rho hs
    have g1 := gasSteps_clamp s e (RecognitionBodyRaw.boundaryResult s
      (fullFrame s.executionEnv.calldata n k)) rho hs
    have g2 : GasSteps (atState s 223 (frame (fullFrame s.executionEnv.calldata n k) rho))
        (atState s 287 (frame (fullFrame s.executionEnv.calldata n (k+1)) rho)) := by
      simpa only [RecognitionFrame.boundary_next s n k hn hk hb] using g0.trans g1
    have g3 := gasSteps_back s e (fullFrame s.executionEnv.calldata n (k+1)) rho hs
    have g4 := gasSteps_pass s e (fullFrame s.executionEnv.calldata n (k+1)) rho hs
    have g5 := gasSteps_route_head s e n (k+1) rho hs hn (by omega)
    simpa only [loopState, if_neg hne, hb, ↓reduceIte] using g2.trans (g3.trans (g4.trans g5))
  · have hbfalse : boundary k=false := by cases h : boundary k <;> simp_all
    have g0 : GasSteps (atState s 185 (frame (fullFrame s.executionEnv.calldata n k) rho))
        (atState s 208 (frame (fullFrame s.executionEnv.calldata n (k+1)) rho)) := by
      simpa only [RecognitionFrame.normal_next s n k (by omega) hbfalse] using
        gasSteps_normal s e (fullFrame s.executionEnv.calldata n k) rho hs
    have g1 := gasSteps_route_normal s e n (k+1) rho hs hn (by omega)
    simpa only [loopState, if_neg hne, hbfalse, Bool.false_eq_true, ↓reduceIte] using g0.trans g1

def gasSteps_words (s : State) (e : Env s) (n m : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hm : m≤n/32) :
    GasSteps (loopState s n 0 rho) (loopState s n m rho) := by
  induction m with
  | zero => exact GasSteps.refl _
  | succ m ih => exact (ih (by omega)).trans (gasSteps_one s e n m rho hs hn (by omega))

def gasSteps_start (s : State) (e : Env s) (n : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    GasSteps (atState s 108 rho) (loopState s n 0 rho) := by
  have gi := gasSteps_init s e rho hs
  have gc := gasSteps_clamp0 s e (RecognitionControlRaw.initResult s.executionEnv.calldata.size) rho hs
  have g0 : GasSteps (atState s 108 rho)
      (atState s 174 (frame (fullFrame s.executionEnv.calldata n 0) rho)) := by
    simpa only [hsize, RecognitionFrame.init_clamped s.executionEnv.calldata n hn] using gi.trans gc
  exact g0.trans ((gasSteps_pass0 s e _ rho hs).trans (gasSteps_route_head s e n 0 rho hs hn (by omega)))

def endFrame (s : State) (n : Nat) : RecognitionBodyRaw.Frame :=
  if n%32=0 then fullFrame s.executionEnv.calldata n (n/32)
  else RecognitionControlRaw.partialResult s (fullFrame s.executionEnv.calldata n (n/32))

def endState (s : State) (n : Nat) (rho : List UInt256) : State :=
  atState s 315 (frame (endFrame s n) rho)

theorem endFrame_acc (s : State) (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    (endFrame s n).acc = resultAcc s.executionEnv.calldata n := by
  by_cases hm : n%32=0
  · simp only [endFrame, if_pos hm, resultAcc, fullFrame]
  · simpa only [endFrame, if_neg hm] using RecognitionFrame.partial_acc s n hn hsize hm

def gasSteps_end (s : State) (e : Env s) (n : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    GasSteps (loopState s n (n/32) rho) (endState s n rho) := by
  have hc := off_eq_size_iff s.executionEnv.calldata n hn hsize
  by_cases hm : n%32=0
  · have g := gasSteps_partialBranch_yes s e (fullFrame s.executionEnv.calldata n (n/32)) rho hs (hc.mpr hm)
    simpa only [loopState, if_pos rfl, ↓reduceIte, endState, endFrame, if_pos hm] using g
  · have g0 := gasSteps_partialBranch_no s e (fullFrame s.executionEnv.calldata n (n/32)) rho hs (hc.not.mpr hm)
    have g1 := RecognitionMovement.gasSteps_partial s e (fullFrame s.executionEnv.calldata n (n/32)) rho hs
    simpa only [loopState, if_pos rfl, ↓reduceIte, endState, endFrame, if_neg hm] using g0.trans g1

def gasSteps_accumulate (s : State) (e : Env s) (n : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hsize : s.executionEnv.calldata.size=n) :
    GasSteps (atState s 108 rho) (endState s n rho) :=
  (gasSteps_start s e n rho hs hn hsize).trans
    ((gasSteps_words s e n (n/32) rho hs hn (by omega)).trans (gasSteps_end s e n rho hs hn hsize))

#print axioms gasSteps_one
#print axioms gasSteps_accumulate
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLoop
