import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentLoopSites
import Challenge.Ripemd160.Submission.Local20261028.ColdIteration
import Challenge.Ripemd160.Submission.Local20261028.FirstEntry
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Loop
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerPersistentLoopSites

def entry (states : Nat → State) (hashes : Nat → Compression.HashState) (i : Nat)
    (rho : List UInt256) : State :=
  {states i with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (hashes i) (UInt256.ofNat (1056+64*i)) (UInt256.ofNat 222) rho}
def post (states : Nat → State) (hashes : Nat → Compression.HashState) (i : Nat)
    (rho : List UInt256) : State :=
  {states (i+1) with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 (hashes i).h2 :: StaggerPersistentFrame.frame (hashes (i+1)) (UInt256.ofNat (1056+64*i)) (UInt256.ofNat 222) rho}
def result (states : Nat → State) (hashes : Nat → Compression.HashState) (count : Nat)
    (rho : List UInt256) : State :=
  {states count with pc := UInt256.ofNat 8397, stack := StaggerPersistentFrame.frame (hashes count) (UInt256.ofNat (1056+64*(count-1))) (Word.ofUInt32 (hashes (count-1)).h2) rho}

def run_blocks (states : Nat → State) (hashes : Nat → Compression.HashState)
    (count : Nat) (hc : 0 < count) (rho : List UInt256) (hs : rho.length ≤ 880)
    (env : ∀ i, i ≤ count → FirstEntry.Env (states i))
    (last : ∀ i, i < count →
      ((UInt256.ofNat (32*(states (i+1)).activeWords.toNat)).toNat <
       (UInt256.ofNat (1056+64*i)+UInt256.ofNat 128).toNat ↔ i+1=count))
    (block : ∀ i, i < count → GasSteps (entry states hashes i rho) (post states hashes i rho)) :
    GasSteps (entry states hashes 0 rho) (result states hashes count rho) := by
  let I (i : Nat) := if i < count then entry states hashes i rho else result states hashes i rho
  have step : ∀ i, i < count → GasSteps (I i) (I (i+1)) := by
    intro i hi
    have e := env (i+1) (by omega)
    have gb := block i hi
    have gd := gasSteps_dispatch (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
      (UInt256.ofNat 222) (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running
      (valid_gl _ e.code) e.code e.fork e.noPrecompile
    have gbd := gb.trans gd
    have h0 : I i = entry states hashes i rho := by simp only [I,if_pos hi]
    rw [h0]
    by_cases hn : i+1 < count
    · have hge : ¬ (UInt256.ofNat (32*(states (i+1)).activeWords.toNat)).toNat <
          (UInt256.ofNat (1056+64*i)+UInt256.ofNat 128).toNat := by
        intro h; have := (last i hi).mp h; omega
      have gt := gasSteps_glStay (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running hge e.code e.fork e.noPrecompile
      have hoff : LoopRaw.nextOffset (UInt256.ofNat (1056+64*i)) = UInt256.ofNat (1056+64*(i+1)) := by
        unfold LoopRaw.nextOffset
        rw [Word.ofNat_add_mod]
        congr 1
      rw [hoff] at gt
      exact (gbd.trans gt).cast rfl (by simp only [I,if_pos hn,entry])
    · have he : i+1=count := by omega
      have gt := gasSteps_glExit (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running ((last i hi).mpr he)
        e.code e.fork e.noPrecompile
      exact (gbd.trans gt).cast rfl (by simp only [I,if_neg hn,result,Nat.add_sub_cancel,LoopRaw.outPC])
  have g := GasSteps.iterateBounded (I := I) count step
  exact g.cast (by simp only [I,if_pos hc]) (by simp only [I,if_neg (Nat.lt_irrefl count)])

noncomputable def gasSteps (input : ByteArray) (hfit : CalldataFits input)
    (hcold : ¬ (input.size % 64=0 ∧ input.size<256))
    (rho : List UInt256) (hs : rho.length ≤ 878) :
    GasSteps (entry (Iteration.states input) (Iteration.hashes input) 0 (NormalPrepare.masks rho))
      (result (Iteration.states input) (Iteration.hashes input) (DriverTrace.blockCount input) (NormalPrepare.masks rho)) := by
  have e (i : Nat) : FirstEntry.Env (Iteration.states input i) := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_code input
    · change (Iteration.states input i).executionEnv.fork = .Osaka
      rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_fork input
    · rw [NormalIteration.halt]; exact PadSkipEntry.entryState_halt input
    · rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_noPrecompile input
  apply run_blocks _ _ _ (DriverTrace.blockCount_pos input) _ (by simp [NormalPrepare.masks]; omega)
    (fun i _ => e i) (fun i hi => Iteration.last input hfit hcold i hi)
  intro i hi
  have hb : 1056+64*i+64 < 2^256 := by
    have := Padding.paddedLength_lt input.size
    have := DriverTrace.paddedLength_eq_blockCount input
    unfold CalldataFits at hfit
    omega
  have g0 := gasSteps_join (Iteration.states input i)
    (StaggerPersistentFrame.frame (Iteration.hashes input i) (UInt256.ofNat (1056+64*i)) (UInt256.ofNat 222) (NormalPrepare.masks rho))
    (by simp [StaggerPersistentFrame.frame,NormalPrepare.masks]; omega)
    (e i).running (e i).code (e i).fork (e i).noPrecompile
  have g1 := NormalIteration.gasSteps_block (Iteration.entry input) 1056 i StackRunBridge.initialHashState
    (UInt256.ofNat 222) rho (by omega) (e 0).running (by decide) hb (e 0).code (e 0).fork (e 0).noPrecompile
  exact g0.trans g1
#print axioms run_blocks
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Loop
