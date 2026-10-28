import Challenge.Ripemd160.Submission.Local20261028.ColdLoop
import Challenge.Ripemd160.Submission.Local20261028.PadContract
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.AlignedLoop
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerPersistentLoopSites

def entry (states : Nat → State) (hashes : Nat → Compression.HashState) (count i : Nat)
    (rho : List UInt256) : State :=
  {states i with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (hashes i) (UInt256.ofNat (1056+64*i)) (UInt256.ofNat (64*(count-i))) rho}
def post (states : Nat → State) (hashes : Nat → Compression.HashState) (count i : Nat)
    (rho : List UInt256) : State :=
  {states (i+1) with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 (hashes i).h2 :: StaggerPersistentFrame.frame (hashes (i+1)) (UInt256.ofNat (1056+64*i)) (UInt256.ofNat (64*(count-i))) rho}
def padEntry (states : Nat → State) (hashes : Nat → Compression.HashState) (count : Nat)
    (rho : List UInt256) : State :=
  {states count with pc := UInt256.ofNat 64, stack := StaggerPersistentFrame.frame (hashes count) (UInt256.ofNat (1056+64*(count-1))) (Word.ofUInt32 (hashes (count-1)).h2) rho}

def run_data (states : Nat → State) (hashes : Nat → Compression.HashState)
    (count : Nat) (hc : 0 < count) (hb : count ≤ 3) (rho : List UInt256) (hs : rho.length ≤ 880)
    (env : ∀ i, i ≤ count → FirstEntry.Env (states i))
    (block : ∀ i, i < count → GasSteps (entry states hashes count i rho) (post states hashes count i rho)) :
    GasSteps (entry states hashes count 0 rho) (padEntry states hashes count rho) := by
  let I (i : Nat) := if i < count then entry states hashes count i rho else padEntry states hashes i rho
  have step : ∀ i, i < count → GasSteps (I i) (I (i+1)) := by
    intro i hi
    have e := env (i+1) (by omega)
    have gb := block i hi
    have hoff : LoopRaw.nextOffset (UInt256.ofNat (1056+64*i)) = UInt256.ofNat (1056+64*(i+1)) := by
      unfold LoopRaw.nextOffset; rw [Word.ofNat_add_mod]; congr 1
    rw [show I i = entry states hashes count i rho by simp only [I,if_pos hi]]
    by_cases h3 : count-i=3
    · have hn : i+1 < count := by omega
      have cont : 64*(count-i)=192 := by omega
      have next : 64*(count-(i+1))=128 := by omega
      have gd := gasSteps_dispatch (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (UInt256.ofNat 192) (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running
        (StaggerPersistentEntrySites.valid_stub192 _ e.code) e.code e.fork e.noPrecompile
      have gs := gasSteps_stub192 (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running e.code e.fork e.noPrecompile
      rw [hoff] at gs
      simp only [post,cont] at gb
      exact (gb.trans (gd.trans gs)).cast rfl (by simp only [I,if_pos hn,entry,next])
    by_cases h2 : count-i=2
    · have hn : i+1 < count := by omega
      have cont : 64*(count-i)=128 := by omega
      have next : 64*(count-(i+1))=64 := by omega
      have gd := gasSteps_dispatch (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (UInt256.ofNat 128) (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running
        (StaggerPersistentEntrySites.valid_stub128 _ e.code) e.code e.fork e.noPrecompile
      have gs := gasSteps_stub128 (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running e.code e.fork e.noPrecompile
      have ga := gasSteps_advance (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (UInt256.ofNat 64) (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running e.code e.fork e.noPrecompile
      rw [hoff] at ga
      simp only [post,cont] at gb
      exact (gb.trans (gd.trans (gs.trans ga))).cast rfl (by simp only [I,if_pos hn,entry,next])
    · have hn : ¬ i+1 < count := by omega
      have cont : 64*(count-i)=64 := by omega
      have gd := gasSteps_dispatch (states (i+1)) (hashes (i+1)) (UInt256.ofNat (1056+64*i))
        (UInt256.ofNat 64) (Word.ofUInt32 (hashes i).h2) rho (by omega) e.running
        (StaggerPersistentEntrySites.valid_pad _ e.code) e.code e.fork e.noPrecompile
      simp only [post,cont] at gb
      exact (gb.trans gd).cast rfl (by simp only [I,if_neg hn,padEntry,Nat.add_sub_cancel])
  have g := GasSteps.iterateBounded (I := I) count step
  exact g.cast (by simp only [I,if_pos hc]) (by simp only [I,if_neg (Nat.lt_irrefl count)])

noncomputable def gasSteps_data (input : ByteArray) (n : Fin 3)
    (_hsize : input.size = 64*(n.val+1)) (rho : List UInt256) (hs : rho.length ≤ 878) :
    GasSteps (entry (Iteration.states input) (Iteration.hashes input) (n.val+1) 0 (NormalPrepare.masks rho))
      (padEntry (Iteration.states input) (Iteration.hashes input) (n.val+1) (NormalPrepare.masks rho)) := by
  have e (i : Nat) : FirstEntry.Env (Iteration.states input i) := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_code input
    · change (Iteration.states input i).executionEnv.fork = .Osaka
      rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_fork input
    · rw [NormalIteration.halt]; exact PadSkipEntry.entryState_halt input
    · rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_noPrecompile input
  apply run_data _ _ _ (by omega) (by have := n.isLt; omega) _ (by simp [NormalPrepare.masks]; omega) (fun i _ => e i)
  intro i hi
  have hb : 1056+64*i+64 < 2^256 := by have := n.isLt; omega
  have g0 := gasSteps_join (Iteration.states input i)
    (StaggerPersistentFrame.frame (Iteration.hashes input i) (UInt256.ofNat (1056+64*i)) (UInt256.ofNat (64*((n.val+1)-i))) (NormalPrepare.masks rho))
    (by simp [StaggerPersistentFrame.frame,NormalPrepare.masks]; omega)
    (e i).running (e i).code (e i).fork (e i).noPrecompile
  have g1 := NormalIteration.gasSteps_block (Iteration.entry input) 1056 i StackRunBridge.initialHashState
    (UInt256.ofNat (64*((n.val+1)-i))) rho (by omega) (e 0).running (by decide) hb (e 0).code (e 0).fork (e 0).noPrecompile
  exact g0.trans g1
#print axioms run_data
#print axioms gasSteps_data
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.AlignedLoop
