import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryLoop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StaggerPersistentLoopRaw StaggerPersistentLoopInduction

def run_until (input : ByteArray) (states : Nat → State) (hashes : Nat → Compression.HashState)
    (rho : List UInt256) (hsize : input.size<2^64) (hstack : rho.length≤880)
    (target : Nat) (htarget : target<DriverTrace.blockCount input)
    (hambient : ∀ i, i≤target → Ambient input (states i))
    (hblock : ∀ i, i<target →
      GasSteps (loopState input (states i) (hashes i) i (DriverTrace.blockCount input) rho)
        (postState input (states (i+1)) (hashes (i+1)) i (DriverTrace.blockCount input) rho)) :
    GasSteps (loopState input (states 0) (hashes 0) 0 (DriverTrace.blockCount input) rho)
      (loopState input (states target) (hashes target) target (DriverTrace.blockCount input) rho) := by
  let count:=DriverTrace.blockCount input
  have hbound : count*64<2^256 := LoopCompletionControl.padded_bound input hsize
  let I : Nat → State := fun i=>loopState input (states i) (hashes i) i count rho
  have hb : ∀ i, i<target → GasSteps (I i) (I (i+1)) := by
    intro i hi
    have hic : i<count := by omega
    have hn : i+1<count := by omega
    have a:=hambient (i+1) (by omega)
    have hfit : (states (i+1)).executionEnv.calldata.size<2^256 := by
      rw [a.calldata]
      have : (2:Nat)^64<2^256 := by decide
      omega
    have ho : (nextOffset (offsetWord i)).toNat=(i+1)*64 := by
      rw [next_offset i count hic hbound]
      change ((i+1)*64)%2^256=(i+1)*64
      exact Nat.mod_eq_of_lt (by omega)
    have hl:=LoopCompletionControl.limit_toNat input hsize
    by_cases hh : input.size=(i+1)*64
    · have gp:=StaggerPersistentLoopSites.gasSteps_pad (states (i+1)) (hashes (i+1))
        (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running
        (by rw [hl,ho];exact LoopCompletionControl.pad_bound input i hh) hfit
        (by rw [a.calldata,ho];exact hh) a.code a.fork a.notPrecompile
      rw [next_offset i count hic hbound] at gp
      simpa only [I,loopState,postState,LoopCompletionControl.blockPC,if_pos hh] using (hblock i hi).trans gp
    · have gp:=StaggerPersistentLoopSites.gasSteps_continue (states (i+1)) (hashes (i+1))
        (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running
        (by rw [hl,ho];exact LoopCompletionControl.continue_lt input i hn hh)
        a.code a.fork a.notPrecompile
      rw [next_offset i count hic hbound] at gp
      simpa only [I,loopState,postState,LoopCompletionControl.blockPC,if_neg hh] using (hblock i hi).trans gp
  exact GasSteps.iterateBounded (I:=I) target hb
#print axioms run_until
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryLoop
