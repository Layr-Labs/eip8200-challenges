import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheStates
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms

set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

set_option linter.unusedSimpArgs false in
theorem run_outWords (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pbi.toNat 32) = s.activeWords) :
    runInstructions CiosStackCachePrograms.out
      (framed s (UInt256.ofNat 4620) (rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4625)
      ([paEnd, UInt256.ofNat 0, MachineState.readWord s.memory pbi.toNat] ++
        rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := by decide
  simp [CiosStackCachePrograms.out, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, h16, h17, h18, h19, hz,
    State.activeWordsAfterUInt256, hactive, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_out (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 8192) (hi : i < n) :
    runInstructions CiosStackCachePrograms.out (outAt s c r pa pb n i dst ret rest) =
    some (l1At 4625 s c r (rowBi c.virtual pb n i) pa pb n i 0 dst ret rest) := by
  have hp := cursor_toNat pb n i hpb hfit hi
  have hr : rowBi c.virtual pb n i =
      MachineState.readWord c.memory (UInt256.ofNat (ptrAt (pb+32*n-32) i)).toNat := by
    rw [hp]
    exact virtual_read_disjoint c _ (by omega)
  have trace := run_outWords { s with memory := c.memory } c r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest hcap
    (by rw [hp]; exact activeWords_fix s _ 32 (by decide) (by omega) hact)
  simpa only [outAt, l1At, rowState, cacheL1, ptrAt_zero, hr, List.nil_append, framed] using trace

def dispatchFor (target : Nat) : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .push 2 (UInt256.ofNat target), .op .JUMPI]

set_option linter.unusedSimpArgs false in
theorem run_dispatch (s : State) (pc target : Nat) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret a b d : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (ht : target < 2^256)
    (hjump : Decode.isValidJumpDest s.executionEnv.code target = true) :
    runInstructions (dispatchFor target)
      (framed s (UInt256.ofNat pc) ([a,b,d] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat (if UInt256.isTrue flag then target else pc+5))
      ([a,b,d] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have ht' : target < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := ht
  by_cases hf : UInt256.isTrue flag <;>
    simp [dispatchFor, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      framed, rowFrame, cacheTail, h19, h20, h21, hf, hjump,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht', Nat.add_assoc]

theorem dispatch_l1 : CiosStackCachePrograms.l1Dispatch = dispatchFor 4782 := rfl
theorem dispatch_l2 : CiosStackCachePrograms.l2Dispatch = dispatchFor 5110 := rfl

theorem run_join (s : State) (pc : Nat) (stack : List UInt256) (hcap : stack.length < 1024) :
    runInstructions [.op .JUMPDEST] (framed s (UInt256.ofNat pc) stack) =
    some (framed s (UInt256.ofNat (pc+1)) stack) := by
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, hcap,
    Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_out
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_dispatch
