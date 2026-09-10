import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemoryMac
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheStates

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 600000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel
open WindowTableMemory

def l2BodyFor (k : Nat) : List Instr :=
  if h : k < 2 then cachedL2Body ⟨k,h⟩
  else if k = 2 then compactPartialL2Body (UInt256.ofNat 64) (UInt256.ofNat 8352)
  else compactMemoryL2Body (UInt256.ofNat (32*k))
    (UInt256.ofNat (8256+32*k)) (UInt256.ofNat (8256+32*(k+1)))

def l2BodySize (k : Nat) : Nat := if k < 2 then 30 else if k = 2 then 34 else 37

theorem sourceWord_eq_read (r : ReadOnlyCache) (c : CachedMemory) (n : Nat)
    (h : r.Valid c.virtual n) (k : Fin 2) :
    sourceWord r k = MachineState.readWord c.virtual (32*k.val) := by
  fin_cases k
  · exact h.z0
  · exact h.m32

/-- Second-loop steps preserve the cached/physical representation, including
the transition from cached source words to an uncached destination word. -/
theorem run_l2Step (pc : Nat) (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hk : k+1 < n) (hread : r.Valid c.virtual n) :
    runInstructions (l2BodyFor (n-2-k)) (l2At pc s c r bi mu c0 pa pb n i k dst ret rest) =
    some (l2At (pc+l2BodySize (n-2-k)) s c r bi mu c0 pa pb n i (k+1) dst ret rest) := by
  let p := cacheL2 c mu c0 n k
  let st : State := { s with memory := p.cache.memory }
  have hro : r.Valid p.cache.virtual n := hread.cacheL2 r c mu c0 n k hn
  have hn1 : n-1-k = (n-2-k)+1 := by omega
  change runInstructions (l2BodyFor (n-2-k))
      (rowState s pc p.cache r pa pb n i dst ret rest [p.carry, mu, bi]) =
    some (rowState s (pc+l2BodySize (n-2-k))
      (p.cache.write (8256+32*(n-1-k))
        (macSum (MachineState.readWord p.cache.virtual (32*(n-2-k))) mu
          (MachineState.readWord p.cache.virtual (8256+32*(n-2-k))) p.carry))
      r pa pb n i dst ret rest
      [macCarry (MachineState.readWord p.cache.virtual (32*(n-2-k))) mu
        (MachineState.readWord p.cache.virtual (8256+32*(n-2-k))) p.carry, mu, bi])
  by_cases hsmall : n-2-k < 2
  · let q : Fin 2 := ⟨n-2-k,hsmall⟩
    let qr : Fin 3 := ⟨q.val,by omega⟩
    let qw : Fin 3 := ⟨q.val+1,by omega⟩
    have hx : MachineState.readWord p.cache.virtual (32*(n-2-k)) = sourceWord r q :=
      (sourceWord_eq_read r p.cache n hro q).symm
    have ht : MachineState.readWord p.cache.virtual (8256+32*(n-2-k)) = word p.cache qr :=
      (word_eq_read p.cache qr).symm
    have hw (v : UInt256) : (p.cache.write (8256+32*((n-2-k)+1)) v).memory = p.cache.memory :=
      write_cached_memory p.cache qw v
    have trace := run_cachedL2Body st (UInt256.ofNat pc) p.cache r
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
      (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret q p.carry mu bi rest hcap
    simp only [l2BodyFor, dif_pos hsmall, l2BodySize, if_pos hsmall]
    rw [hx, ht, hn1]
    have hpc : advancePC 30 (UInt256.ofNat pc) = UInt256.ofNat (pc+30) := by
      simp only [advancePC, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]
    simpa only [rowState, st, framed, hpc, addr, q, qr, qw, hw] using trace
  · by_cases heq : n-2-k = 2
    · have hx : MachineState.readWord p.cache.virtual (32*(n-2-k)) =
          MachineState.readWord p.cache.memory 64 := by
        rw [heq]
        exact virtual_read_disjoint p.cache _ (by omega)
      have ht : MachineState.readWord p.cache.virtual (8256+32*(n-2-k)) = p.cache.t2 := by
        rw [heq]
        exact virtual_t2 p.cache
      have hw := write_uncached p.cache 8352
      have trace := run_compactPartialL2Body st (UInt256.ofNat pc) p.cache r
        (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
        (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret
        (UInt256.ofNat 64) (UInt256.ofNat 8352) p.carry mu bi rest hcap
        (activeWords_fix s 64 32 (by decide) (by omega) hact)
        (activeWords_fix s 8352 32 (by decide) (by omega) hact)
      simp only [l2BodyFor, dif_neg hsmall, if_pos heq, l2BodySize, if_neg hsmall]
      rw [hx, ht, hn1, heq]
      change runInstructions (compactPartialL2Body (UInt256.ofNat 64) (UInt256.ofNat 8352)) _ =
        some (rowState s (pc+34) (p.cache.write 8352
          (macSum (MachineState.readWord p.cache.memory 64) mu p.cache.t2 p.carry))
          r pa pb n i dst ret rest
          [macCarry (MachineState.readWord p.cache.memory 64) mu p.cache.t2 p.carry, mu, bi])
      rw [hw _ (by decide)]
      simpa only [rowState, st, framed, storeWord, rowFrame, cacheTail,
        show (UInt256.ofNat 64).toNat = 64 by decide,
        show (UInt256.ofNat 8352).toNat = 8352 by decide,
        Challenge.EvmProof.Word.ofNat_add_mod] using trace
    · let x := UInt256.ofNat (32*(n-2-k))
      let tl := UInt256.ofNat (8256+32*(n-2-k))
      let ts := UInt256.ofNat (8256+32*((n-2-k)+1))
      have hxnat : x.toNat = 32*(n-2-k) := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have htlnat : tl.toNat = 8256+32*(n-2-k) := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have htsnat : ts.toNat = 8256+32*((n-2-k)+1) := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hx : MachineState.readWord p.cache.virtual (32*(n-2-k)) =
          MachineState.readWord p.cache.memory x.toNat := by
        rw [hxnat]
        exact virtual_read_disjoint p.cache _ (by omega)
      have ht : MachineState.readWord p.cache.virtual (8256+32*(n-2-k)) =
          MachineState.readWord p.cache.memory tl.toNat := by
        rw [htlnat]
        exact virtual_read_disjoint p.cache _ (by omega)
      have hw := write_uncached p.cache (8256+32*((n-2-k)+1))
      have trace := run_compactMemoryL2Body st (UInt256.ofNat pc) p.cache r
        (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
        (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret x tl ts p.carry mu bi rest hcap
        (by rw [hxnat]; exact activeWords_fix s _ 32 (by decide) (by omega) hact)
        (by rw [htlnat]; exact activeWords_fix s _ 32 (by decide) (by omega) hact)
        (by rw [htsnat]; exact activeWords_fix s _ 32 (by decide) (by omega) hact)
      simp only [l2BodyFor, dif_neg hsmall, if_neg heq, l2BodySize, if_neg hsmall]
      rw [hx, ht, hn1, hw _ (by omega)]
      simpa only [rowState, st, framed, htsnat, storeWord, rowFrame, cacheTail,
        Challenge.EvmProof.Word.ofNat_add_mod] using trace

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_l2Step
