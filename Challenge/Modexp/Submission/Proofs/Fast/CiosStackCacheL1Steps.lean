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

def l1BodyFor (k : Nat) : List Instr :=
  if h : k < 3 then cachedL1Body ⟨k,h⟩ else CiosCached.l1Body (UInt256.ofNat (8256+32*k))

def l1BodySize (k : Nat) : Nat := if k < 3 then 31 else 36

def l1StepFor (k : Nat) : List Instr := l1BodyFor k ++ CiosCachedL1.advanceProgram
def l1Last : List Instr := l1BodyFor 0 ++ CiosCachedL1.dropProgram

/-- Each first-loop body implements one recurrence step in the virtual model.
The operand bounds keep physical operand loads away from the cached T words. -/
theorem run_l1Body (pc : Nat) (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hj : j < n) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) :
    runInstructions (l1BodyFor (n-1-j)) (l1At pc s c r bi pa pb n i j dst ret rest) =
    some (l1BodyAt (pc+l1BodySize (n-1-j)) s c r bi pa pb n i j dst ret rest) := by
  let p := cacheL1 c bi pa n j
  let a := UInt256.ofNat (ptrAt (pa+32*n-32) j)
  let st : State := { s with memory := p.cache.memory }
  have ha : a.toNat = pa+32*(n-1-j) := cursor_toNat pa n j hpa hfit hj
  have hactive : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat a.toNat 32) = st.activeWords := by
    rw [ha]
    exact activeWords_fix s _ 32 (by decide) (by omega) hact
  have hra : MachineState.readWord p.cache.virtual (pa+32*(n-1-j)) =
      MachineState.readWord p.cache.memory a.toNat := by
    rw [ha]
    exact virtual_read_disjoint p.cache _ (by omega)
  change runInstructions (l1BodyFor (n-1-j))
      (rowState s pc p.cache r pa pb n i dst ret rest [a, p.carry, bi]) =
    some (rowState s (pc+l1BodySize (n-1-j))
      (p.cache.write (8256+32*(n-1-j))
        (macSum (MachineState.readWord p.cache.virtual (pa+32*(n-1-j))) bi
          (MachineState.readWord p.cache.virtual (8256+32*(n-1-j))) p.carry))
      r pa pb n i dst ret rest
      [a, macCarry (MachineState.readWord p.cache.virtual (pa+32*(n-1-j))) bi
        (MachineState.readWord p.cache.virtual (8256+32*(n-1-j))) p.carry, bi])
  rw [hra]
  by_cases hk : n-1-j < 3
  · let k : Fin 3 := ⟨n-1-j,hk⟩
    have hmem (v : UInt256) : (p.cache.write (8256+32*(n-1-j)) v).memory = p.cache.memory :=
      write_cached_memory p.cache k v
    have trace := run_cachedL1Body st (UInt256.ofNat pc) p.cache r
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
      (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret k a p.carry bi rest hcap hactive
    have hw : MachineState.readWord p.cache.virtual (8256+32*(n-1-j)) = word p.cache k :=
      (word_eq_read p.cache k).symm
    simp only [l1BodyFor, dif_pos hk, l1BodySize, if_pos hk]
    rw [hw]
    have hpc : advancePC 31 (UInt256.ofNat pc) = UInt256.ofNat (pc+31) := by
      simp only [advancePC, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]
    simpa only [rowState, st, framed, hpc, addr, k, hmem] using trace
  · let t := UInt256.ofNat (8256+32*(n-1-j))
    have ht : t.toNat = 8256+32*(n-1-j) := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hactiveT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) = st.activeWords := by
      rw [ht]
      exact activeWords_fix s _ 32 (by decide) (by omega) hact
    have hrt : MachineState.readWord p.cache.virtual (8256+32*(n-1-j)) =
        MachineState.readWord p.cache.memory t.toNat := by
      rw [ht]
      exact virtual_read_disjoint p.cache _ (by omega)
    have hw := write_uncached p.cache (8256+32*(n-1-j))
    have trace := run_memoryL1Body st (UInt256.ofNat pc) p.cache r
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
      (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret a t p.carry bi rest hcap hactive hactiveT
    simp only [l1BodyFor, dif_neg hk, l1BodySize, if_neg hk]
    rw [hrt, hw _ (by omega)]
    simpa only [rowState, st, framed, ht, storeWord, rowFrame, cacheTail,
      Challenge.EvmProof.Word.ofNat_add_mod] using trace

theorem run_l1Step (pc : Nat) (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hj : j < n) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) :
    runInstructions (l1StepFor (n-1-j)) (l1At pc s c r bi pa pb n i j dst ret rest) =
    some (l1At (pc+l1BodySize (n-1-j)+2) s c r bi pa pb n i (j+1) dst ret rest) := by
  let p := cacheL1 c bi pa n (j+1)
  have hb := run_l1Body pc s c r bi pa pb n i j dst ret rest hcap hact hn hj hpa hfit
  have ha := run_advance { s with memory := p.cache.memory }
    (UInt256.ofNat (pc+l1BodySize (n-1-j))) p.cache r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret
    (UInt256.ofNat (ptrAt (pa+32*n-32) j)) p.carry bi rest hcap
  have hall := runInstructions_append_some _ _ _ _ _ hb ha
  simpa only [l1StepFor, l1BodyAt, l1At, rowState, p, cursor_next,
    advancePC, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod] using hall

theorem run_l1Last (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hpos : 0 < n) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) :
    runInstructions l1Last (l1At 4862 s c r bi pa pb n i (n-1) dst ret rest) =
    some (midAt s (cacheL1 c bi pa n n).cache r (cacheL1 c bi pa n n).carry bi
      pa pb n i dst ret rest) := by
  have hn0 : n-1-(n-1) = 0 := by omega
  have hn1 : n-1+1 = n := by omega
  have hb := run_l1Body 4862 s c r bi pa pb n i (n-1) dst ret rest hcap hact hn (by omega) hpa hfit
  rw [hn0] at hb
  let p := cacheL1 c bi pa n n
  have hd := run_drop { s with memory := p.cache.memory } (UInt256.ofNat 4893) p.cache r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret
    (UInt256.ofNat (ptrAt (pa+32*n-32) (n-1))) p.carry bi rest hcap
  have hb' := hb
  simp only [l1BodyAt, hn1] at hb'
  have hall := runInstructions_append_some _ _ _ _ _ hb' hd
  simpa only [l1Last, midAt, rowState, p, advancePC, Challenge.EvmProof.Word.succ_ofNat_mod] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_l1Step
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_l1Last
