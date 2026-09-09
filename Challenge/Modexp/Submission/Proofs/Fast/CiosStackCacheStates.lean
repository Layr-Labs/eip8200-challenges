import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheReadOnly

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

/-- Physical execution state; the virtual memory is used only in the model. -/
def rowState (s : State) (pc : Nat) (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest head : List UInt256) : State :=
  let frame := rowFrame c r (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat (pa+32*n-32)) (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest
  framed { s with memory := c.memory } (UInt256.ofNat pc)
    (match head with | [] => frame | x::xs => (x::xs) ++ frame)

def outAt (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  rowState s 4620 c r pa pb n i dst ret rest []

def l1At (pc : Nat) (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  let p := cacheL1 c bi pa n j
  rowState s pc p.cache r pa pb n i dst ret rest
    [UInt256.ofNat (ptrAt (pa+32*n-32) j), p.carry, bi]

def l1BodyAt (pc : Nat) (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  let p := cacheL1 c bi pa n (j+1)
  rowState s pc p.cache r pa pb n i dst ret rest
    [UInt256.ofNat (ptrAt (pa+32*n-32) j), p.carry, bi]

def midAt (s : State) (c : CachedMemory) (r : ReadOnlyCache) (carry bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  rowState s 4919 c r pa pb n i dst ret rest [carry, bi]

def l2At (pc : Nat) (s : State) (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  let p := cacheL2 c mu c0 n k
  rowState s pc p.cache r pa pb n i dst ret rest [p.carry, mu, bi]

def tailAt (s : State) (c : CachedMemory) (r : ReadOnlyCache) (carry mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  rowState s 5206 c r pa pb n i dst ret rest [carry, mu, bi]

theorem write_cached_memory (c : CachedMemory) (k : Fin 3) (v : UInt256) :
    (c.write (addr k) v).memory = c.memory := by
  fin_cases k <;> simp [CachedMemory.write, addr]

theorem write_uncached (c : CachedMemory) (a : Nat) (v : UInt256) (ha : 8352 ≤ a) :
    c.write a v = { c with memory := WindowTableMemory.storeWord c.memory a v } := by
  simp only [CachedMemory.write, if_neg (show a ≠ 8256 by omega),
    if_neg (show a ≠ 8288 by omega), if_neg (show a ≠ 8320 by omega)]

theorem cursor_toNat (pa n j : Nat) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) (hj : j < n) :
    (UInt256.ofNat (ptrAt (pa+32*n-32) j)).toNat = pa+32*(n-1-j) := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    show (2 : Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 by decide,
    ptrAt_mod _ _ (by omega) (by omega)]
  omega

theorem cursor_next (pa n j : Nat) :
    CiosCached.negative32 + UInt256.ofNat (ptrAt (pa+32*n-32) j) =
      UInt256.ofNat (ptrAt (pa+32*n-32) (j+1)) := by
  rw [CiosCached.negative32, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
