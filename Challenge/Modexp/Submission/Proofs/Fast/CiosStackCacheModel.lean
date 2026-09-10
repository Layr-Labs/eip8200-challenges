import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

structure CachedMacState where
  cache : CachedMemory
  carry : UInt256

def CachedMacState.virtual (c : CachedMacState) : MacState :=
  ⟨c.cache.virtual, c.carry⟩

theorem accumulator_address (k : Nat) :
    8256+32*k = 8256 ∨ 8256+32*k = 8288 ∨ 8256+32*k = 8320 ∨
    8256+32*k+32 ≤ 8256 ∨ 8352 ≤ 8256+32*k := by omega

def cacheL1 (c : CachedMemory) (bi : UInt256) (pa n : Nat) : Nat → CachedMacState
  | 0 => ⟨c, UInt256.ofNat 0⟩
  | j+1 =>
      let p := cacheL1 c bi pa n j
      let x := MachineState.readWord p.cache.virtual (pa+32*(n-1-j))
      let t := MachineState.readWord p.cache.virtual (8256+32*(n-1-j))
      ⟨p.cache.write (8256+32*(n-1-j)) (macSum x bi t p.carry),
        macCarry x bi t p.carry⟩

theorem virtual_cacheL1 (c : CachedMemory) (bi : UInt256) (pa n j : Nat) :
    (cacheL1 c bi pa n j).virtual = l1Step c.virtual bi pa n j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hm := congrArg MacState.memory ih
      have hc := congrArg MacState.carry ih
      simp only [CachedMacState.virtual] at hm hc
      simp only [cacheL1, CachedMacState.virtual, l1Step,
        virtual_write _ _ _ (accumulator_address (n-1-j)), hm, hc, storeWord]

def cacheMid (c : CachedMemory) (carry : UInt256) : CachedMemory :=
  (c.write 8224 (MachineState.readWord c.virtual 8224 + carry)).write 8192
    (UInt256.lt (MachineState.readWord c.virtual 8224 + carry) carry)

theorem virtual_cacheMid (c : CachedMemory) (carry : UInt256) :
    (cacheMid c carry).virtual = midMem c.virtual carry := by
  simp only [cacheMid, virtual_write _ 8192 _ (by omega),
    virtual_write _ 8224 _ (by omega), midMem, midMem1, storeWord]

def cacheL2 (c : CachedMemory) (mu c0 : UInt256) (n : Nat) : Nat → CachedMacState
  | 0 => ⟨c, c0⟩
  | k+1 =>
      let p := cacheL2 c mu c0 n k
      let x := MachineState.readWord p.cache.virtual (32*(n-2-k))
      let t := MachineState.readWord p.cache.virtual (8256+32*(n-2-k))
      ⟨p.cache.write (8256+32*(n-1-k)) (macSum x mu t p.carry),
        macCarry x mu t p.carry⟩

theorem virtual_cacheL2 (c : CachedMemory) (mu c0 : UInt256) (n k : Nat) :
    (cacheL2 c mu c0 n k).virtual = l2Step c.virtual mu c0 n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hm := congrArg MacState.memory ih
      have hc := congrArg MacState.carry ih
      simp only [CachedMacState.virtual] at hm hc
      simp only [cacheL2, CachedMacState.virtual, l2Step,
        virtual_write _ _ _ (accumulator_address (n-1-k)), hm, hc, storeWord]

def cacheTail (c : CachedMemory) (carry : UInt256) : CachedMemory :=
  let c1 := c.write 8256 (MachineState.readWord c.virtual 8224 + carry)
  c1.write 8224 (MachineState.readWord c1.virtual 8192 +
    UInt256.lt (MachineState.readWord c.virtual 8224 + carry) carry)

theorem virtual_cacheTail (c : CachedMemory) (carry : UInt256) :
    (cacheTail c carry).virtual = tailMem c.virtual carry := by
  simp only [cacheTail, virtual_write _ 8256 _ (by omega),
    virtual_write _ 8224 _ (by omega), tailMem, tailMem1, storeWord]

def cacheRowL1 (c : CachedMemory) (pa pb n i : Nat) : CachedMacState :=
  cacheL1 c (rowBi c.virtual pb n i) pa n n

def cacheRowMid (c : CachedMemory) (pa pb n i : Nat) : CachedMemory :=
  cacheMid (cacheRowL1 c pa pb n i).cache (cacheRowL1 c pa pb n i).carry

def cacheRowL2 (c : CachedMemory) (pa pb n i : Nat) : CachedMacState :=
  cacheL2 (cacheRowMid c pa pb n i)
    (rowMu (cacheRowL1 c pa pb n i).cache.virtual n)
    (rowC0 (cacheRowL1 c pa pb n i).cache.virtual n) n (n-1)

def cacheRow (c : CachedMemory) (pa pb n i : Nat) : CachedMemory :=
  cacheTail (cacheRowL2 c pa pb n i).cache (cacheRowL2 c pa pb n i).carry

theorem virtual_cacheRowL1 (c : CachedMemory) (pa pb n i : Nat) :
    (cacheRowL1 c pa pb n i).virtual = rowL1 c.virtual pa pb n i :=
  virtual_cacheL1 _ _ _ _ _

theorem virtual_cacheRowMid (c : CachedMemory) (pa pb n i : Nat) :
    (cacheRowMid c pa pb n i).virtual = rowMid c.virtual pa pb n i := by
  have hm := congrArg MacState.memory (virtual_cacheRowL1 c pa pb n i)
  have hc := congrArg MacState.carry (virtual_cacheRowL1 c pa pb n i)
  simp only [CachedMacState.virtual] at hm hc
  simp only [cacheRowMid, virtual_cacheMid, rowMid, hm, hc]

theorem virtual_cacheRowL2 (c : CachedMemory) (pa pb n i : Nat) :
    (cacheRowL2 c pa pb n i).virtual = rowL2 c.virtual pa pb n i := by
  have hm := congrArg MacState.memory (virtual_cacheRowL1 c pa pb n i)
  simp only [CachedMacState.virtual] at hm
  simpa only [cacheRowL2, virtual_cacheRowMid, rowL2, hm] using
    virtual_cacheL2 (cacheRowMid c pa pb n i)
      (rowMu (cacheRowL1 c pa pb n i).cache.virtual n)
      (rowC0 (cacheRowL1 c pa pb n i).cache.virtual n) n (n-1)

theorem virtual_cacheRow (c : CachedMemory) (pa pb n i : Nat) :
    (cacheRow c pa pb n i).virtual = rowMem c.virtual pa pb n i := by
  have hm := congrArg MacState.memory (virtual_cacheRowL2 c pa pb n i)
  have hc := congrArg MacState.carry (virtual_cacheRowL2 c pa pb n i)
  simp only [CachedMacState.virtual] at hm hc
  simp only [cacheRow, virtual_cacheTail, rowMem, hm, hc]

def cacheRows (c : CachedMemory) (pa pb n : Nat) : Nat → CachedMemory
  | 0 => c
  | i+1 => cacheRow (cacheRows c pa pb n i) pa pb n i

/-- Flushing the cache after any number of complete CIOS rows gives the exact
original memory model, including its scratch words and all untouched bytes. -/
theorem virtual_cacheRows (c : CachedMemory) (pa pb n i : Nat) :
    (cacheRows c pa pb n i).virtual = rowsMem c.virtual pa pb n i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [cacheRows, rowsMem, virtual_cacheRow, ih]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel.virtual_cacheRows
