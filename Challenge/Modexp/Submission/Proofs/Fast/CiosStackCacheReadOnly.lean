import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheFrames
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit

set_option warningAsError true
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit

def ReadOnlyCache.capture (mem : ByteArray) (n : Nat) : ReadOnlyCache :=
  ⟨MachineState.readWord mem (32*n-32), MachineState.readWord mem 0,
    MachineState.readWord mem 32, MachineState.readWord mem 9376, MachineState.readWord mem 9440⟩

structure ReadOnlyCache.Valid (r : ReadOnlyCache) (mem : ByteArray) (n : Nat) : Prop where
  m0 : r.m0 = MachineState.readWord mem (32*n-32)
  z0 : r.z0 = MachineState.readWord mem 0
  m32 : r.m32 = MachineState.readWord mem 32
  inv : r.inv = MachineState.readWord mem 9376
  tl : r.tl = MachineState.readWord mem 9440

theorem ReadOnlyCache.capture_valid (mem : ByteArray) (n : Nat) :
    (ReadOnlyCache.capture mem n).Valid mem n := by
  constructor <;> rfl

theorem ReadOnlyCache.Valid.transfer (r : ReadOnlyCache) (mem mem' : ByteArray) (n : Nat)
    (h : r.Valid mem n) (hn : n ≤ 32)
    (hr : ∀ a, a+32 ≤ 8192 ∨ 9280 ≤ a → MachineState.readWord mem' a = MachineState.readWord mem a) :
    r.Valid mem' n := by
  constructor
  · exact h.m0.trans (hr (32*n-32) (by omega)).symm
  · exact h.z0.trans (hr 0 (by omega)).symm
  · exact h.m32.trans (hr 32 (by omega)).symm
  · exact h.inv.trans (hr 9376 (by omega)).symm
  · exact h.tl.trans (hr 9440 (by omega)).symm

theorem ReadOnlyCache.Valid.cacheL1 (r : ReadOnlyCache) (c : CachedMemory)
    (bi : UInt256) (pa n j : Nat) (h : r.Valid c.virtual n) (hn : n ≤ 32) :
    r.Valid (CiosStackCacheModel.cacheL1 c bi pa n j).cache.virtual n := by
  apply h.transfer r c.virtual _ n hn
  intro a ha
  change MachineState.readWord (CiosStackCacheModel.cacheL1 c bi pa n j).virtual.memory a = _
  rw [virtual_cacheL1]
  exact readWord_l1Step c.virtual bi pa n a j hn ha

theorem ReadOnlyCache.Valid.cacheL2 (r : ReadOnlyCache) (c : CachedMemory)
    (mu c0 : UInt256) (n k : Nat) (h : r.Valid c.virtual n) (hn : n ≤ 32) :
    r.Valid (CiosStackCacheModel.cacheL2 c mu c0 n k).cache.virtual n := by
  apply h.transfer r c.virtual _ n hn
  intro a ha
  change MachineState.readWord (CiosStackCacheModel.cacheL2 c mu c0 n k).virtual.memory a = _
  rw [virtual_cacheL2]
  exact readWord_l2Step c.virtual mu c0 n a k hn ha

theorem ReadOnlyCache.Valid.cacheMid (r : ReadOnlyCache) (c : CachedMemory)
    (carry : UInt256) (n : Nat) (h : r.Valid c.virtual n) (hn : n ≤ 32) :
    r.Valid (CiosStackCacheModel.cacheMid c carry).virtual n := by
  apply h.transfer r c.virtual _ n hn
  intro a ha
  rw [virtual_cacheMid]
  exact readWord_midMem c.virtual carry a ha

theorem ReadOnlyCache.Valid.cacheTail (r : ReadOnlyCache) (c : CachedMemory)
    (carry : UInt256) (n : Nat) (h : r.Valid c.virtual n) (hn : n ≤ 32) :
    r.Valid (CiosStackCacheModel.cacheTail c carry).virtual n := by
  apply h.transfer r c.virtual _ n hn
  intro a ha
  rw [virtual_cacheTail]
  exact readWord_tailMem c.virtual carry a ha

theorem ReadOnlyCache.Valid.cacheRows (r : ReadOnlyCache) (c : CachedMemory)
    (pa pb n i : Nat) (h : r.Valid c.virtual n) (hn : n ≤ 32) :
    r.Valid (CiosStackCacheModel.cacheRows c pa pb n i).virtual n := by
  apply h.transfer r c.virtual _ n hn
  intro a ha
  rw [virtual_cacheRows]
  exact readWord_rowsMem c.virtual pa pb n a hn ha i

theorem ReadOnlyCache.capture_initial (s : State) (mem : ByteArray) (n : Nat)
    (hn : 3 ≤ n) (hn32 : n ≤ 32) :
    (ReadOnlyCache.capture mem n).Valid (initial s mem n).virtual n := by
  rw [virtual_initial s mem n hn]
  apply (ReadOnlyCache.capture_valid mem n).transfer _ mem _ n hn32
  intro a ha
  exact readWord_mpZeroed s mem n a hn32 ha

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.ReadOnlyCache.Valid.cacheRows
