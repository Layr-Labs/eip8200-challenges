import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheInitialMemory
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquarePreserves

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstModel
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel SquareResult CarryRowModel
open CiosCachedMidMemory
open TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves
open R8ZeroFirstRow

/-- The first-row product equals the zero-initialized model after materializing
its initially zero carry. The incoming product scratch need not be zero. -/
theorem product_lift (s : State) (mem : ByteArray) (hscr : R8RowZeroExact.ScratchZero mem) :
    liftMac (firstProduct mem) (UInt256.ofNat 0) =
      sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0) := by
  let q := sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)
  have hq : lift q.memory (UInt256.ofNat 0) = q.memory := by
    have h := squareL1_lift (mpZeroed s mem 8) (UInt256.ofNat 0) 8 0 (UInt256.ofNat 0) (by decide)
    rw [TnCacheInitialMemory.lift_zeroed] at h
    exact (congrArg MacState.memory h).symm
  have hm := congrArg (fun m => lift m (UInt256.ofNat 0))
    (R8RowZeroExact.firstMemory_eq s mem hscr)
  change lift (lift (firstProduct mem).memory (firstProduct mem).carry) (UInt256.ofNat 0) =
    lift (lift q.memory (MachineState.readWord q.memory 2080 + q.carry)) (UInt256.ofNat 0) at hm
  rw [lift_overwrite, lift_overwrite, hq] at hm
  have hc := (firstProduct_bridge s mem).2
  have hext : ∀ a b : MacState, a.memory = b.memory → a.carry = b.carry → a = b := by
    intro a b hm' hc'
    cases a; cases b; cases hm'; cases hc'; rfl
  exact hext _ _ hm hc

def first (mem : ByteArray) : CacheState := fromL1 (firstProduct mem) (UInt256.ofNat 0) 8

theorem first_lift (s : State) (mem : ByteArray) (hscr : R8RowZeroExact.ScratchZero mem) :
    lift (first mem).memory (first mem).tn =
      sqRowCarry (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0) := by
  have h := from_lift (firstProduct mem) (UInt256.ofNat 0) 8 (by decide) (by decide)
  rw [product_lift s mem hscr] at h
  exact h.symm

theorem product_read (s : State) (mem : ByteArray) (addr : Nat)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (firstProduct mem).memory addr = MachineState.readWord mem addr := by
  rw [eqFrom_read (firstProduct_bridge s mem).1 addr (by omega),
    readWord_sqL1 _ 8 0 addr _ (by decide) (by omega),
    StagedMonpro.readWord_mpZeroed s mem 8 addr (by decide) (by omega)]

theorem first_read (s : State) (mem : ByteArray) (addr : Nat)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (first mem).memory addr = MachineState.readWord mem addr := by
  rw [first, read_fromL1 _ _ 8 addr (by decide) hout, product_read s mem addr hout]

theorem product_cached (s : State) {mem : ByteArray} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached mem 2368 8 tl inv m0 m96 m64 m32) :
    Cached (firstProduct mem).memory 2368 8 tl inv m0 m96 m64 m32 := by
  refine ⟨h.readonly.of_preserved (product_read s mem 2720 (Or.inr (by decide)))
      (product_read s mem 224 (Or.inl (by decide))),
    h.extra.of_preserved (product_read s mem 96 (Or.inl (by decide)))
      (product_read s mem 64 (Or.inl (by decide)))
      (product_read s mem 32 (Or.inl (by decide))), ?_, fun _ _ => rfl⟩
  unfold inverseInvariant
  rw [product_read s mem 224 (Or.inl (by decide)), product_read s mem 2720 (Or.inr (by decide))]
  exact h.inverse

theorem first_cached (s : State) {mem : ByteArray} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached mem 2368 8 tl inv m0 m96 m64 m32) :
    Cached (first mem).memory 2368 8 tl inv m0 m96 m64 m32 := by
  refine ⟨h.readonly.of_preserved (first_read s mem 2720 (Or.inr (by decide)))
      (first_read s mem 224 (Or.inl (by decide))),
    h.extra.of_preserved (first_read s mem 96 (Or.inl (by decide)))
      (first_read s mem 64 (Or.inl (by decide)))
      (first_read s mem 32 (Or.inl (by decide))), ?_, fun _ _ => rfl⟩
  unfold inverseInvariant
  rw [first_read s mem 224 (Or.inl (by decide)), first_read s mem 2720 (Or.inr (by decide))]
  exact h.inverse

#print axioms product_lift
#print axioms first_lift
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstModel
