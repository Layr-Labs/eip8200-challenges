import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowModel

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.TnMod128Invariant
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro TnCacheMemory

theorem fromL1_read (q : MacState) (tn : UInt256) (n : Nat) :
    MachineState.readWord (TnCacheSquareModel.fromL1 q tn n).memory 128 =
      MachineState.readWord q.memory 128 := by
  simp only [TnCacheSquareModel.fromL1]
  rw [read_put_outside _ _ 2112 128 (Or.inl (by decide))]
  exact readWord_l2Step_low _ _ _ n 128 (n-1) (by decide)

theorem row_read (z : TnCacheRowModel.CacheState) (pa pb n i : Nat) :
    MachineState.readWord (TnCacheRowModel.row z pa pb n i).memory 128 =
      MachineState.readWord z.memory 128 := by
  simp only [TnCacheRowModel.row]
  rw [read_put_outside _ _ 2112 128 (Or.inl (by decide)),
    readWord_l2Step_low _ _ _ n 128 (n-1) (by decide),
    readWord_l1Step_low _ _ pa n 128 n (by decide)]

theorem rows_read (z : TnCacheRowModel.CacheState) (pa pb n k : Nat) :
    MachineState.readWord (TnCacheRowModel.rows z pa pb n k).memory 128 =
      MachineState.readWord z.memory 128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [TnCacheRowModel.rows, row_read, ih]

theorem row_read_low (z : TnCacheRowModel.CacheState) (pa pb n i addr : Nat)
    (haddr : addr + 32 ≤ 2112) :
    MachineState.readWord (TnCacheRowModel.row z pa pb n i).memory addr =
      MachineState.readWord z.memory addr := by
  simp only [TnCacheRowModel.row]
  rw [read_put_outside _ _ 2112 addr (Or.inl haddr),
    readWord_l2Step_low _ _ _ n addr (n-1) haddr,
    readWord_l1Step_low _ _ pa n addr n haddr]

theorem rows_read_low (z : TnCacheRowModel.CacheState) (pa pb n k addr : Nat)
    (haddr : addr + 32 ≤ 2112) :
    MachineState.readWord (TnCacheRowModel.rows z pa pb n k).memory addr =
      MachineState.readWord z.memory addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [TnCacheRowModel.rows, row_read_low _ _ _ _ _ _ haddr, ih]

theorem squareRow_read (z : TnCacheRowModel.CacheState) (n i : Nat) (hi : i < n) :
    MachineState.readWord (TnCacheSquareModel.squareRow z n i).memory 128 =
      MachineState.readWord z.memory 128 := by
  rw [TnCacheSquareModel.squareRow, fromL1_read,
    SquareModel.readWord_sqL1 _ n i 128 _ hi (Or.inl (by decide))]

theorem squareRows_read (z : TnCacheRowModel.CacheState) (n k : Nat) (hk : k ≤ n) :
    MachineState.readWord (TnCacheSquareModel.squareRows z n k).memory 128 =
      MachineState.readWord z.memory 128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [TnCacheSquareModel.squareRows, squareRow_read _ n k (by omega), ih (by omega)]

theorem zeroRun_read (q : MacState) (bi : UInt256) (k : Nat) :
    MachineState.readWord (R8ZeroFirstRow.zeroRun q bi k).memory 128 =
      MachineState.readWord q.memory 128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [R8ZeroFirstRow.zeroRun, R8ZeroFirstRow.zeroStep]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih
      · apply Or.inl
        unfold tAddr
        omega

theorem firstProduct_read (mem : ByteArray) :
    MachineState.readWord (R8ZeroFirstRow.firstProduct mem).memory 128 =
      MachineState.readWord mem 128 := by
  rw [R8ZeroFirstRow.firstProduct, zeroRun_read]
  change MachineState.readWord (put mem _ 2336) 128 = _
  exact read_put_outside _ _ 2336 128 (Or.inl (by decide))

end Challenge.Modexp.Submission.Proofs.Fast.TnMod128Invariant
