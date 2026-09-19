import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact
import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CounterMemoryPrototype

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
open Monpro SquareModel SquareResult

theorem size_l2Step_of_mem_size (mem : ByteArray) (mu c0 : UInt256) (n : Nat)
    (hn : n ≤ 8) (hmem : 2656 ≤ mem.size) :
    ∀ k, (l2Step mem mu c0 n k).memory.size = mem.size
  | 0 => rfl
  | k + 1 => by
      show (MachineState.writeBytes (l2Step mem mu c0 n k).memory _
        (2112 + 32 * (n - 1 - k))).size = mem.size
      rw [R8RowZeroExact.size_store_of_le _ _ _ (by rw [size_l2Step_of_mem_size mem mu c0 n hn hmem k]; omega),
        size_l2Step_of_mem_size mem mu c0 n hn hmem k]

theorem size_tailCarry_of_mem_size (mem : ByteArray) (c f : UInt256)
    (hmem : 2656 ≤ mem.size) :
    (CarryRowModel.tailCarry mem c f).size = mem.size := by
  have htail : (Monpro.tailMem1 mem c).size = mem.size := by
    unfold Monpro.tailMem1
    exact R8RowZeroExact.size_store_of_le _ _ _ (by omega)
  unfold CarryRowModel.tailCarry
  rw [R8RowZeroExact.size_store_of_le _ _ _ (by rw [htail]; omega), htail]

theorem size_rowFromCarry_of_mem_size (q : MacState) (n : Nat) (hn : n ≤ 8)
    (hmem : 2656 ≤ q.memory.size) :
    (SquareResult.rowFromCarry q n).size = q.memory.size := by
  have hmid : (Monpro.midMem1 q.memory q.carry).size = q.memory.size :=
    R8RowZeroExact.size_midMem1 _ _ (by omega)
  have hmidmem : 2656 ≤ (Monpro.midMem1 q.memory q.carry).size := by
    rw [hmid]
    exact hmem
  have hl2 :
      (Monpro.l2Step (Monpro.midMem1 q.memory q.carry)
        (Monpro.rowMu q.memory n) (Monpro.rowC0 q.memory n) n (n - 1)).memory.size =
        q.memory.size := by
    rw [size_l2Step_of_mem_size _ _ _ n hn hmidmem, hmid]
  have hl2mem : 2656 ≤
      (Monpro.l2Step (Monpro.midMem1 q.memory q.carry)
        (Monpro.rowMu q.memory n) (Monpro.rowC0 q.memory n) n (n - 1)).memory.size := by
    rw [hl2]
    exact hmem
  unfold SquareResult.rowFromCarry SquareResult.rowFromL2Carry
  rw [size_tailCarry_of_mem_size _ _ _ hl2mem, hl2]

theorem size_sqL1_of_mem_size (mem : ByteArray) (n i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 8) (hmem : 2656 ≤ mem.size) :
    (SquareModel.sqL1 mem n i tb).memory.size = mem.size := by
  have hp : (SquareModel.sqPro mem n i tb).memory.size = mem.size :=
    R8RowZeroExact.size_sqPro _ _ _ _ (by unfold Monpro.tAddr; omega)
  unfold SquareModel.sqL1
  rw [R8RowZeroExact.size_l1Run _ _ 2368 n (i + 1) hn (by rw [hp]; omega)
      (n - 1 - i), hp]

theorem size_sqRowCarry_of_mem_size (mem : ByteArray) (n i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 8) (hmem : 2656 ≤ mem.size) :
    (SquareResult.sqRowCarry mem n i tb).size = mem.size := by
  have hq : (SquareModel.sqL1 mem n i tb).memory.size = mem.size :=
    size_sqL1_of_mem_size mem n i tb hi hn hmem
  have hqmem : 2656 ≤ (SquareModel.sqL1 mem n i tb).memory.size := by
    rw [hq]
    exact hmem
  unfold SquareResult.sqRowCarry
  rw [size_rowFromCarry_of_mem_size _ n hn hqmem, hq]

theorem size_sqRowsCarry_of_mem_size (mem : ByteArray) (n : Nat) (hn : n ≤ 8)
    (hmem : 2656 ≤ mem.size) :
    ∀ i, i ≤ n → (SquareResult.sqRowsCarry mem n i).size = mem.size := by
  intro i
  induction i with
  | zero =>
      intro _
      rfl
  | succ i ih =>
      intro hi
      rw [SquareResult.sqRowsCarry_succ]
      have hprev : (SquareResult.sqRowsCarry mem n i).size = mem.size :=
        ih (by omega)
      have hprevmem : 2656 ≤ (SquareResult.sqRowsCarry mem n i).size := by
        rw [hprev]
        exact hmem
      rw [size_sqRowCarry_of_mem_size _ n i _ (by omega) hn hprevmem, hprev]

theorem size_sqRowsCarry (mem : ByteArray) (n : Nat) (hn : n ≤ 8)
    (hmem : 2656 ≤ mem.size) :
    (SquareResult.sqRowsCarry mem n n).size = mem.size :=
  size_sqRowsCarry_of_mem_size mem n hn hmem n le_rfl

theorem size_r4Mem_of_mem_size (mem : ByteArray) (W : R4Math.W5)
    (hmem : 2656 ≤ mem.size) :
    (R4Bridge.r4Mem mem W).size = mem.size := by
  have hstore : ∀ (bs : ByteArray) (w start : Nat), bs.size = mem.size →
      start + 32 ≤ mem.size →
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded w 32) start).size = mem.size := by
    intro bs w start hbs hstart
    rw [R8RowZeroExact.size_store_of_le _ _ _ (by rw [hbs]; exact hstart), hbs]
  have h0 :
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208).size =
        mem.size :=
    hstore mem W.t0.toNat 2208 rfl (by omega)
  have h1 :
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208)
        (Data.Bytes.natToBytesPadded W.t1.toNat 32) 2176).size = mem.size :=
    hstore _ W.t1.toNat 2176 h0 (by omega)
  have h2 :
      (MachineState.writeBytes
        (MachineState.writeBytes
          (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208)
          (Data.Bytes.natToBytesPadded W.t1.toNat 32) 2176)
        (Data.Bytes.natToBytesPadded W.t2.toNat 32) 2144).size = mem.size :=
    hstore _ W.t2.toNat 2144 h1 (by omega)
  have h3 :
      (MachineState.writeBytes
        (MachineState.writeBytes
          (MachineState.writeBytes
            (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208)
            (Data.Bytes.natToBytesPadded W.t1.toNat 32) 2176)
          (Data.Bytes.natToBytesPadded W.t2.toNat 32) 2144)
        (Data.Bytes.natToBytesPadded W.t3.toNat 32) 2112).size = mem.size :=
    hstore _ W.t3.toNat 2112 h2 (by omega)
  unfold R4Bridge.r4Mem
  exact hstore _ W.t4.toNat 2080 h3 (by omega)

theorem size_rows4 (mem : ByteArray) (hmem : 2656 ≤ mem.size) :
    (R4Bridge.rows4 mem).size = mem.size := by
  unfold R4Bridge.rows4
  exact size_r4Mem_of_mem_size mem _ hmem

theorem r8_square_round_size (mem : ByteArray) (p : Nat) (hn : p + 2 ≤ 8)
    (hmem : 2656 ≤ mem.size) :
    2656 ≤ (SquareResult.sqRowsCarry mem (p + 2) (p + 2)).size := by
  rw [size_sqRowsCarry mem (p + 2) hn hmem]
  exact hmem

theorem r4_square_round_size (mem : ByteArray) (hmem : 2656 ≤ mem.size) :
    2656 ≤ (R4Bridge.rows4 mem).size := by
  rw [size_rows4 mem hmem]
  exact hmem

theorem r8_square_round_readWord_high (mem : ByteArray) (p pdst addr : Nat)
    (hn : p + 2 ≤ 8) (hpdst : pdst + 32 * (p + 2) ≤ 2624)
    (haddr : 2624 ≤ addr) :
    MachineState.readWord
        (LazyCsub.resultMemory (SquareResult.sqRowsCarry mem (p + 2) (p + 2))
          (p + 2) pdst) addr =
      MachineState.readWord mem addr := by
  rw [LazyCsub.result_readWord_outside _ _ _ _ (by omega) (by omega) (by omega),
    SquareResult.readWord_sqRowsCarry mem (p + 2) addr hn (Or.inr haddr) (p + 2) le_rfl]

theorem r4_square_round_readWord_high (mem : ByteArray) (pdst addr : Nat)
    (hpdst : pdst + 32 * 4 ≤ 2624) (haddr : 2624 ≤ addr) :
    MachineState.readWord (LazyCsub.resultMemory (R4Bridge.rows4 mem) 4 pdst) addr =
      MachineState.readWord mem addr := by
  rw [LazyCsub.result_readWord_outside _ _ _ _ (by omega) (by omega) (by omega),
    R4Bridge.rows4_readWord_outside mem addr (Or.inr (by omega))]

end CounterMemoryPrototype

