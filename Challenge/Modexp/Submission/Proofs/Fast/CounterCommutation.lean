import Challenge.EvmProof.Bytes
import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowEnds

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CounterCommutationPrototype

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
open Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
open Monpro SquareModel SquareResult CarryRowModel

theorem r4Mem_countMem_comm (mem : ByteArray) (c : Nat) (W : R4Math.W5) :
    R4Bridge.r4Mem (countMem mem c) W = countMem (R4Bridge.r4Mem mem W) c := by
  unfold R4Bridge.r4Mem countMem
  have hc : (Data.Bytes.natToBytesPadded c 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h0 : (Data.Bytes.natToBytesPadded W.t0.toNat 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h1 : (Data.Bytes.natToBytesPadded W.t1.toNat 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h2 : (Data.Bytes.natToBytesPadded W.t2.toNat 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h3 : (Data.Bytes.natToBytesPadded W.t3.toNat 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h4 : (Data.Bytes.natToBytesPadded W.t4.toNat 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have hd0 : 2624 + (Data.Bytes.natToBytesPadded c 32).size ≤ 2208 ∨
      2208 + (Data.Bytes.natToBytesPadded W.t0.toNat 32).size ≤ 2624 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have hd1 : 2624 + (Data.Bytes.natToBytesPadded c 32).size ≤ 2176 ∨
      2176 + (Data.Bytes.natToBytesPadded W.t1.toNat 32).size ≤ 2624 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have hd2 : 2624 + (Data.Bytes.natToBytesPadded c 32).size ≤ 2144 ∨
      2144 + (Data.Bytes.natToBytesPadded W.t2.toNat 32).size ≤ 2624 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have hd3 : 2624 + (Data.Bytes.natToBytesPadded c 32).size ≤ 2112 ∨
      2112 + (Data.Bytes.natToBytesPadded W.t3.toNat 32).size ≤ 2624 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have hd4 : 2624 + (Data.Bytes.natToBytesPadded c 32).size ≤ 2080 ∨
      2080 + (Data.Bytes.natToBytesPadded W.t4.toNat 32).size ≤ 2624 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  rw [R8ZeroFirstRow.writeBytes_comm_disjoint _ _ _ 2624 2208 hc h0 hd0,
    R8ZeroFirstRow.writeBytes_comm_disjoint _ _ _ 2624 2176 hc h1 hd1,
    R8ZeroFirstRow.writeBytes_comm_disjoint _ _ _ 2624 2144 hc h2 hd2,
    R8ZeroFirstRow.writeBytes_comm_disjoint _ _ _ 2624 2112 hc h3 hd3,
    R8ZeroFirstRow.writeBytes_comm_disjoint _ _ _ 2624 2080 hc h4 hd4]

theorem r4Final_countMem (mem : ByteArray) (c : Nat) :
    R4Bridge.r4Final (countMem mem c) maxWord
        (MachineState.readWord (countMem mem c) 96)
        (MachineState.readWord (countMem mem c) 64)
        (MachineState.readWord (countMem mem c) 32)
        (MachineState.readWord (countMem mem c) 2720) =
      R4Bridge.r4Final mem maxWord
        (MachineState.readWord mem 96)
        (MachineState.readWord mem 64)
        (MachineState.readWord mem 32)
        (MachineState.readWord mem 2720) := by
  unfold R4Bridge.r4Final
  rw [readWord_countMem_disjoint _ c 2464 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 2432 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 2400 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 2368 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 96 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 64 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 32 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 0 (Or.inl (by omega)),
    readWord_countMem_disjoint _ c 2720 (Or.inr (by omega))]

theorem rows4_countMem_comm (mem : ByteArray) (c : Nat) :
    R4Bridge.rows4 (countMem mem c) = countMem (R4Bridge.rows4 mem) c := by
  unfold R4Bridge.rows4
  rw [r4Final_countMem, r4Mem_countMem_comm]

theorem countMem_writeBytes_comm (mem bytes : ByteArray) (c start : Nat)
    (hbytes : bytes.size ≠ 0) (hstart : start + bytes.size ≤ 2624) :
    MachineState.writeBytes (countMem mem c) bytes start =
      countMem (MachineState.writeBytes mem bytes start) c := by
  unfold countMem
  have hc : (Data.Bytes.natToBytesPadded c 32).size ≠ 0 := by
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have hb : bytes.size ≠ 0 := by omega
  exact R8ZeroFirstRow.writeBytes_comm_disjoint mem
    (Data.Bytes.natToBytesPadded c 32) bytes 2624 start hc hb (Or.inr hstart)

theorem csStep_countMem_comm (mem : ByteArray) (c n : Nat) (hn : n ≤ 8) :
    ∀ j, j ≤ n →
      (Csub.csStep (countMem mem c) n j).memory =
        countMem (Csub.csStep mem n j).memory c ∧
        (Csub.csStep (countMem mem c) n j).flag =
          (Csub.csStep mem n j).flag := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [Csub.csStep]
  | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have ht :
          MachineState.readWord (Csub.csStep (countMem mem c) n j).memory
              (2112 + 32 * (n - 1 - j)) =
            MachineState.readWord (Csub.csStep mem n j).memory
              (2112 + 32 * (n - 1 - j)) := by
        rw [ih'.1]
        exact readWord_countMem_disjoint _ c _ (Or.inl (by omega))
      have hm :
          MachineState.readWord (Csub.csStep (countMem mem c) n j).memory
              (32 * (n - 1 - j)) =
            MachineState.readWord (Csub.csStep mem n j).memory
              (32 * (n - 1 - j)) := by
        rw [ih'.1]
        exact readWord_countMem_disjoint _ c _ (Or.inl (by omega))
      have hd :
          (MachineState.readWord (countMem (Csub.csStep mem n j).memory c)
              (2112 + 32 * (n - 1 - j)) -
            MachineState.readWord (countMem (Csub.csStep mem n j).memory c)
              (32 * (n - 1 - j)) -
            (Csub.csStep (countMem mem c) n j).flag) =
          (MachineState.readWord (Csub.csStep mem n j).memory
              (2112 + 32 * (n - 1 - j)) -
            MachineState.readWord (Csub.csStep mem n j).memory
              (32 * (n - 1 - j)) -
            (Csub.csStep mem n j).flag) := by
        rw [readWord_countMem_disjoint _ c _ (Or.inl (by omega)),
          readWord_countMem_disjoint _ c _ (Or.inl (by omega)), ih'.2]
      simp only [Csub.csStep]
      constructor
      · rw [ih'.1, hd]
        apply countMem_writeBytes_comm
        · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          omega
        · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          omega
      · rw [ht, hm, ih'.2]

theorem subResultMemory_countMem_comm (mem : ByteArray) (c n pdst : Nat)
    (hn1 : 1 ≤ n) (hn32 : n ≤ 8)
    (hsrc : (Csub.csSrc mem n n).toNat + 32 * n ≤ 2624)
    (hdst : pdst + 32 * n ≤ 2624) :
    Csub.subResultMemory (countMem mem c) n pdst =
      countMem (Csub.subResultMemory mem n pdst) c := by
  have hs := csStep_countMem_comm mem c n hn32 n le_rfl
  have hsrcEq : Csub.csSrc (countMem mem c) n n = Csub.csSrc mem n n := by
    unfold Csub.csSrc Csub.csUse
    rw [hs.1, readWord_countMem_disjoint _ c 2080 (Or.inl (by omega)), hs.2]
  have hcopy :
      MachineState.readPadded (Csub.csStep (countMem mem c) n n).memory
          (Csub.csSrc (countMem mem c) n n).toNat (32 * n) =
        MachineState.readPadded (Csub.csStep mem n n).memory
          (Csub.csSrc mem n n).toNat (32 * n) := by
    rw [hs.1, hsrcEq]
    unfold countMem
    apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
    exact Or.inl hsrc
  unfold Csub.subResultMemory
  rw [hcopy, hs.1]
  apply countMem_writeBytes_comm
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdst

theorem lazyResultMemory_countMem_comm (mem : ByteArray) (c n pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hsrc : (Csub.csSrc mem n n).toNat + 32 * n ≤ 2624)
    (hdst : pdst + 32 * n ≤ 2624) :
    LazyCsub.resultMemory (countMem mem c) n pdst =
      countMem (LazyCsub.resultMemory mem n pdst) c := by
  have htn : MachineState.readWord (countMem mem c) 2080 =
      MachineState.readWord mem 2080 :=
    readWord_countMem_disjoint _ c 2080 (Or.inl (by omega))
  by_cases hz : (MachineState.readWord mem 2080).toNat = 0
  · have hzc : (MachineState.readWord (countMem mem c) 2080).toNat = 0 := by
      rw [htn, hz]
    unfold LazyCsub.resultMemory
    rw [if_pos hzc, if_pos hz]
    have hread :
        MachineState.readPadded (countMem mem c) 2112 (32 * n) =
          MachineState.readPadded mem 2112 (32 * n) := by
      unfold countMem
      apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
      exact Or.inl (by omega)
    rw [hread]
    apply countMem_writeBytes_comm
    · rw [Challenge.EvmProof.Memory.readPadded_size]
      omega
    · rw [Challenge.EvmProof.Memory.readPadded_size]
      exact hdst
  · have hzc : (MachineState.readWord (countMem mem c) 2080).toNat ≠ 0 := by
      rw [htn]
      exact hz
    unfold LazyCsub.resultMemory
    rw [if_neg hzc, if_neg hz]
    exact subResultMemory_countMem_comm mem c n pdst (by omega) hn32 hsrc hdst

theorem stage_countMem_comm (mem : ByteArray) (c : Nat) :
    StagedOperand.stage (countMem mem c) 512 4 =
      countMem (StagedOperand.stage mem 512 4) c := by
  unfold StagedOperand.stage
  have hread :
      MachineState.readPadded (countMem mem c) 512 (32 * 4) =
        MachineState.readPadded mem 512 (32 * 4) := by
    unfold countMem
    apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
    exact Or.inl (by omega)
  rw [hread]
  apply countMem_writeBytes_comm
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega

theorem mpZeroed_countMem_comm (s : State) (mem : ByteArray) (c : Nat) :
    Monpro.mpZeroed s (countMem mem c) 4 =
      countMem (Monpro.mpZeroed s mem 4) c := by
  unfold Monpro.mpZeroed
  apply countMem_writeBytes_comm
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega

theorem writeBytes_readPadded_size_of_le
    (bs source : ByteArray) (src len dst : Nat)
    (h : dst + len ≤ bs.size) :
    (MachineState.writeBytes bs (MachineState.readPadded source src len) dst).size = bs.size := by
  rw [MachineState.writeBytes_size, Challenge.EvmProof.Memory.readPadded_size]
  by_cases hz : len = 0
  · simp [hz]
  · rw [if_neg hz]
    exact Nat.max_eq_left h

theorem countMem_size_of_mem_size (mem : ByteArray) (c : Nat)
    (hmem : 2656 ≤ mem.size) : (countMem mem c).size = mem.size := by
  unfold countMem
  exact R8RowZeroExact.size_store_of_le _ _ _ (by omega)

theorem csStep_size_of_mem_size (mem : ByteArray) (n : Nat) (hn : n ≤ 8)
    (hmem : 2656 ≤ mem.size) :
    ∀ j, j ≤ n → (Csub.csStep mem n j).memory.size = mem.size := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro hj
      simp only [Csub.csStep]
      rw [R8RowZeroExact.size_store_of_le _ _ _ (by rw [ih (by omega)]; omega),
        ih (by omega)]

theorem subResultMemory_size_of_mem_size (mem : ByteArray) (n pdst : Nat)
    (hn : n ≤ 8) (hmem : 2656 ≤ mem.size)
    (hdst : pdst + 32 * n ≤ 2624) :
    (Csub.subResultMemory mem n pdst).size = mem.size := by
  have hs := csStep_size_of_mem_size mem n hn hmem n le_rfl
  unfold Csub.subResultMemory
  rw [writeBytes_readPadded_size_of_le _ _ _ _ _ (by rw [hs]; omega), hs]

theorem lazyResultMemory_size_of_mem_size (mem : ByteArray) (n pdst : Nat)
    (hn : n ≤ 8) (hmem : 2656 ≤ mem.size)
    (hdst : pdst + 32 * n ≤ 2624) :
    (LazyCsub.resultMemory mem n pdst).size = mem.size := by
  unfold LazyCsub.resultMemory
  split
  · exact writeBytes_readPadded_size_of_le _ _ _ _ _ (by omega)
  · exact subResultMemory_size_of_mem_size mem n pdst hn hmem hdst

theorem r4Mem_size_of_mem_size (mem : ByteArray) (W : R4Math.W5)
    (hmem : 2656 ≤ mem.size) : (R4Bridge.r4Mem mem W).size = mem.size := by
  have hstore : ∀ (bs : ByteArray) (w start : Nat), bs.size = mem.size →
      start + 32 ≤ mem.size →
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded w 32) start).size = mem.size := by
    intro bs w start hbs hstart
    rw [R8RowZeroExact.size_store_of_le _ _ _ (by rw [hbs]; exact hstart), hbs]
  have h0 :
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208).size =
        mem.size := hstore mem W.t0.toNat 2208 rfl (by omega)
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

theorem rows4_size_of_mem_size (mem : ByteArray) (hmem : 2656 ≤ mem.size) :
    (R4Bridge.rows4 mem).size = mem.size := by
  unfold R4Bridge.rows4
  exact r4Mem_size_of_mem_size mem _ hmem

def rawR4Round (s : State) (mem : ByteArray) (pdst : Nat) : ByteArray :=
  LazyCsub.resultMemory
    (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)) 4 pdst

theorem rawR4Round_size_of_mem_size (s : State) (mem : ByteArray) (pdst : Nat)
    (hmem : 2656 ≤ mem.size) (hdst : pdst + 32 * 4 ≤ 2624) :
    (rawR4Round s mem pdst).size = mem.size := by
  unfold rawR4Round
  have hstage : (StagedOperand.stage mem 512 4).size = mem.size := by
    change (MachineState.writeBytes mem
      (MachineState.readPadded mem 512 (32 * 4)) 2368).size = mem.size
    exact writeBytes_readPadded_size_of_le mem mem 512 (32 * 4) 2368 (by omega)
  have hzero : (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4).size = mem.size := by
    change (MachineState.writeBytes (StagedOperand.stage mem 512 4)
      (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
        (64 + 32 * 4)) 2048).size = mem.size
    calc
      _ = (StagedOperand.stage mem 512 4).size := by
        exact writeBytes_readPadded_size_of_le _ _ s.executionEnv.calldata.size
          (64 + 32 * 4) 2048 (by rw [hstage]; omega)
      _ = mem.size := hstage
  have hzero_mem : 2656 ≤ (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4).size := by
    rw [hzero]
    exact hmem
  have hrows :
      (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)).size = mem.size := by
    exact (rows4_size_of_mem_size _ hzero_mem).trans hzero
  have hlazy :
      (LazyCsub.resultMemory
        (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)) 4 pdst).size =
        (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)).size := by
    exact lazyResultMemory_size_of_mem_size _ 4 pdst (by norm_num)
      (by rw [hrows]; exact hmem) hdst
  exact hlazy.trans hrows

theorem rawR4Round_countMem_comm (s : State) (mem : ByteArray) (c pdst : Nat)
    (hsrc :
      (Csub.csSrc
        (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)) 4 4).toNat +
          32 * 4 ≤ 2624)
    (hdst : pdst + 32 * 4 ≤ 2624) :
    rawR4Round s (countMem mem c) pdst =
      countMem (rawR4Round s mem pdst) c := by
  have hstage := stage_countMem_comm mem c
  have hzero := mpZeroed_countMem_comm s (StagedOperand.stage mem 512 4) c
  have hrows := rows4_countMem_comm
    (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4) c
  have hlazy := lazyResultMemory_countMem_comm
    (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)) c 4 pdst
    (by norm_num) (by norm_num) hsrc hdst
  change LazyCsub.resultMemory
      (R4Bridge.rows4 (Monpro.mpZeroed s
        (StagedOperand.stage (countMem mem c) 512 4) 4)) 4 pdst =
    countMem (LazyCsub.resultMemory
      (R4Bridge.rows4 (Monpro.mpZeroed s
        (StagedOperand.stage mem 512 4) 4)) 4 pdst) c
  calc
    _ = LazyCsub.resultMemory
        (R4Bridge.rows4 (Monpro.mpZeroed s
          (countMem (StagedOperand.stage mem 512 4) c) 4)) 4 pdst := by
          rw [hstage]
    _ = LazyCsub.resultMemory
        (R4Bridge.rows4 (countMem
          (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4) c)) 4 pdst := by
          rw [hzero]
    _ = LazyCsub.resultMemory
        (countMem (R4Bridge.rows4
          (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)) c) 4 pdst := by
          exact congrArg (fun x => LazyCsub.resultMemory x 4 pdst) hrows
    _ = countMem (LazyCsub.resultMemory
        (R4Bridge.rows4 (Monpro.mpZeroed s (StagedOperand.stage mem 512 4) 4)) 4 pdst) c := hlazy

theorem csSrc_extent_of_top_le_one (mem : ByteArray) (n : Nat) (hn : n ≤ 8)
    (htn : (MachineState.readWord (Csub.csStep mem n n).memory 2080).toNat ≤ 1) :
    (Csub.csSrc mem n n).toNat + 32 * n ≤ 2624 := by
  have huse := Csub.csUse_le_one mem n n htn
  rw [Csub.csSrc_toNat mem n n huse]
  split <;> omega

theorem sqPro_countMem_comm (mem : ByteArray) (c n i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 8) :
    (sqPro (countMem mem c) n i tb).memory =
        countMem (sqPro mem n i tb).memory c ∧
      (sqPro (countMem mem c) n i tb).carry =
        (sqPro mem n i tb).carry := by
  have hx := readWord_countMem_disjoint mem c (aAddr n i) (Or.inl (by
    unfold aAddr
    omega))
  have ht := readWord_countMem_disjoint mem c (tAddr n i) (Or.inl (by
    unfold tAddr
    omega))
  have hs : sqSum (countMem mem c) n i tb = sqSum mem n i tb := by
    unfold sqSum sqX
    rw [hx, ht]
  have hc : sqCarry (countMem mem c) n i tb = sqCarry mem n i tb := by
    unfold sqCarry sqX
    rw [hs, hx]
  unfold sqPro
  rw [hs]
  constructor
  · exact countMem_writeBytes_comm mem
      (Data.Bytes.natToBytesPadded (sqSum mem n i tb).toNat 32) c (tAddr n i)
      (by simp) (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; unfold tAddr; omega)
  · exact hc

theorem l1StepOn_countMem_comm (q : MacState) (c n j : Nat) (bi : UInt256)
    (hj : j < n) (hn : n ≤ 8) :
    (l1StepOn {q with memory := countMem q.memory c} bi 2368 n j).memory =
        countMem (l1StepOn q bi 2368 n j).memory c ∧
      (l1StepOn {q with memory := countMem q.memory c} bi 2368 n j).carry =
        (l1StepOn q bi 2368 n j).carry := by
  have hx := readWord_countMem_disjoint q.memory c
    (2368 + 32 * (n - 1 - j)) (Or.inl (by omega))
  have ht := readWord_countMem_disjoint q.memory c
    (2112 + 32 * (n - 1 - j)) (Or.inl (by omega))
  have hsum :
      macSum (MachineState.readWord (countMem q.memory c)
          (2368 + 32 * (n - 1 - j))) bi
          (MachineState.readWord (countMem q.memory c)
            (2112 + 32 * (n - 1 - j))) q.carry =
        macSum (MachineState.readWord q.memory
          (2368 + 32 * (n - 1 - j))) bi
          (MachineState.readWord q.memory
            (2112 + 32 * (n - 1 - j))) q.carry := by
    rw [hx, ht]
  have hcarry :
      macCarry (MachineState.readWord (countMem q.memory c)
          (2368 + 32 * (n - 1 - j))) bi
          (MachineState.readWord (countMem q.memory c)
            (2112 + 32 * (n - 1 - j))) q.carry =
        macCarry (MachineState.readWord q.memory
          (2368 + 32 * (n - 1 - j))) bi
          (MachineState.readWord q.memory
            (2112 + 32 * (n - 1 - j))) q.carry := by
    rw [hx, ht]
  simp only [l1StepOn]
  rw [hsum]
  constructor
  · exact countMem_writeBytes_comm q.memory
      (Data.Bytes.natToBytesPadded
        (macSum (MachineState.readWord q.memory (2368 + 32 * (n - 1 - j))) bi
          (MachineState.readWord q.memory (2112 + 32 * (n - 1 - j))) q.carry).toNat 32) c
      (2112 + 32 * (n - 1 - j)) (by simp)
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)
  · exact hcarry

theorem l1Run_countMem_comm (q : MacState) (c n j0 k : Nat) (bi : UInt256)
    (hj : j0 + k ≤ n) (hn : n ≤ 8) :
    (l1Run {q with memory := countMem q.memory c} bi 2368 n j0 k).memory =
        countMem (l1Run q bi 2368 n j0 k).memory c ∧
      (l1Run {q with memory := countMem q.memory c} bi 2368 n j0 k).carry =
        (l1Run q bi 2368 n j0 k).carry := by
  induction k with
  | zero =>
      simp only [l1Run_zero]
      constructor <;> trivial
  | succ k ih =>
      have hprev := ih (by omega)
      have hstep := l1StepOn_countMem_comm
        (l1Run q bi 2368 n j0 k) c n (j0 + k) bi (by omega) hn
      simpa only [l1Run_succ, l1StepOn, hprev.1, hprev.2] using hstep

theorem sqL1_countMem_comm (mem : ByteArray) (c n i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 8) :
    (sqL1 (countMem mem c) n i tb).memory =
        countMem (sqL1 mem n i tb).memory c ∧
      (sqL1 (countMem mem c) n i tb).carry =
        (sqL1 mem n i tb).carry := by
  have hx := readWord_countMem_disjoint mem c (aAddr n i) (Or.inl (by
    unfold aAddr
    omega))
  have hbi : sqB2 (sqX (countMem mem c) n i) tb = sqB2 (sqX mem n i) tb := by
    unfold sqB2 sqX
    rw [hx]
  have hp := sqPro_countMem_comm mem c n i tb hi hn
  have hstate :
      sqPro (countMem mem c) n i tb =
        {sqPro mem n i tb with memory := countMem (sqPro mem n i tb).memory c} := by
    cases hq : sqPro (countMem mem c) n i tb with
    | mk m1 c1 =>
      cases h : sqPro mem n i tb with
      | mk m2 c2 =>
        simp_all
  unfold sqL1
  rw [hbi, hstate]
  exact l1Run_countMem_comm (sqPro mem n i tb) c n (i + 1) (n - 1 - i)
    (sqB2 (sqX mem n i) tb) (by omega) hn

def l2StepOn (q : MacState) (mu : UInt256) (n k : Nat) : MacState :=
  let x := MachineState.readWord q.memory (32 * (n - 2 - k))
  let t := MachineState.readWord q.memory (2112 + 32 * (n - 2 - k))
  { memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded (macSum x mu t q.carry).toNat 32)
      (2112 + 32 * (n - 1 - k))
    carry := macCarry x mu t q.carry }

theorem l2StepOn_countMem_comm (q : MacState) (c n k : Nat)
    (mu : UInt256) (hn : n ≤ 8) :
    (l2StepOn {q with memory := countMem q.memory c} mu n k).memory =
        countMem (l2StepOn q mu n k).memory c ∧
      (l2StepOn {q with memory := countMem q.memory c} mu n k).carry =
        (l2StepOn q mu n k).carry := by
  have hx := readWord_countMem_disjoint q.memory c (32 * (n - 2 - k))
    (Or.inl (by omega))
  have ht := readWord_countMem_disjoint q.memory c (2112 + 32 * (n - 2 - k))
    (Or.inl (by omega))
  have hs :
      macSum (MachineState.readWord (countMem q.memory c) (32 * (n - 2 - k))) mu
          (MachineState.readWord (countMem q.memory c)
            (2112 + 32 * (n - 2 - k))) q.carry =
        macSum (MachineState.readWord q.memory (32 * (n - 2 - k))) mu
          (MachineState.readWord q.memory (2112 + 32 * (n - 2 - k))) q.carry := by
    rw [hx, ht]
  have hc :
      macCarry (MachineState.readWord (countMem q.memory c) (32 * (n - 2 - k))) mu
          (MachineState.readWord (countMem q.memory c)
            (2112 + 32 * (n - 2 - k))) q.carry =
        macCarry (MachineState.readWord q.memory (32 * (n - 2 - k))) mu
          (MachineState.readWord q.memory (2112 + 32 * (n - 2 - k))) q.carry := by
    rw [hx, ht]
  simp only [l2StepOn]
  rw [hs]
  constructor
  · exact countMem_writeBytes_comm q.memory
      (Data.Bytes.natToBytesPadded
        (macSum (MachineState.readWord q.memory (32 * (n - 2 - k))) mu
          (MachineState.readWord q.memory (2112 + 32 * (n - 2 - k))) q.carry).toNat 32) c
      (2112 + 32 * (n - 1 - k)) (by simp) (by rw
        [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)
  · exact hc

theorem l2Step_countMem_comm (mem : ByteArray) (c n k : Nat)
    (mu c0 : UInt256) (hk : k ≤ n - 1) (hn : n ≤ 8) :
    (l2Step (countMem mem c) mu c0 n k).memory =
        countMem (l2Step mem mu c0 n k).memory c ∧
      (l2Step (countMem mem c) mu c0 n k).carry =
        (l2Step mem mu c0 n k).carry := by
  induction k with
  | zero =>
      simp only [l2Step]
      constructor <;> trivial
  | succ k ih =>
      have hprev := ih (by omega)
      have hstep := l2StepOn_countMem_comm (l2Step mem mu c0 n k) c n k mu hn
      simpa only [l2Step, l2StepOn, hprev.1, hprev.2] using hstep

theorem midMem1_countMem_comm (mem : ByteArray) (c : Nat) (carry : UInt256) :
    midMem1 (countMem mem c) carry = countMem (midMem1 mem carry) c := by
  unfold midMem1
  have h := readWord_countMem_disjoint mem c 2080 (Or.inl (by omega))
  rw [h]
  exact countMem_writeBytes_comm mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 2080 + carry).toNat 32)
    c 2080 (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)

theorem rowMu_countMem_eq (mem : ByteArray) (c n : Nat) (hn : n ≤ 8) :
    rowMu (countMem mem c) n = rowMu mem n := by
  unfold rowMu
  rw [readWord_countMem_disjoint mem c 2720 (Or.inr (by omega)),
    readWord_countMem_disjoint mem c (2080 + 32 * n) (Or.inl (by omega))]

theorem rowC0_countMem_eq (mem : ByteArray) (c n : Nat) (hn : n ≤ 8) :
    rowC0 (countMem mem c) n = rowC0 mem n := by
  unfold rowC0
  rw [readWord_countMem_disjoint mem c (32 * n - 32) (Or.inl (by omega)),
    rowMu_countMem_eq mem c n hn]

theorem overflow_countMem_eq (mem : ByteArray) (c : Nat) (carry : UInt256) :
    overflow (countMem mem c) carry = overflow mem carry := by
  unfold overflow
  rw [readWord_countMem_disjoint mem c 2080 (Or.inl (by omega))]

theorem rowFromL2Carry_countMem_comm (q : MacState) (c n : Nat) (hn : n ≤ 8) :
    (rowFromL2Carry {q with memory := countMem q.memory c} n).memory =
        countMem (rowFromL2Carry q n).memory c ∧
      (rowFromL2Carry {q with memory := countMem q.memory c} n).carry =
        (rowFromL2Carry q n).carry := by
  unfold rowFromL2Carry
  have hmid := midMem1_countMem_comm q.memory c q.carry
  have hmu := rowMu_countMem_eq q.memory c n hn
  have hc0 := rowC0_countMem_eq q.memory c n hn
  rw [hmid, hmu, hc0]
  exact l2Step_countMem_comm (midMem1 q.memory q.carry) c n (n - 1)
    (rowMu q.memory n) (rowC0 q.memory n) (by omega) hn

theorem tailMem1_countMem_comm (mem : ByteArray) (c : Nat) (carry : UInt256) :
    tailMem1 (countMem mem c) carry = countMem (tailMem1 mem carry) c := by
  unfold tailMem1
  have h := readWord_countMem_disjoint mem c 2080 (Or.inl (by omega))
  rw [h]
  exact countMem_writeBytes_comm mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 2080 + carry).toNat 32)
    c 2112 (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)

theorem tailCarry_countMem_comm (mem : ByteArray) (c : Nat)
    (carry f : UInt256) :
    tailCarry (countMem mem c) carry f = countMem (tailCarry mem carry f) c := by
  unfold tailCarry
  have hm := tailMem1_countMem_comm mem c carry
  have h := readWord_countMem_disjoint mem c 2080 (Or.inl (by omega))
  rw [hm, h]
  exact countMem_writeBytes_comm (tailMem1 mem carry)
    (Data.Bytes.natToBytesPadded
      (f + UInt256.lt (MachineState.readWord mem 2080 + carry) carry).toNat 32)
    c 2080 (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)

theorem rowFromCarry_countMem_comm (q : MacState) (c n : Nat) (hn : n ≤ 8) :
    rowFromCarry {q with memory := countMem q.memory c} n =
      countMem (rowFromCarry q n) c := by
  unfold rowFromCarry
  have hl2 := rowFromL2Carry_countMem_comm q c n hn
  have ho := overflow_countMem_eq q.memory c q.carry
  rw [hl2.1, hl2.2, ho]
  exact tailCarry_countMem_comm (rowFromL2Carry q n).memory c
    (rowFromL2Carry q n).carry (overflow q.memory q.carry)

theorem sqRowCarry_countMem_comm (mem : ByteArray) (c n i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 8) :
    sqRowCarry (countMem mem c) n i tb = countMem (sqRowCarry mem n i tb) c := by
  have hq := sqL1_countMem_comm mem c n i tb hi hn
  have hstate :
      sqL1 (countMem mem c) n i tb =
        {sqL1 mem n i tb with memory := countMem (sqL1 mem n i tb).memory c} := by
    cases h1 : sqL1 (countMem mem c) n i tb with
    | mk m1 c1 =>
      cases h2 : sqL1 mem n i tb with
      | mk m2 c2 =>
        simp_all
  unfold sqRowCarry
  rw [hstate]
  exact rowFromCarry_countMem_comm (sqL1 mem n i tb) c n hn

theorem sqRowsCarry_countMem_comm (mem : ByteArray) (c n i : Nat)
    (hi : i ≤ n) (hn : n ≤ 8) :
    sqRowsCarry (countMem mem c) n i = countMem (sqRowsCarry mem n i) c := by
  induction i with
  | zero =>
      simp only [sqRowsCarry_zero]
  | succ i ih =>
      have hprev := ih (by omega)
      have htb :
          sqTb (sqRowsCarry (countMem mem c) n i) n i =
            sqTb (sqRowsCarry mem n i) n i := by
        cases i with
        | zero => rfl
        | succ j =>
            have hr := readWord_countMem_disjoint (sqRowsCarry mem n (j + 1)) c
              (aAddr n j) (Or.inl (by unfold aAddr; omega))
            simpa only [sqTb, hprev] using
              congrArg (fun w => UInt256.sgt (UInt256.ofNat 0) w) hr
      have hrow := sqRowCarry_countMem_comm (sqRowsCarry mem n i) c n i
        (sqTb (sqRowsCarry mem n i) n i) (by omega) hn
      rw [sqRowsCarry_succ, htb, hprev]
      exact hrow

end CounterCommutationPrototype


