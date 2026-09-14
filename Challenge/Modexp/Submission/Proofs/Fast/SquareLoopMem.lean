import Challenge.Modexp.Submission.Proofs.Fast.LazyLoopMemory
import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel StagedOperand SquareModel SquareResult

def roundDst (_c : Nat) : Nat := 2368

def sqRound (s : State) (n c : Nat) (mem : ByteArray) : ByteArray :=
  LazyCsub.resultMemory
    (SquareLoopBlocks.countMem (sqRowsCarry (mpZeroed s mem n) n n) c) n (roundDst c)

/-- Writing the same bytes at the same place twice is the same as writing them once. -/
theorem writeBytes_writeBytes_same (bs bytes : ByteArray) (start : Nat) :
    MachineState.writeBytes (MachineState.writeBytes bs bytes start) bytes start =
      MachineState.writeBytes bs bytes start := by
  have hsize : (MachineState.writeBytes (MachineState.writeBytes bs bytes start) bytes start).size =
      (MachineState.writeBytes bs bytes start).size := by
    rw [MachineState.writeBytes_size (MachineState.writeBytes bs bytes start),
      MachineState.writeBytes_size bs]
    split_ifs <;> omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi',
    MachineState.writeBytes_getElem?_getD (MachineState.writeBytes bs bytes start)]
  split_ifs with h
  · rw [MachineState.writeBytes_getElem?_getD bs, if_pos h]
  · rfl

/-- Zeroing the accumulator region is idempotent. -/
theorem mpZeroed_idem (s : State) (mem : ByteArray) (n : Nat) :
    mpZeroed s (mpZeroed s mem n) n = mpZeroed s mem n := by
  unfold mpZeroed
  exact writeBytes_writeBytes_same _ _ _

/-- One squaring round never touches the scratch word `[2048, 2080)`. -/
theorem scratchZero_sqRound (s : State) (n c : Nat) (M : ByteArray) (hn1 : 1 ≤ n)
    (hn : n ≤ 8) : R8RowZeroExact.ScratchZero (sqRound s n c M) := by
  have h0 := (R8RowZeroExact.scratchZero_mpZeroed s M n hn1).sqRowsCarry n n
  have h1 := h0.store c 2624 (Or.inr (by decide))
  unfold sqRound LazyCsub.resultMemory SquareLoopBlocks.countMem Csub.subResultMemory roundDst
  split
  · exact h1.write _ 2368 (Or.inr (by decide))
  · exact (h1.csStep n hn n).write _ 2368 (Or.inr (by decide))

def sqRunMem (s : State) (n : Nat) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => sqRunMem s n k (sqRound s n k mem)

def sqLoopMem (s : State) (n : Nat) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => sqRunMem s n (k + 1) (stage mem 512 n)

theorem sqLoopMem_zero (s : State) (n : Nat) (mem : ByteArray) : sqLoopMem s n 0 mem = mem := rfl

theorem sqLoopMem_succ (s : State) (n k : Nat) (mem : ByteArray) :
    sqLoopMem s n (k + 1) mem = sqRunMem s n (k + 1) (stage mem 512 n) := rfl

theorem sqRunMem_zero (s : State) (n : Nat) (mem : ByteArray) : sqRunMem s n 0 mem = mem := rfl

theorem sqRunMem_succ (s : State) (n k : Nat) (mem : ByteArray) :
    sqRunMem s n (k + 1) mem = sqRunMem s n k (sqRound s n k mem) := rfl

theorem sqRound_mpZeroed (s : State) (n c : Nat) (mem : ByteArray) :
    sqRound s n c (mpZeroed s mem n) = sqRound s n c mem := by
  unfold sqRound; rw [mpZeroed_idem]

/-- A run of at least one round does not see whether its entry memory was already zeroed. -/
theorem sqRunMem_mpZeroed (s : State) (n k : Nat) (mem : ByteArray) (hk : 1 ≤ k) :
    sqRunMem s n k (mpZeroed s mem n) = sqRunMem s n k mem := by
  cases k with
  | zero => omega
  | succ j => rw [sqRunMem_succ, sqRunMem_succ, sqRound_mpZeroed]

theorem tn_le_one (s : State) (mem : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 8)
    (_hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    (MachineState.readWord (sqRowsCarry (mpZeroed s mem (p + 2)) (p + 2) (p + 2)) 2080).toNat ≤ 1 := by
  have ha0 := represents_zeroed_stage s mem (p + 2) a (by omega) ha
  have hm0 : Model.FastRepresents (mpZeroed s mem (p + 2)) 0 (p + 2) mm := by
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [readWord_mpZeroed s mem (p + 2) (0 + 32 * j) hn32 (Or.inl (by omega))]
  have hminv0 : ((MachineState.readWord (mpZeroed s mem (p + 2)) (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord (mpZeroed s mem (p + 2)) 2720).toNat + 1) % 2 ^ 256 = 0 := by
    rw [readWord_mpZeroed s mem (p + 2) (32 * (p + 2) - 32) hn32 (Or.inl (by omega)),
      readWord_mpZeroed s mem (p + 2) 2720 hn32 (Or.inr (by decide))]
    exact hminv
  exact LazySquareMemory.carry_tn_le_one (mpZeroed s mem (p + 2)) p a mm (by omega)
    ha0 hm0 hmpos hminv0 (tValue_mpZeroed s mem (p + 2))

def sqRoundValue (s : State) (n c : Nat) (mem : ByteArray) (mm : Nat) : Nat :=
  LazySquareMemory.roundValue
    (SquareLoopBlocks.countMem (sqRowsCarry (mpZeroed s mem n) n n) c) n mm

theorem sqRound_represents (s : State) (mem : ByteArray) (p a mm c : Nat) (hn32 : p + 2 ≤ 8)
    (_hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (_har : a < Limbs.radix^(p+2))
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqRound s (p + 2) c mem) (roundDst c) (p + 2)
      (sqRoundValue s (p+2) c mem mm) := by
  have ha0 := represents_zeroed_stage s mem (p + 2) a (by omega) ha
  have hm0 : Model.FastRepresents (mpZeroed s mem (p + 2)) 0 (p + 2) mm := by
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [readWord_mpZeroed s mem (p + 2) (0 + 32 * j) hn32 (Or.inl (by omega))]
  have hminv0 : ((MachineState.readWord (mpZeroed s mem (p + 2)) (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord (mpZeroed s mem (p + 2)) 2720).toNat + 1) % 2 ^ 256 = 0 := by
    rw [readWord_mpZeroed s mem (p + 2) (32 * (p + 2) - 32) hn32 (Or.inl (by omega)),
      readWord_mpZeroed s mem (p + 2) 2720 hn32 (Or.inr (by decide))]
    exact hminv
  exact (LazySquareMemory.carry_result (mpZeroed s mem (p+2)) p a mm c (roundDst c)
    hn32 ha0 hm0 hodd hminv0 (tValue_mpZeroed s mem (p+2))).1

theorem sqRound_readWord_outside (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (_hfast : n = 4 ∨ n = 8)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (sqRound s n c mem) addr = MachineState.readWord mem addr := by
  have hd : addr + 32 ≤ roundDst c ∨ roundDst c + 32 * n ≤ addr := by
    simp only [roundDst]; omega
  rw [sqRound, LazyCsub.result_readWord_outside _ n (roundDst c) addr hn hsubb hd,
    SquareLoopBlocks.readWord_countMem_disjoint _ c addr hcount,
    readWord_sqRowsCarry _ n addr hn32 hscratch n le_rfl,
    readWord_mpZeroed s _ n addr hn32 hscratch]

theorem sqRound_readWord_high (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hfast : n = 4 ∨ n = 8) (haddr : 2656 ≤ addr) :
    MachineState.readWord (sqRound s n c mem) addr = MachineState.readWord mem addr :=
  sqRound_readWord_outside s mem n c addr hn hn32 hfast (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

theorem sqRound_count (s : State) (mem : ByteArray) (n c : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (_hfast : n = 4 ∨ n = 8) (hc : c < 2 ^ 256) :
    MachineState.readWord (sqRound s n c mem) 2624 = UInt256.ofNat c := by
  rw [sqRound, LazyCsub.result_readWord_outside _ n (roundDst c) 2624 hn (Or.inr (by omega))
    (by simp only [roundDst]; omega)]
  exact SquareLoopBlocks.readWord_countMem _ c hc

theorem sqRound_fastRepresents_outside (s : State) (mem : ByteArray) (n c ptr cnt v : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hfast : n = 4 ∨ n = 8)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2624 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr)
    (hcount : ptr + 32 * cnt ≤ 2624 ∨ 2656 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqRound s n c mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [sqRound_readWord_outside s mem n c (ptr + 32 * j) hn hn32 hfast (by omega) (by omega)
    (by omega) (by omega)]

theorem sqRunMem_readWord_outside (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (sqRunMem s n k mem) addr = MachineState.readWord mem addr := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [sqRunMem_succ, ih (sqRound s n k mem),
        sqRound_readWord_outside s mem n k addr hn hn32 hfast hsubb hscratch hdst hcount]

theorem sqRunMem_readWord_high (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8) (haddr : 2656 ≤ addr) :
    MachineState.readWord (sqRunMem s n k mem) addr = MachineState.readWord mem addr :=
  sqRunMem_readWord_outside s mem n k addr hfast hn hn32 (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

theorem sqRunMem_frame (s : State) (mem : ByteArray) (n k : Nat) (hfast : n = 4 ∨ n = 8)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) :
    MachineState.readWord (sqRunMem s n k mem) 2688 = MachineState.readWord mem 2688 ∧
      MachineState.readWord (sqRunMem s n k mem) 2720 = MachineState.readWord mem 2720 ∧
      MachineState.readWord (sqRunMem s n k mem) 2752 = MachineState.readWord mem 2752 ∧
      MachineState.readWord (sqRunMem s n k mem) 2784 = MachineState.readWord mem 2784 ∧
      MachineState.readWord (sqRunMem s n k mem) 2816 = MachineState.readWord mem 2816 :=
  ⟨sqRunMem_readWord_high s mem n k 2688 hfast hn hn32 (by omega),
   sqRunMem_readWord_high s mem n k 2720 hfast hn hn32 (by omega),
   sqRunMem_readWord_high s mem n k 2752 hfast hn hn32 (by omega),
   sqRunMem_readWord_high s mem n k 2784 hfast hn hn32 (by omega),
   sqRunMem_readWord_high s mem n k 2816 hfast hn hn32 (by omega)⟩

theorem sqRunMem_fastRepresents_outside (s : State) (mem : ByteArray) (n k ptr cnt v : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2656 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqRunMem s n k mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [sqRunMem_readWord_outside s mem n k (ptr + 32 * j) hfast hn hn32 (by omega) (by omega)
    (by omega) (by omega)]

theorem sqRunMem_eq_run (s : State) (n k : Nat) (mem : ByteArray) (h4 : n ≠ 4) :
    sqRunMem s n k mem = LazyLoopMemory.run s n k mem := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [sqRunMem_succ, LazyLoopMemory.run, ih]
      congr 1
      simp only [sqRound, roundDst, LazyLoopMemory.round, LazyLoopMemory.rows, if_neg h4]

theorem sqRunMem_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (_hfast : p+2 = 4 ∨ p+2 = 8) (hn32 : p+2 ≤ 8) (hk : 1 ≤ k) (h4 : p+2 ≠ 4)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1)
    (_har : a < Limbs.radix^(p+2)) (_hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    ∃ v, Model.FastRepresents (sqRunMem s (p+2) k mem) 2368 (p+2) v ∧
      v < Limbs.radix^(p+2) ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) := by
  rw [sqRunMem_eq_run s (p+2) k mem h4]
  exact LazyLoopMemory.run_represents s mem p a mm k hn32 hk ha hm hodd hminv

theorem sqLoopMem_readWord_outside (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (sqLoopMem s n k mem) addr = MachineState.readWord mem addr := by
  cases k with
  | zero => rfl
  | succ k =>
      rw [sqLoopMem_succ, sqRunMem_readWord_outside s _ n (k + 1) addr hfast hn hn32 hsubb hscratch hdst hcount,
        read_stage_outside mem 512 n addr (by omega)]

theorem sqLoopMem_readWord_high (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8) (haddr : 2656 ≤ addr) :
    MachineState.readWord (sqLoopMem s n k mem) addr = MachineState.readWord mem addr :=
  sqLoopMem_readWord_outside s mem n k addr hfast hn hn32 (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

theorem sqLoopMem_frame (s : State) (mem : ByteArray) (n k : Nat) (hfast : n = 4 ∨ n = 8)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) :
    MachineState.readWord (sqLoopMem s n k mem) 2688 = MachineState.readWord mem 2688 ∧
      MachineState.readWord (sqLoopMem s n k mem) 2720 = MachineState.readWord mem 2720 ∧
      MachineState.readWord (sqLoopMem s n k mem) 2752 = MachineState.readWord mem 2752 ∧
      MachineState.readWord (sqLoopMem s n k mem) 2784 = MachineState.readWord mem 2784 ∧
      MachineState.readWord (sqLoopMem s n k mem) 2816 = MachineState.readWord mem 2816 :=
  ⟨sqLoopMem_readWord_high s mem n k 2688 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 2720 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 2752 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 2784 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 2816 hfast hn hn32 (by omega)⟩

theorem sqLoopMem_fastRepresents_outside (s : State) (mem : ByteArray) (n k ptr cnt v : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2656 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqLoopMem s n k mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [sqLoopMem_readWord_outside s mem n k (ptr + 32 * j) hfast hn hn32 (by omega) (by omega)
    (by omega) (by omega)]

theorem sqLoopMem_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hn32 : p + 2 ≤ 8) (hk : 1 ≤ k) (h4 : p+2 ≠ 4)
    (ha : Model.FastRepresents mem 512 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (har : a < Limbs.radix^(p+2)) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∃ v, Model.FastRepresents (sqLoopMem s (p+2) k mem) 2368 (p+2) v ∧
      v < Limbs.radix^(p+2) ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) := by
  cases k with
  | zero => omega
  | succ k =>
      have hm' : Model.FastRepresents (stage mem 512 (p + 2)) 0 (p + 2) mm := by
        refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
        intro j hj
        rw [read_stage_outside mem 512 (p + 2) (0 + 32 * j) (Or.inl (by omega))]
      have hminv' : ((MachineState.readWord (stage mem 512 (p + 2)) (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord (stage mem 512 (p + 2)) 2720).toNat + 1) % 2 ^ 256 = 0 := by
        rw [read_stage_outside mem 512 (p + 2) (32 * (p + 2) - 32) (Or.inl (by omega)),
          read_stage_outside mem 512 (p + 2) 2720 (Or.inr (by omega))]
        exact hminv
      exact sqRunMem_represents s (stage mem 512 (p + 2)) p a mm (k + 1) hfast hn32 (by omega) h4
        (represents_stage mem (p + 2) a ha) hm' hodd har hmpos hminv'

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
