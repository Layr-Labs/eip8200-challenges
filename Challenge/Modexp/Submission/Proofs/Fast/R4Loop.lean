import Challenge.Modexp.Submission.Proofs.Fast.R4Bridge
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4 路径下 `n = 4` 的平方循环内存

一回合 = R4（`rows4`）+ 计数器写回 + CSUB。与旧回合的区别只在不再重新清零累加器：
R4 覆盖整个 `t` 窗口，不读旧值。首回合的输入是入口 `setup` 已清零、已暂存的内存。
每回合结果都写回 2368（末回合之后接 fused product）。

`loopMem` 是调用方看到的循环内存：`n = 4` 走 R4 回合，其余走行回合。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Loop

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro StagedOperand SquareModel SquareResult SquareLoopMem R4Bridge

def r4Round (c : Nat) (mem : ByteArray) : ByteArray :=
  Csub.csResultMemory (SquareLoopBlocks.countMem (rows4 mem) c) 4 (roundDst c)

def r4RunMem : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => r4RunMem k (r4Round k mem)

def r4LoopMem (s : State) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => r4RunMem (k + 1) (mpZeroed s (stage mem 512 4) 4)

theorem r4RunMem_succ (k : Nat) (mem : ByteArray) :
    r4RunMem (k + 1) mem = r4RunMem k (r4Round k mem) := rfl

theorem r4LoopMem_succ (s : State) (k : Nat) (mem : ByteArray) :
    r4LoopMem s (k + 1) mem = r4RunMem (k + 1) (mpZeroed s (stage mem 512 4) 4) := rfl

/-! ## 一回合 -/

theorem r4Round_readWord_outside (mem : ByteArray) (c addr : Nat)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * 4 ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * 4 ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (r4Round c mem) addr = MachineState.readWord mem addr := by
  have hd : addr + 32 ≤ roundDst c ∨ roundDst c + 32 * 4 ≤ addr := by
    simp only [roundDst]; omega
  rw [r4Round, csResultMemory_readWord_outside _ 4 (roundDst c) addr (by omega) hsubb hd,
    SquareLoopBlocks.readWord_countMem_disjoint _ c addr hcount,
    rows4_readWord_outside mem addr (by omega)]

theorem r4Round_readWord_high (mem : ByteArray) (c addr : Nat) (haddr : 2656 ≤ addr) :
    MachineState.readWord (r4Round c mem) addr = MachineState.readWord mem addr :=
  r4Round_readWord_outside mem c addr (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

theorem r4Round_count (mem : ByteArray) (c : Nat) (hc : c < 2 ^ 256) :
    MachineState.readWord (r4Round c mem) 2624 = UInt256.ofNat c := by
  rw [r4Round, csResultMemory_readWord_outside _ 4 (roundDst c) 2624 (by omega) (Or.inr (by omega))
    (by simp only [roundDst]; omega)]
  exact SquareLoopBlocks.readWord_countMem _ c hc

theorem r4Round_fastRepresents_outside (mem : ByteArray) (c ptr cnt v : Nat)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * 4 ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2624 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * 4 ≤ ptr)
    (hcount : ptr + 32 * cnt ≤ 2624 ∨ 2656 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (r4Round c mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [r4Round_readWord_outside mem c (ptr + 32 * j) (by omega) (by omega) (by omega) (by omega)]

theorem r4Round_represents (mem : ByteArray) (a mm c : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (r4Round c mem) (roundDst c) 4
      (Model.montMul mm (Limbs.radix ^ 4) a a) := by
  have hrep := rows4_represents mem a mm (roundDst c) ha hm hodd ham hminv
  have hagree := CountAgree.csResult_agree _ _ (CountAgree.countMem_agree (rows4 mem) c) 4
    (roundDst c) (by omega) (by omega) (rows4_tn_le_one mem a mm ha hm hminv ham)
  exact (CountAgree.fastRepresents_iff _ _ hagree (roundDst c) 4 _
    (by simp only [roundDst]; omega)).2 hrep

/-! ## 回合序列 -/

theorem r4RunMem_readWord_outside (k : Nat) (mem : ByteArray) (addr : Nat)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * 4 ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * 4 ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (r4RunMem k mem) addr = MachineState.readWord mem addr := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [r4RunMem_succ, ih (r4Round k mem),
        r4Round_readWord_outside mem k addr hsubb hscratch hdst hcount]

theorem r4RunMem_represents (a mm k : Nat) (mem : ByteArray) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (r4RunMem k mem) 2368 4
      ((fun x => Model.montMul mm (Limbs.radix ^ 4) x x)^[k] a) := by
  induction k generalizing mem a with
  | zero => omega
  | succ k ih =>
      have hrep := r4Round_represents mem a mm k ha hm hodd ham hminv
      cases k with
      | zero => simpa [r4RunMem, roundDst] using hrep
      | succ j =>
        have hmod : Model.FastRepresents (r4Round (j + 1) mem) 0 4 mm :=
          r4Round_fastRepresents_outside mem (j + 1) 0 4 mm (Or.inl (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hm
        have hminv' : ((MachineState.readWord (r4Round (j + 1) mem) 96).toNat *
            (MachineState.readWord (r4Round (j + 1) mem) 2720).toNat + 1) % 2 ^ 256 = 0 := by
          rw [r4Round_readWord_outside mem (j + 1) 96 (Or.inl (by omega)) (Or.inl (by omega))
              (Or.inl (by omega)) (Or.inl (by omega)),
            r4Round_readWord_high mem (j + 1) 2720 (by omega)]
          exact hminv
        have hstage : roundDst (j + 1) = 2368 := by simp [roundDst]
        rw [hstage] at hrep
        rw [r4RunMem_succ, Function.iterate_succ_apply]
        exact ih (Model.montMul mm (Limbs.radix ^ 4) a a) (r4Round (j + 1) mem)
          (by omega) hrep hmod (Model.montMul_lt hmpos _ _ _) hminv'

/-! ## 整个调用（首回合前的暂存与清零） -/

theorem r4LoopMem_readWord_outside (s : State) (mem : ByteArray) (k addr : Nat)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * 4 ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * 4 ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (r4LoopMem s k mem) addr = MachineState.readWord mem addr := by
  cases k with
  | zero => rfl
  | succ k =>
      rw [r4LoopMem_succ, r4RunMem_readWord_outside (k + 1) _ addr hsubb hscratch hdst hcount,
        readWord_mpZeroed s _ 4 addr (by norm_num) hscratch,
        read_stage_outside mem 512 4 addr (by omega)]

theorem r4LoopMem_frame (s : State) (mem : ByteArray) (k : Nat) :
    MachineState.readWord (r4LoopMem s k mem) 2688 = MachineState.readWord mem 2688 ∧
      MachineState.readWord (r4LoopMem s k mem) 2720 = MachineState.readWord mem 2720 ∧
      MachineState.readWord (r4LoopMem s k mem) 2752 = MachineState.readWord mem 2752 ∧
      MachineState.readWord (r4LoopMem s k mem) 2784 = MachineState.readWord mem 2784 ∧
      MachineState.readWord (r4LoopMem s k mem) 2816 = MachineState.readWord mem 2816 :=
  ⟨r4LoopMem_readWord_outside s mem k 2688 (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)),
   r4LoopMem_readWord_outside s mem k 2720 (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)),
   r4LoopMem_readWord_outside s mem k 2752 (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)),
   r4LoopMem_readWord_outside s mem k 2784 (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)),
   r4LoopMem_readWord_outside s mem k 2816 (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega))⟩

theorem r4LoopMem_fastRepresents_outside (s : State) (mem : ByteArray) (k ptr cnt v : Nat)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * 4 ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2656 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * 4 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (r4LoopMem s k mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [r4LoopMem_readWord_outside s mem k (ptr + 32 * j) (by omega) (by omega) (by omega)
    (by omega)]

theorem r4LoopMem_represents (s : State) (mem : ByteArray) (a mm k : Nat) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 512 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (r4LoopMem s k mem) 2368 4
      ((fun x => Model.montMul mm (Limbs.radix ^ 4) x x)^[k] a) := by
  cases k with
  | zero => omega
  | succ k =>
      have hrd (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
          MachineState.readWord (mpZeroed s (stage mem 512 4) 4) addr =
            MachineState.readWord mem addr := by
        rw [readWord_mpZeroed s _ 4 addr (by norm_num) hd,
          read_stage_outside mem 512 4 addr (by omega)]
      have ha' := represents_zeroed_stage s (stage mem 512 4) 4 a (by norm_num)
        (represents_stage mem 4 a ha)
      have hm' : Model.FastRepresents (mpZeroed s (stage mem 512 4) 4) 0 4 mm := by
        refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
        intro j hj
        rw [hrd (0 + 32 * j) (Or.inl (by omega))]
      have hminv' : ((MachineState.readWord (mpZeroed s (stage mem 512 4) 4) 96).toNat *
          (MachineState.readWord (mpZeroed s (stage mem 512 4) 4) 2720).toNat + 1) %
            2 ^ 256 = 0 := by
        rw [hrd 96 (Or.inl (by norm_num)), hrd 2720 (Or.inr (by norm_num))]
        exact hminv
      rw [r4LoopMem_succ]
      exact r4RunMem_represents a mm (k + 1) _ (by omega) ha' hm' hodd ham hmpos hminv'

/-! ## 调用方的循环内存：按 `n` 分派 -/

def loopMem (s : State) (n k : Nat) (mem : ByteArray) : ByteArray :=
  if n = 4 then r4LoopMem s k mem else SquareLoopMem.sqLoopMem s n k mem

theorem loopMem_readWord_outside (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (loopMem s n k mem) addr = MachineState.readWord mem addr := by
  unfold loopMem
  split
  · rename_i h4
    subst h4
    exact r4LoopMem_readWord_outside s mem k addr hsubb hscratch hdst hcount
  · exact SquareLoopMem.sqLoopMem_readWord_outside s mem n k addr hfast hn hn32 hsubb hscratch
      hdst hcount

theorem loopMem_readWord_high (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8) (haddr : 2656 ≤ addr) :
    MachineState.readWord (loopMem s n k mem) addr = MachineState.readWord mem addr :=
  loopMem_readWord_outside s mem n k addr hfast hn hn32 (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

theorem loopMem_frame (s : State) (mem : ByteArray) (n k : Nat) (hfast : n = 4 ∨ n = 8)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) :
    MachineState.readWord (loopMem s n k mem) 2688 = MachineState.readWord mem 2688 ∧
      MachineState.readWord (loopMem s n k mem) 2720 = MachineState.readWord mem 2720 ∧
      MachineState.readWord (loopMem s n k mem) 2752 = MachineState.readWord mem 2752 ∧
      MachineState.readWord (loopMem s n k mem) 2784 = MachineState.readWord mem 2784 ∧
      MachineState.readWord (loopMem s n k mem) 2816 = MachineState.readWord mem 2816 :=
  ⟨loopMem_readWord_high s mem n k 2688 hfast hn hn32 (by omega),
   loopMem_readWord_high s mem n k 2720 hfast hn hn32 (by omega),
   loopMem_readWord_high s mem n k 2752 hfast hn hn32 (by omega),
   loopMem_readWord_high s mem n k 2784 hfast hn hn32 (by omega),
   loopMem_readWord_high s mem n k 2816 hfast hn hn32 (by omega)⟩

theorem loopMem_fastRepresents_outside (s : State) (mem : ByteArray) (n k ptr cnt v : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2656 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (loopMem s n k mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [loopMem_readWord_outside s mem n k (ptr + 32 * j) hfast hn hn32 (by omega) (by omega)
    (by omega) (by omega)]

theorem loopMem_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hn32 : p + 2 ≤ 8) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 512 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (loopMem s (p + 2) k mem) 2368 (p + 2)
      ((fun x => Model.montMul mm (Limbs.radix ^ (p + 2)) x x)^[k] a) := by
  unfold loopMem
  split
  · rename_i h4
    have hp : p = 2 := by omega
    subst hp
    exact r4LoopMem_represents s mem a mm k hk ha hm hodd ham hmpos hminv
  · exact SquareLoopMem.sqLoopMem_represents s mem p a mm k hfast hn32 hk ha hm hodd ham hmpos
      hminv

end Challenge.Modexp.Submission.Proofs.Fast.R4Loop
