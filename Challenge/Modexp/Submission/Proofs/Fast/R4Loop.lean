import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000
namespace Challenge.Modexp.Submission.Proofs.Fast.R4Loop
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro StagedOperand SquareModel SquareResult SquareLoopMem R4Bridge

def r4Round (c : Nat) (mem : ByteArray) : ByteArray :=
  LazyCsub.resultMemory (SquareLoopBlocks.countMem (rows4 mem) c) 4 (roundDst c)

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

theorem r4Round_readWord_outside (mem : ByteArray) (c addr : Nat)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * 4 ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * 4 ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (r4Round c mem) addr = MachineState.readWord mem addr := by
  have hd : addr + 32 ≤ roundDst c ∨ roundDst c + 32 * 4 ≤ addr := by
    simp only [roundDst]; omega
  rw [r4Round, LazyCsub.result_readWord_outside _ 4 (roundDst c) addr (by omega) hsubb hd,
    SquareLoopBlocks.readWord_countMem_disjoint _ c addr hcount,
    rows4_readWord_outside mem addr (by omega)]

theorem r4Round_readWord_high (mem : ByteArray) (c addr : Nat) (haddr : 2656 ≤ addr) :
    MachineState.readWord (r4Round c mem) addr = MachineState.readWord mem addr :=
  r4Round_readWord_outside mem c addr (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

theorem r4Round_count (mem : ByteArray) (c : Nat) (hc : c < 2 ^ 256) :
    MachineState.readWord (r4Round c mem) 2624 = UInt256.ofNat c := by
  rw [r4Round, LazyCsub.result_readWord_outside _ 4 (roundDst c) 2624 (by omega) (Or.inr (by omega))
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

def r4RoundValue (mem : ByteArray) (c mm : Nat) : Nat :=
  LazySquareMemory.roundValue (SquareLoopBlocks.countMem (rows4 mem) c) 4 mm

theorem r4Round_represents (mem : ByteArray) (a mm c : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (_har : a < Limbs.radix^4)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (r4Round c mem) (roundDst c) 4 (r4RoundValue mem c mm) := by
  rw [r4Round]
  exact (LazySquareMemory.r4_result mem a mm c (roundDst c) ha hm hodd hminv).1

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

theorem r4Round_eq_round (s : State) (c : Nat) (mem : ByteArray) :
    r4Round c mem = LazyLoopMemory.round s 4 c mem := by
  exact congrArg
    (fun r : ByteArray => LazyCsub.resultMemory (SquareLoopBlocks.countMem r c) 4 2368)
    (show rows4 mem = LazyLoopMemory.rows s 4 mem from
      (if_pos (rfl : (4 : Nat) = 4)).symm)

theorem r4RunMem_eq_run (s : State) (k : Nat) (mem : ByteArray) :
    r4RunMem k mem = LazyLoopMemory.run s 4 k mem := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [r4RunMem_succ, LazyLoopMemory.run, ih, r4Round_eq_round]

theorem r4RunMem_represents (s : State) (a mm k : Nat) (mem : ByteArray) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (_har : a < Limbs.radix^4) (_hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    ∃ v, Model.FastRepresents (r4RunMem k mem) 2368 4 v ∧ v < Limbs.radix^4 ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^4) x x)^[k] a) := by
  rw [r4RunMem_eq_run s k mem]
  exact LazyLoopMemory.run_represents s mem 2 a mm k (by omega) hk ha hm hodd hminv

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
    (hodd : mm % 2 = 1) (har : a < Limbs.radix^4) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∃ v, Model.FastRepresents (r4LoopMem s k mem) 2368 4 v ∧ v < Limbs.radix^4 ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^4) x x)^[k] a) := by
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
      exact r4RunMem_represents s a mm (k + 1) _ (by omega) ha' hm' hodd har hmpos hminv'

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
    (hodd : mm % 2 = 1) (har : a < Limbs.radix^(p+2)) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∃ v, Model.FastRepresents (loopMem s (p+2) k mem) 2368 (p+2) v ∧ v < Limbs.radix^(p+2) ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) := by
  unfold loopMem
  split
  · rename_i h4
    have hp : p = 2 := by omega
    subst hp
    exact r4LoopMem_represents s mem a mm k hk ha hm hodd har hmpos hminv
  · rename_i hn4
    exact SquareLoopMem.sqLoopMem_represents s mem p a mm k hfast hn32 hk hn4 ha hm hodd har hmpos
      hminv

end Challenge.Modexp.Submission.Proofs.Fast.R4Loop
