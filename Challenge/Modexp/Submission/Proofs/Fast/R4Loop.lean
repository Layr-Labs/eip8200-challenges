import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

/-!
# The n=4 square loop memory (n4a + n4t + rare4)

The four-limb kernel squares the operand in place: every round reads `a` from 2112..2208 and the
tail stores the reduced square back there (`R4Bridge.rows4r`, overflow word 2080 zeroed).  After
the last round the lazy gate copies the window to 2368 for the fused product.  The eight-limb
loop keeps `SquareLoopMem.sqLoopMem`; `loopMem` picks the model by width.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Loop
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro StagedOperand SquareModel SquareResult SquareLoopMem

/-- `k` n=4 rounds. -/
def r4Steps : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => r4Steps k (R4Bridge.rows4r mem)

/-- `k` rounds, then the lazy gate (`[2368, after_sq]` on a zero overflow word: the copy of the
window to 2368). -/
def r4RunMem (k : Nat) (mem : ByteArray) : ByteArray :=
  LazyCsub.resultMemory (r4Steps k mem) 4 2368

/-- The whole n=4 call: the setup's self-copy, the cleared scratch word, then the rounds. -/
def r4LoopMem (_s : State) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => r4RunMem (k + 1) (SquarePartialClear.memory (stageW mem 2112 4))

theorem r4Steps_succ (k : Nat) (mem : ByteArray) :
    r4Steps (k + 1) mem = r4Steps k (R4Bridge.rows4r mem) := rfl

theorem r4LoopMem_succ (s : State) (k : Nat) (mem : ByteArray) :
    r4LoopMem s (k + 1) mem =
      r4RunMem (k + 1) (SquarePartialClear.memory (stageW mem 2112 4)) := rfl

theorem r4Steps_readWord_outside (k : Nat) (mem : ByteArray) (addr : Nat)
    (h : addr + 32 ≤ 2080 ∨ 2240 ≤ addr) :
    MachineState.readWord (r4Steps k mem) addr = MachineState.readWord mem addr := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [r4Steps_succ, ih, R4Bridge.rows4r_readWord_outside mem addr h]

theorem r4RunMem_readWord_outside (k : Nat) (mem : ByteArray) (addr : Nat)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * 4 ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
    MachineState.readWord (r4RunMem k mem) addr = MachineState.readWord mem addr := by
  unfold r4RunMem
  rw [LazyCsub.result_readWord_outside _ 4 2368 addr (by omega) hsubb (by omega),
    r4Steps_readWord_outside k mem addr (by omega)]

theorem r4LoopMem_readWord_outside (s : State) (mem : ByteArray) (k addr : Nat)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * 4 ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (_hdst : addr + 32 ≤ 512 ∨ 512 + 32 * 4 ≤ addr)
    (_hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (r4LoopMem s k mem) addr = MachineState.readWord mem addr := by
  cases k with
  | zero => rfl
  | succ k =>
      rw [r4LoopMem_succ, r4RunMem_readWord_outside (k + 1) _ addr hsubb hscratch,
        SquarePartialClear.readWord_outside _ addr (by omega),
        read_stageW_four_outside mem addr (by omega)]

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

/-- The rounds: after `k ≥ 1` of them the operand window holds the `k`-fold Montgomery square,
below `R⁴`, and the overflow word is zero. -/
theorem r4Steps_represents (mm : Nat) (hodd : mm % 2 = 1) :
    ∀ (k : Nat) (mem : ByteArray) (a : Nat), 1 ≤ k →
      Model.FastRepresents mem 2112 4 a → Model.FastRepresents mem 0 4 mm →
      ((MachineState.readWord mem 96).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0 →
      ∃ v, Model.FastRepresents (r4Steps k mem) 2112 4 v ∧ v < Limbs.radix^4 ∧
        v % mm = ((fun x => Model.montMul mm (Limbs.radix^4) x x)^[k] a) ∧
        MachineState.readWord (r4Steps k mem) 2080 = ⟨0⟩ := by
  intro k
  induction k with
  | zero => intro _ _ hk; omega
  | succ k ih =>
      intro mem a _ ha hm hminv
      obtain ⟨hv, hvr, hvm, h0⟩ := LazySquareMemory.r4r_result mem a mm ha hm hodd hminv
      rw [r4Steps_succ]
      cases k with
      | zero => exact ⟨_, hv, hvr, hvm, h0⟩
      | succ j =>
          have hm' := R4Bridge.rows4r_fastRepresents_outside mem 0 4 mm (Or.inl (by omega)) hm
          have hi' : ((MachineState.readWord (R4Bridge.rows4r mem) 96).toNat *
              (MachineState.readWord (R4Bridge.rows4r mem) 2720).toNat + 1) % 2^256 = 0 := by
            rw [R4Bridge.rows4r_readWord_outside mem 96 (Or.inl (by omega)),
              R4Bridge.rows4r_readWord_outside mem 2720 (Or.inr (by omega))]
            exact hminv
          obtain ⟨w, hw, hwr, hwm, hw0⟩ := ih (R4Bridge.rows4r mem) _ (by omega) hv hm' hi'
          refine ⟨w, hw, hwr, ?_, hw0⟩
          rw [hwm]
          have hf := LazyLoopMemory.mont_square_congr mm (Limbs.radix^4)
            (LazySquareMemory.roundValue (R4Bridge.rows4 mem) 4 mm)
            (Model.montMul mm (Limbs.radix^4) a a)
            (by rw [hvm, Nat.mod_eq_of_lt (Model.montMul_lt (by omega) _ _ _)])
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          exact congrArg ((fun x => Model.montMul mm (Limbs.radix^4) x x)^[j]) hf

theorem r4RunMem_represents (a mm k : Nat) (mem : ByteArray) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2112 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∃ v, Model.FastRepresents (r4RunMem k mem) 2368 4 v ∧ v < Limbs.radix^4 ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^4) x x)^[k] a) := by
  obtain ⟨v, hv, hvr, hvm, h0⟩ := r4Steps_represents mm hodd k mem a hk ha hm hminv
  refine ⟨v, ?_, hvr, hvm⟩
  unfold r4RunMem LazyCsub.resultMemory
  rw [h0, if_pos (show (⟨0⟩ : UInt256).toNat = 0 from rfl)]
  exact Csub.fastRepresents_mcopy _ 2112 2368 4 v (by omega) hv

theorem r4LoopMem_represents (s : State) (mem : ByteArray) (a mm k : Nat) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2112 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (_har : a < Limbs.radix^4) (_hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∃ v, Model.FastRepresents (r4LoopMem s k mem) 2368 4 v ∧ v < Limbs.radix^4 ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^4) x x)^[k] a) := by
  cases k with
  | zero => omega
  | succ k =>
      have hrd (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2240 ≤ addr) :
          MachineState.readWord (SquarePartialClear.memory (stageW mem 2112 4)) addr =
            MachineState.readWord mem addr := by
        rw [SquarePartialClear.readWord_outside _ addr (by omega),
          read_stageW_four_outside mem addr (by omega)]
      have ha' : Model.FastRepresents (SquarePartialClear.memory (stageW mem 2112 4)) 2112 4 a :=
        SquarePartialClear.fastRepresents_outside _ 2112 4 a (Or.inr (by omega))
          (represents_stageW_four mem 2112 4 a (Or.inr (Or.inr ⟨rfl, le_rfl⟩)) ha)
      have hm' : Model.FastRepresents (SquarePartialClear.memory (stageW mem 2112 4)) 0 4 mm := by
        refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
        intro j hj
        rw [hrd (0 + 32 * j) (Or.inl (by omega))]
      have hminv' : ((MachineState.readWord (SquarePartialClear.memory (stageW mem 2112 4)) 96).toNat *
          (MachineState.readWord (SquarePartialClear.memory (stageW mem 2112 4)) 2720).toNat + 1) %
            2 ^ 256 = 0 := by
        rw [hrd 96 (Or.inl (by norm_num)), hrd 2720 (Or.inr (by norm_num))]
        exact hminv
      rw [r4LoopMem_succ]
      exact r4RunMem_represents a mm (k + 1) _ (by omega) ha' hm' hodd hminv'

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
    (ha : Model.FastRepresents mem 2112 (p + 2) a)
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
