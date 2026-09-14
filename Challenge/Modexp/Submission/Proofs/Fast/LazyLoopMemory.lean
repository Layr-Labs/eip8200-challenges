import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyLoopMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult SquareLoopBlocks

def rows (s : State) (n : Nat) (mem : ByteArray) : ByteArray :=
  if n = 4 then R4Bridge.rows4 mem else sqRowsCarry (mpZeroed s mem n) n n

def round (s : State) (n c : Nat) (mem : ByteArray) : ByteArray :=
  LazyCsub.resultMemory (countMem (rows s n mem) c) n 2368

def run (s : State) (n : Nat) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k+1, mem => run s n k (round s n k mem)

theorem rows_read_word (s : State) (mem : ByteArray) (n addr : Nat) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2624 ≤ addr) :
    MachineState.readWord (rows s n mem) addr = MachineState.readWord mem addr := by
  unfold rows
  split
  · exact R4Bridge.rows4_readWord_outside mem addr (by omega)
  · rw [readWord_sqRowsCarry _ n addr hn hout n le_rfl, readWord_mpZeroed s mem n addr hn hout]

theorem round_read_word (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hout : addr+32 ≤ 1792 ∨ 2656 ≤ addr) :
    MachineState.readWord (round s n c mem) addr = MachineState.readWord mem addr := by
  unfold round
  rw [LazyCsub.result_readWord_outside _ n 2368 addr (by omega) (by omega) (by omega),
    readWord_countMem_disjoint _ c addr (by omega), rows_read_word s mem n addr hn32 (by omega)]

theorem round_preserves (s : State) (mem : ByteArray) (n c ptr cnt v : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hout : ptr+32*cnt ≤ 1792 ∨ 2656 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (round s n c mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) (b := round s n c mem)
    (ptr := ptr) (count := cnt) ?_ v).1 hrep
  intro j hj
  exact (round_read_word s mem n c (ptr+32*j) hn hn32 (by omega)).symm

theorem rows_equation (s : State) (mem : ByteArray) (p a mm : Nat)
    (hn : p+2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    ∃ Q, Q < Limbs.radix^(p+2) ∧
      tValue (rows s (p+2) mem) (p+2) * Limbs.radix^(p+2) = a*a + Q*mm := by
  by_cases h4 : p+2 = 4
  · obtain ⟨Q, hQ, heq⟩ := R4Bridge.rows4_eq mem a mm
      (by simpa only [h4] using ha) (by simpa only [h4] using hm)
      (by simpa only [h4] using hminv)
    refine ⟨Q, by simpa only [h4] using hQ, ?_⟩
    rw [rows, if_pos h4, h4]
    exact heq
  · have ha' := represents_zeroed_stage s mem (p+2) a hn ha
    have hm' : Model.FastRepresents (mpZeroed s mem (p+2)) 0 (p+2) mm := by
      refine (Model.fastRepresents_congr (a := mem) (b := mpZeroed s mem (p+2)) ?_ mm).1 hm
      intro j hj
      rw [readWord_mpZeroed s mem (p+2) (0+32*j) hn (Or.inl (by omega))]
    have hi' : ((MachineState.readWord (mpZeroed s mem (p+2)) (32*(p+2)-32)).toNat *
        (MachineState.readWord (mpZeroed s mem (p+2)) 2720).toNat + 1) % 2^256 = 0 := by
      rw [readWord_mpZeroed s mem (p+2) (32*(p+2)-32) hn (Or.inl (by omega)),
        readWord_mpZeroed s mem (p+2) 2720 hn (Or.inr (by omega))]
      exact hminv
    obtain ⟨Q, hQ, heq, _, _⟩ := LazyBounds.current_sqRows_lazy (mpZeroed s mem (p+2))
      p a mm hn ha' hm' (by omega) hi' (tValue_mpZeroed s mem (p+2))
    refine ⟨Q, hQ, ?_⟩
    rw [rows, if_neg h4, LazySquareMemory.carry_accumulator _ (p+2) hn]
    exact heq

theorem round_represents (s : State) (mem : ByteArray) (p a mm c : Nat)
    (hn : p+2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    ∃ v, Model.FastRepresents (round s (p+2) c mem) 2368 (p+2) v ∧
      v < Limbs.radix^(p+2) ∧ v % mm = Model.montMul mm (Limbs.radix^(p+2)) a a := by
  obtain ⟨Q, hQ, heq⟩ := rows_equation s mem p a mm hn ha hm hodd hminv
  let after := countMem (rows s (p+2) mem) c
  have hm' : Model.FastRepresents after 0 (p+2) mm := by
    refine (Model.fastRepresents_congr (a := mem) (b := after) ?_ mm).1 hm
    intro j hj
    dsimp only [after]
    rw [readWord_countMem_disjoint _ c (0+32*j) (by omega),
      rows_read_word s mem (p+2) (0+32*j) hn (Or.inl (by omega))]
  have heq' : tValue after (p+2) * Limbs.radix^(p+2) = a*a+Q*mm := by
    dsimp only [after]
    rw [LazySquareMemory.count_accumulator _ (p+2) c hn]
    exact heq
  rw [round]
  exact ⟨LazySquareMemory.roundValue after (p+2) mm,
    LazySquareMemory.result_from_square_equation after (p+2) a mm Q 2368 (by omega) hn ha.1 hm' hodd hQ heq'⟩

theorem run_read_word (s : State) (mem : ByteArray) (n k addr : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hout : addr+32 ≤ 1792 ∨ 2656 ≤ addr) :
    MachineState.readWord (run s n k mem) addr = MachineState.readWord mem addr := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [run, ih, round_read_word s mem n k addr hn hn32 hout]

theorem run_preserves (s : State) (mem : ByteArray) (n k ptr cnt v : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hout : ptr+32*cnt ≤ 1792 ∨ 2656 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (run s n k mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) (b := run s n k mem)
    (ptr := ptr) (count := cnt) ?_ v).1 hrep
  intro j hj
  exact (run_read_word s mem n k (ptr+32*j) hn hn32 (by omega)).symm

theorem mont_square_congr (mm R a b : Nat) (h : a % mm = b % mm) :
    Model.montMul mm R a a = Model.montMul mm R b b := by
  have hc : (a : ZMod mm) = (b : ZMod mm) :=
    (ZMod.natCast_eq_natCast_iff a b mm).2 h
  unfold Model.montMul
  rw [hc]

theorem run_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (hn : p+2 ≤ 8) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    ∃ v, Model.FastRepresents (run s (p+2) k mem) 2368 (p+2) v ∧
      v < Limbs.radix^(p+2) ∧
      v % mm = ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) := by
  induction k generalizing mem a with
  | zero => omega
  | succ k ih =>
      rw [run]
      obtain ⟨v, hv, hvr, hvm⟩ := round_represents s mem p a mm k hn ha hm hodd hminv
      cases k with
      | zero =>
          exact ⟨v, hv, hvr, hvm⟩
      | succ j =>
          have hm' := round_preserves s mem (p+2) (j+1) 0 (p+2) mm (by omega) hn (Or.inl (by omega)) hm
          have hi' : ((MachineState.readWord (round s (p+2) (j+1) mem) (32*(p+2)-32)).toNat *
              (MachineState.readWord (round s (p+2) (j+1) mem) 2720).toNat + 1) % 2^256 = 0 := by
            rw [round_read_word s mem (p+2) (j+1) (32*(p+2)-32) (by omega) hn (Or.inl (by omega)),
              round_read_word s mem (p+2) (j+1) 2720 (by omega) hn (Or.inr (by omega))]
            exact hminv
          obtain ⟨w, hw, hwr, hwm⟩ := ih (round s (p+2) (j+1) mem) v (by omega) hv hm' hi'
          refine ⟨w, hw, hwr, ?_⟩
          rw [hwm]
          have hf := mont_square_congr mm (Limbs.radix^(p+2)) v
            (Model.montMul mm (Limbs.radix^(p+2)) a a)
            (by rw [hvm, Nat.mod_eq_of_lt (Model.montMul_lt (by omega) _ _ _)])
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          exact congrArg ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[j]) hf

end Challenge.Modexp.Submission.Proofs.Fast.LazyLoopMemory
