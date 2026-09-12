import Challenge.Modexp.Submission.Proofs.Fast.SquareModel
import Challenge.Modexp.Submission.Proofs.Fast.CarryResult

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The machine-carry square rows and the square subroutine's result memory

The kernel keeps the row overflow on the stack (`CarryRowModel` style) instead of
storing it at `T_ = 2048`.  `sqRowsCarry` is that machine model; it agrees with
the Monpro-style `sqRowsMem` everywhere except the scratch word `[2048, 2080)`.

`sqMem s mem n` is the memory a whole `SQUARE(512) → 512` call leaves behind:
for `n ∈ {4, 8}` the square rows followed by the conditional subtraction, and for
other widths the generic `MONPRO(512, 512) → 512` fallback.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareResult

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel CarryScratchAgreement StagedOperand SquareModel

/-! ## The machine-carry row on a first-loop result -/

/-- The second limb loop of the machine-carry row on a first-loop result `q`. -/
def rowFromL2Carry (q : MacState) (n : Nat) : MacState :=
  l2Step (midMem1 q.memory q.carry) (rowMu q.memory n) (rowC0 q.memory n) n (n - 1)

/-- Middle, second loop and tail of the machine-carry row (overflow on the stack). -/
def rowFromCarry (q : MacState) (n : Nat) : ByteArray :=
  tailCarry (rowFromL2Carry q n).memory (rowFromL2Carry q n).carry (overflow q.memory q.carry)

theorem rowCarry_eq_rowFromCarry (mem : ByteArray) (pa pb n i : Nat) :
    rowCarry mem pa pb n i = rowFromCarry (rowL1 mem pa pb n i) n := rfl

theorem rowL2Carry_eq (mem : ByteArray) (pa pb n i : Nat) :
    rowL2Carry mem pa pb n i = rowFromL2Carry (rowL1 mem pa pb n i) n := rfl

/-- Memory after machine-carry square row `i` with carried top bit `tb`. -/
def sqRowCarry (mem : ByteArray) (n i : Nat) (tb : UInt256) : ByteArray :=
  rowFromCarry (sqL1 mem n i tb) n

/-- Memory after `i` machine-carry square rows. -/
def sqRowsCarry (mem : ByteArray) (n : Nat) : Nat → ByteArray
  | 0 => mem
  | i + 1 => sqRowCarry (sqRowsCarry mem n i) n i (sqTb (sqRowsCarry mem n i) n i)

theorem sqRowsCarry_zero (mem : ByteArray) (n : Nat) : sqRowsCarry mem n 0 = mem := rfl

theorem sqRowsCarry_succ (mem : ByteArray) (n i : Nat) :
    sqRowsCarry mem n (i + 1) =
      sqRowCarry (sqRowsCarry mem n i) n i (sqTb (sqRowsCarry mem n i) n i) := rfl

/-! ## Agreement with the Monpro-style model -/

theorem rowFrom_agree (a b : MacState) (h : Agree a.memory b.memory) (hc : a.carry = b.carry)
    (n : Nat) (hn32 : n ≤ 32) :
    Agree (rowFromCarry a n) (rowFrom b n) := by
  have hm := middle_agree a.memory b.memory h b.carry
  have hmu := rowMu_eq a.memory b.memory h n
  have hc0 := rowC0_eq a.memory b.memory h n hn32
  have hflag := overflow_eq a.memory b.memory h b.carry
  have hl2 := l2_agree _ _ hm (rowMu b.memory n) (rowC0 b.memory n) n (n - 1) hn32
  have hf : MachineState.readWord (rowFromL2 b n).memory 2048 = overflow b.memory b.carry := by
    unfold rowFromL2 rowFromMid
    rw [readWord_l2Step_low _ _ _ n 2048 (n - 1) (by decide), readWord_midMem_tnp]
    rfl
  unfold rowFromCarry rowFromL2Carry rowFrom rowFromL2 rowFromMid
  rw [hc, hmu, hc0, hflag, hl2.2]
  exact tail_agree _ _ hl2.1 _ _ hf

theorem l1Run_agree (qa qb : MacState) (h : Agree qa.memory qb.memory) (hc : qa.carry = qb.carry)
    (bi : UInt256) (pa n j0 : Nat) (hpa : pa + 32 * n ≤ 2048) :
    ∀ k, j0 + k ≤ n →
      Agree (l1Run qa bi pa n j0 k).memory (l1Run qb bi pa n j0 k).memory ∧
        (l1Run qa bi pa n j0 k).carry = (l1Run qb bi pa n j0 k).carry := by
  intro k
  induction k with
  | zero => intro _; exact ⟨h, hc⟩
  | succ k ih =>
      intro hk
      have prev := ih (by omega)
      have hx := readWord_eq prev.1 (pa + 32 * (n - 1 - (j0 + k))) (Or.inl (by omega))
      have ht := readWord_eq prev.1 (2112 + 32 * (n - 1 - (j0 + k))) (Or.inr (by omega))
      simp only [l1Run_succ, l1StepOn, hx, ht, prev.2]
      constructor
      · exact write_same prev.1 _ _
      · trivial

theorem sqPro_agree (a b : ByteArray) (h : Agree a b) (n i : Nat) (tb : UInt256)
    (hn : n ≤ 32) :
    Agree (sqPro a n i tb).memory (sqPro b n i tb).memory ∧
      (sqPro a n i tb).carry = (sqPro b n i tb).carry := by
  have hx : sqX a n i = sqX b n i := readWord_eq h (aAddr n i) (Or.inl (by unfold aAddr; omega))
  have ht := readWord_eq h (tAddr n i) (Or.inr (by unfold tAddr; omega))
  have hs : sqSum a n i tb = sqSum b n i tb := by unfold sqSum; rw [hx, ht]
  have hcar : sqCarry a n i tb = sqCarry b n i tb := by unfold sqCarry; rw [hs, hx]
  refine ⟨?_, hcar⟩
  show Agree (MachineState.writeBytes a (Data.Bytes.natToBytesPadded (sqSum a n i tb).toNat 32)
      (tAddr n i)) (MachineState.writeBytes b (Data.Bytes.natToBytesPadded (sqSum b n i tb).toNat 32)
      (tAddr n i))
  rw [hs]
  exact write_same h _ _

theorem sqL1_agree (a b : ByteArray) (h : Agree a b) (n i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 32) :
    Agree (sqL1 a n i tb).memory (sqL1 b n i tb).memory ∧
      (sqL1 a n i tb).carry = (sqL1 b n i tb).carry := by
  have hx : sqX a n i = sqX b n i := readWord_eq h (aAddr n i) (Or.inl (by unfold aAddr; omega))
  have hp := sqPro_agree a b h n i tb hn
  unfold sqL1
  rw [hx]
  exact l1Run_agree _ _ hp.1 hp.2 _ 512 n (i + 1) (by omega) (n - 1 - i) (by omega)

theorem sqTb_eq (a b : ByteArray) (h : Agree a b) (n i : Nat) (hn : n ≤ 32) :
    sqTb a n i = sqTb b n i := by
  cases i with
  | zero => rfl
  | succ i =>
      show UInt256.sgt (UInt256.ofNat 0) (MachineState.readWord a (aAddr n i)) =
        UInt256.sgt (UInt256.ofNat 0) (MachineState.readWord b (aAddr n i))
      rw [readWord_eq h (aAddr n i) (Or.inl (by unfold aAddr; omega))]

theorem sqRow_agree (a b : ByteArray) (h : Agree a b) (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    Agree (sqRowCarry a n i (sqTb a n i)) (sqRowMem b n i (sqTb b n i)) := by
  rw [sqTb_eq a b h n i hn]
  have hl := sqL1_agree a b h n i (sqTb b n i) hi hn
  exact rowFrom_agree _ _ hl.1 hl.2 n hn

/-- The machine-carry square rows agree with the Monpro-style ones outside `T_`. -/
theorem sqRows_agree (mem : ByteArray) (n : Nat) (hn : n ≤ 32) :
    ∀ i, i ≤ n → Agree (sqRowsCarry mem n i) (sqRowsMem mem n i) := by
  intro i
  induction i with
  | zero => intro _; exact refl mem
  | succ i ih =>
      intro hi
      exact sqRow_agree _ _ (ih (by omega)) n i (by omega) hn

/-! ## Where the machine-carry rows write -/

/-- One 32-byte store at `dst ∈ [2048, 2112 + 32 n)` leaves every word outside
that region alone. -/
theorem readWord_store_far (mem : ByteArray) (w dst n addr : Nat)
    (hdst : 2048 ≤ dst) (hdstHi : dst + 32 ≤ 2112 + 32 * n)
    (haddr : addr + 32 ≤ 2048 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) dst) addr =
      MachineState.readWord mem addr :=
  readWord_storeWord_outside mem w dst addr (by omega)

theorem readWord_l2Step_far (mem : ByteArray) (mu c0 : UInt256) (n addr : Nat) (hn : 1 ≤ n)
    (haddr : addr + 32 ≤ 2048 ∨ 2112 + 32 * n ≤ addr) :
    ∀ k, MachineState.readWord (l2Step mem mu c0 n k).memory addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [l2Step]
      rw [readWord_store_far _ _ (2112 + 32 * (n - 1 - k)) n addr (by omega) (by omega) haddr]
      exact ih

theorem readWord_rowFromCarry_far (q : MacState) (n addr : Nat) (hn : 1 ≤ n)
    (haddr : addr + 32 ≤ 2048 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (rowFromCarry q n) addr = MachineState.readWord q.memory addr := by
  unfold rowFromCarry rowFromL2Carry tailCarry tailMem1 midMem1
  rw [readWord_store_far _ _ 2080 n addr (by omega) (by omega) haddr,
    readWord_store_far _ _ 2112 n addr (by omega) (by omega) haddr,
    readWord_l2Step_far _ _ _ n addr hn haddr (n - 1),
    readWord_store_far _ _ 2080 n addr (by omega) (by omega) haddr]

theorem readWord_sqRowCarry_far (mem : ByteArray) (n i addr : Nat) (tb : UInt256) (hi : i < n)
    (haddr : addr + 32 ≤ 2048 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (sqRowCarry mem n i tb) addr = MachineState.readWord mem addr := by
  unfold sqRowCarry
  rw [readWord_rowFromCarry_far _ n addr (by omega) haddr,
    readWord_sqL1 mem n i addr tb hi (by omega)]

/-- The machine-carry square rows write only inside `[2048, 2112 + 32 n)`. -/
theorem readWord_sqRowsCarry_far (mem : ByteArray) (n addr : Nat)
    (haddr : addr + 32 ≤ 2048 ∨ 2112 + 32 * n ≤ addr) :
    ∀ i, i ≤ n → MachineState.readWord (sqRowsCarry mem n i) addr = MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      rw [sqRowsCarry_succ,
        readWord_sqRowCarry_far (sqRowsCarry mem n i) n i addr _ (by omega) haddr]
      exact ih (by omega)

/-- The machine-carry square rows write only inside `[2048, 2720)`. -/
theorem readWord_sqRowsCarry (mem : ByteArray) (n addr : Nat) (hn : n ≤ 32)
    (haddr : addr + 32 ≤ 2048 ∨ 2720 ≤ addr) (i : Nat) (hi : i ≤ n) :
    MachineState.readWord (sqRowsCarry mem n i) addr = MachineState.readWord mem addr :=
  readWord_sqRowsCarry_far mem n addr (by omega) i hi

/-- The top bit fed into row `i + 1` is `SGT 0 x_i`, with `x_i` the limb row `i` read. -/
theorem sqTb_succ_carry (mem : ByteArray) (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    sqTb (sqRowsCarry mem n (i + 1)) n (i + 1) =
      UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry mem n i) n i) := by
  show UInt256.sgt (UInt256.ofNat 0) (MachineState.readWord (sqRowsCarry mem n (i + 1)) (aAddr n i)) =
    UInt256.sgt (UInt256.ofNat 0) (MachineState.readWord (sqRowsCarry mem n i) (aAddr n i))
  rw [sqRowsCarry_succ,
    readWord_sqRowCarry_far _ n i (aAddr n i) _ hi (Or.inl (by unfold aAddr; omega))]

/-! ## The square rows' value, machine-carry form -/

/-- The top limb of the final machine-carry accumulator is at most one. -/
theorem sqRowsCarry_tn_le_one (m0 : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 32)
    (ha : Model.FastRepresents m0 512 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 2816).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue m0 (p + 2) = 0) (ham : a < mm) :
    (MachineState.readWord (sqRowsCarry m0 (p + 2) (p + 2)) 2080).toNat ≤ 1 := by
  rw [readWord_eq (sqRows_agree m0 (p + 2) hn32 (p + 2) le_rfl) 2080 (Or.inr (by decide))]
  exact sqRows_tn_le_one m0 p a mm hn32 ha hm hminv hz ham

theorem sqRowsCarry_represents (m0 : ByteArray) (p a mm pdst : Nat) (hn32 : p + 2 ≤ 32)
    (hpd : pdst + 32 * (p + 2) ≤ 2048)
    (ha : Model.FastRepresents m0 512 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 2816).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue m0 (p + 2) = 0) :
    Model.FastRepresents (Csub.csResultMemory (sqRowsCarry m0 (p + 2) (p + 2)) (p + 2) pdst)
      pdst (p + 2) (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) := by
  have hrow := sqRows_agree m0 (p + 2) hn32 (p + 2) le_rfl
  have htn := sqRows_tn_le_one m0 p a mm hn32 ha hm hminv hz ham
  have hres := csResult_agree _ _ hrow (p + 2) pdst (by omega) hn32 htn
  have hrep := sqRows_represents m0 p a mm pdst hn32 ha hm hodd ham hminv hz
  exact (fastRepresents_iff _ _ hres pdst (p + 2) _ (Or.inl hpd)).2 hrep

/-! ## The square subroutine's result memory -/

/-- The memory a whole `SQUARE(512) → 512` call leaves behind. -/
def sqMem (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  if n = 4 ∨ n = 8 then
    Csub.csResultMemory (sqRowsCarry (mpZeroed s (inputMemory mem 512 n) n) n n) n 512
  else CarryResult.monproMem s mem 512 512 n 512

theorem sqMem_of_fast (s : State) (mem : ByteArray) (n : Nat) (h : n = 4 ∨ n = 8) :
    sqMem s mem n =
      Csub.csResultMemory (sqRowsCarry (mpZeroed s (inputMemory mem 512 n) n) n n) n 512 := by
  unfold sqMem
  rw [if_pos h]

theorem sqMem_of_not_fast (s : State) (mem : ByteArray) (n : Nat) (h : ¬(n = 4 ∨ n = 8)) :
    sqMem s mem n = Monpro.monproMem s mem 512 512 n 512 := by
  unfold sqMem CarryResult.monproMem CarryResult.selectedRows inputMemory Monpro.monproMem
  rw [if_neg h, if_neg h, if_neg h]

/-- The fast-path call ends with exactly this memory (the `CSUB` return state). -/
theorem csReturnedState_memory_sqMem (s : State) (mem : ByteArray) (n : Nat) (h : n = 4 ∨ n = 8)
    (ret : UInt256) (rest : List UInt256) :
    (Csub.csReturnedState s (sqRowsCarry (mpZeroed s (inputMemory mem 512 n) n) n n) n n
      (UInt256.ofNat 512) ret rest).memory = sqMem s mem n := by
  rw [Csub.csReturnedState_memory, sqMem_of_fast s mem n h]
  rfl

/-- `SQUARE(512) → 512` writes the Montgomery square `a · a · R⁻¹ mod m`. -/
theorem sqMem_represents (s : State) (mem : ByteArray) (p a mm : Nat)
    (hn32 : p + 2 ≤ 32)
    (ha : Model.FastRepresents mem 512 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2816).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqMem s mem (p + 2)) 512 (p + 2)
      (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) := by
  unfold sqMem
  split
  · let prepared := inputMemory mem 512 (p + 2)
    have ha' : Model.FastRepresents prepared 512 (p + 2) a :=
      (fastRepresents_inputMemory mem 512 (p + 2) 512 (p + 2) a (by omega)).2 ha
    have hm' : Model.FastRepresents prepared 0 (p + 2) mm :=
      (fastRepresents_inputMemory mem 512 (p + 2) 0 (p + 2) mm (by omega)).2 hm
    have hminv' : ((MachineState.readWord prepared (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord prepared 2816).toNat + 1) % 2 ^ 256 = 0 := by
      simpa only [prepared,
        read_inputMemory_outside mem 512 (p + 2) (32 * (p + 2) - 32) (Or.inl (by omega)),
        read_inputMemory_outside mem 512 (p + 2) 2816 (Or.inr (by decide))] using hminv
    have ha0 : Model.FastRepresents (mpZeroed s prepared (p + 2)) 512 (p + 2) a := by
      refine (Model.fastRepresents_congr (a := prepared) ?_ a).1 ha'
      intro j hj
      rw [readWord_mpZeroed s prepared (p + 2) (512 + 32 * j) hn32 (Or.inl (by omega))]
    have hm0 : Model.FastRepresents (mpZeroed s prepared (p + 2)) 0 (p + 2) mm := by
      refine (Model.fastRepresents_congr (a := prepared) ?_ mm).1 hm'
      intro j hj
      rw [readWord_mpZeroed s prepared (p + 2) (0 + 32 * j) hn32 (Or.inl (by omega))]
    have hminv0 : ((MachineState.readWord (mpZeroed s prepared (p + 2)) (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord (mpZeroed s prepared (p + 2)) 2816).toNat + 1) % 2 ^ 256 = 0 := by
      rw [readWord_mpZeroed s prepared (p + 2) (32 * (p + 2) - 32) hn32 (Or.inl (by omega)),
        readWord_mpZeroed s prepared (p + 2) 2816 hn32 (Or.inr (by omega))]
      exact hminv'
    exact sqRowsCarry_represents (mpZeroed s prepared (p + 2)) p a mm 512 hn32 (by omega)
      ha0 hm0 hodd ham hminv0 (tValue_mpZeroed s prepared (p + 2))
  · exact CarryResult.monproMem_represents s mem 512 512 p 512 a a mm hn32
      (by omega) (by omega) (by omega) ha ha hm hodd ham hminv

/-- Every word outside `SUBB`, outside the CIOS scratch `[2048, 2720)` and
outside the operand/destination block at `512` survives a `SQUARE` call. -/
theorem sqMem_readWord_outside (s : State) (mem : ByteArray) (n addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2720 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr) :
    MachineState.readWord (sqMem s mem n) addr = MachineState.readWord mem addr := by
  unfold sqMem
  split
  · rw [csResultMemory_readWord_outside _ n 512 addr hn hsubb hdst,
      readWord_sqRowsCarry _ n addr hn32 hscratch n le_rfl,
      readWord_mpZeroed s _ n addr hn32 hscratch,
      read_inputMemory_outside mem 512 n addr hscratch]
  · exact CarryResult.monproMem_readWord_outside s mem 512 512 n 512 addr hn hn32
      hsubb hscratch hdst

/-- Everything at or above `2720` survives a `SQUARE` call. -/
theorem sqMem_readWord_high (s : State) (mem : ByteArray) (n addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (haddr : 2720 ≤ addr) :
    MachineState.readWord (sqMem s mem n) addr = MachineState.readWord mem addr :=
  sqMem_readWord_outside s mem n addr hn hn32 (Or.inr (by omega)) (Or.inr haddr)
    (Or.inr (by omega))

/-- The five configuration words `V_S32`, `V_MINV`, `V_ML`, `V_TL`, `V_EOFF`
are unchanged by a `SQUARE` call. -/
theorem sqMem_frame (s : State) (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    MachineState.readWord (sqMem s mem n) 2784 = MachineState.readWord mem 2784 ∧
      MachineState.readWord (sqMem s mem n) 2816 = MachineState.readWord mem 2816 ∧
      MachineState.readWord (sqMem s mem n) 2848 = MachineState.readWord mem 2848 ∧
      MachineState.readWord (sqMem s mem n) 2880 = MachineState.readWord mem 2880 ∧
      MachineState.readWord (sqMem s mem n) 2912 = MachineState.readWord mem 2912 :=
  ⟨sqMem_readWord_high s mem n 2784 hn hn32 (by omega),
   sqMem_readWord_high s mem n 2816 hn hn32 (by omega),
   sqMem_readWord_high s mem n 2848 hn hn32 (by omega),
   sqMem_readWord_high s mem n 2880 hn hn32 (by omega),
   sqMem_readWord_high s mem n 2912 hn hn32 (by omega)⟩

/-- Every represented block disjoint from `SUBB`, from the CIOS scratch and from
the block at `512` survives a `SQUARE` call. -/
theorem sqMem_fastRepresents_outside (s : State) (mem : ByteArray)
    (n ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2720 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqMem s mem n) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) (b := sqMem s mem n) ?_ v).1 hrep
  intro j hj
  exact (sqMem_readWord_outside s mem n (ptr + 32 * j) hn hn32
    (by omega) (by omega) (by omega)).symm

end Challenge.Modexp.Submission.Proofs.Fast.SquareResult

/-! ## Operand snapshot preservation (staged reads of the chain)

Stated in `StagedOperand` so that dot notation `h.sqRowsCarry …` works on a
`StagedOperand.Snapshot` hypothesis. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult


theorem Snapshot.of_far {mem mem' : ByteArray} {pa n : Nat} (h : Snapshot mem pa n)
    (hn : n ≤ 8) (hpa : pa + 32 * n ≤ 2048)
    (hpres : ∀ addr, (addr + 32 ≤ 2048 ∨ 2112 + 32 * n ≤ addr) →
      MachineState.readWord mem' addr = MachineState.readWord mem addr) :
    Snapshot mem' pa n := by
  intro k hk
  rw [hpres (2400 + 32 * k) (Or.inr (by omega)), hpres (pa + 32 * k) (Or.inl (by omega))]
  exact h k hk

theorem Snapshot.sqPro {mem : ByteArray} {n : Nat} (h : Snapshot mem 512 n) (i : Nat)
    (tb : UInt256) (hi : i < n) (hn : n ≤ 8) :
    Snapshot (SquareModel.sqPro mem n i tb).memory 512 n :=
  h.of_far hn (by omega) (fun addr haddr => readWord_sqPro mem n i addr tb hi (by omega))

theorem Snapshot.l1Run {q : MacState} {n : Nat} (h : Snapshot q.memory 512 n) (bi : UInt256)
    (j0 k : Nat) (hk : j0 + k ≤ n) (hn : n ≤ 8) :
    Snapshot (SquareModel.l1Run q bi 512 n j0 k).memory 512 n :=
  h.of_far hn (by omega) (fun addr haddr => readWord_l1Run q bi 512 n j0 addr (by omega) k hk)

theorem Snapshot.sqL1 {mem : ByteArray} {n : Nat} (h : Snapshot mem 512 n) (i : Nat)
    (tb : UInt256) (hi : i < n) (hn : n ≤ 8) :
    Snapshot (SquareModel.sqL1 mem n i tb).memory 512 n :=
  h.of_far hn (by omega) (fun addr haddr => readWord_sqL1 mem n i addr tb hi (by omega))

theorem Snapshot.sqRowCarry {mem : ByteArray} {n : Nat} (h : Snapshot mem 512 n) (i : Nat)
    (tb : UInt256) (hi : i < n) (hn : n ≤ 8) :
    Snapshot (SquareResult.sqRowCarry mem n i tb) 512 n :=
  h.of_far hn (by omega) (fun addr haddr => readWord_sqRowCarry_far mem n i addr tb hi haddr)

theorem Snapshot.sqRowsCarry {mem : ByteArray} {n : Nat} (h : Snapshot mem 512 n) (i : Nat)
    (hi : i ≤ n) (hn : n ≤ 8) :
    Snapshot (SquareResult.sqRowsCarry mem n i) 512 n :=
  h.of_far hn (by omega) (fun addr haddr => readWord_sqRowsCarry_far mem n addr haddr i hi)

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
