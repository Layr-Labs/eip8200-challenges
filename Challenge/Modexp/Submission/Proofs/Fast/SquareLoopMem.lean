import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The memory model of the in-kernel squaring loop

One round of the loop is one square plus the counter store that `sq_exit` performs between
the rows and the final conditional subtraction:

    sqRound s n c mem
      = CSUB (2624 := c) (rows (re-stage, re-zero) mem)

`SquareResult.sqMem s mem n` is the same composition **without** the counter store, so the
two memories agree everywhere except the CIOS top word `[2048, 2080)` (where the machine
model already differs from the Monpro-style one) and the counter word `[2624, 2656)`.
`CountAgree` is that agreement relation; it transports `SquareResult`'s value and
preservation lemmas onto every round, so the loop needs no new arithmetic.

`sqLoopMem s n k mem` is the memory after the `k` squares of a call whose counter word
holds `k`: each round stores the decremented counter, so the last one stores zero.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel StagedOperand SquareModel SquareResult

/-! ## Agreement outside the CIOS top word and the counter word -/

namespace CountAgree

/-- Byte agreement outside `[2048, 2080)` (the machine model's scratch word) and outside
`[2624, 2656)` (the squaring counter). -/
def Agree (a b : ByteArray) : Prop :=
  ∀ i, i < 2048 ∨ (2080 ≤ i ∧ i < 2624) ∨ 2656 ≤ i → a[i]?.getD 0 = b[i]?.getD 0

theorem refl (a : ByteArray) : Agree a a := fun _ _ => rfl

theorem symm {a b : ByteArray} (h : Agree a b) : Agree b a := fun i hi => (h i hi).symm

theorem trans {a b c : ByteArray} (hab : Agree a b) (hbc : Agree b c) : Agree a c :=
  fun i hi => (hab i hi).trans (hbc i hi)

/-- The scratch agreement of `CarryScratchAgreement` is stronger. -/
theorem of_scratch {a b : ByteArray} (h : CarryScratchAgreement.Agree a b) : Agree a b :=
  fun i hi => h i (by omega)

/-- Storing the counter at 2624 changes nothing that `Agree` sees. -/
theorem countMem_agree (a : ByteArray) (c : Nat) :
    Agree (SquareLoopBlocks.countMem a c) a := by
  intro i hi
  rw [SquareLoopBlocks.countMem, MachineState.writeBytes_getElem?_getD, if_neg]
  intro h
  rw [show (Data.Bytes.natToBytesPadded c 32).size = 32 by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]] at h
  omega

theorem readPadded_eq {a b : ByteArray} (h : Agree a b) (start count : Nat)
    (hout : start + count ≤ 2048 ∨ (2080 ≤ start ∧ start + count ≤ 2624) ∨ 2656 ≤ start) :
    MachineState.readPadded a start count = MachineState.readPadded b start count := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  exact h (start + i) (by omega)

theorem readWord_eq {a b : ByteArray} (h : Agree a b) (start : Nat)
    (hout : start + 32 ≤ 2048 ∨ (2080 ≤ start ∧ start + 32 ≤ 2624) ∨ 2656 ≤ start) :
    MachineState.readWord a start = MachineState.readWord b start := by
  unfold MachineState.readWord
  rw [readPadded_eq h start 32 hout]

theorem write_same {a b : ByteArray} (h : Agree a b) (bytes : ByteArray) (start : Nat) :
    Agree (MachineState.writeBytes a bytes start) (MachineState.writeBytes b bytes start) := by
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD]
  split
  · rfl
  · exact h i hi

theorem csStep_agree (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 8) :
    Agree (Csub.csStep a n j).memory (Csub.csStep b n j).memory ∧
      (Csub.csStep a n j).flag = (Csub.csStep b n j).flag := by
  induction j with
  | zero => exact ⟨h, rfl⟩
  | succ j ih =>
    have ht := readWord_eq ih.1 (2112 + 32 * (n - 1 - j)) (Or.inr (Or.inl (by omega)))
    have hm := readWord_eq ih.1 (32 * (n - 1 - j)) (Or.inl (by omega))
    simp only [Csub.csStep, ht, hm, ih.2]
    exact ⟨write_same ih.1 _ _, True.intro⟩

theorem csUse_eq (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 8) :
    Csub.csUse a n j = Csub.csUse b n j := by
  have hs := csStep_agree a b h n j hn
  simp only [Csub.csUse, hs.2, readWord_eq hs.1 2080 (Or.inr (Or.inl (by decide)))]

theorem csSrc_eq (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 8) :
    Csub.csSrc a n j = Csub.csSrc b n j := by
  unfold Csub.csSrc
  rw [csUse_eq a b h n j hn]

theorem csResult_agree (a b : ByteArray) (h : Agree a b) (n dst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (htn : (MachineState.readWord b 2080).toNat ≤ 1) :
    Agree (Csub.csResultMemory a n dst) (Csub.csResultMemory b n dst) := by
  have hg : EarlyCsub.Skip a = EarlyCsub.Skip b := by
    unfold EarlyCsub.Skip EarlyCsub.guardWord
    rw [readWord_eq h 2080 (Or.inr (Or.inl (by decide))),
      readWord_eq h 2112 (Or.inr (Or.inl (by decide))), readWord_eq h 0 (Or.inl (by decide))]
  simp only [Csub.csResultMemory, hg]
  split
  · rw [readPadded_eq h 2112 (32 * n) (Or.inr (Or.inl (by omega)))]
    exact write_same h _ _
  ·
    have hs := csStep_agree a b h n n hn32
    have htn' : (MachineState.readWord (Csub.csStep b n n).memory 2080).toNat ≤ 1 := by
      rw [Csub.csStep_readWord_disjoint b n 2080 hn (Or.inr (by omega)) n le_rfl]
      exact htn
    have hsrc := Csub.csSrc_toNat b n n (Csub.csUse_le_one b n n htn')
    have hout : (Csub.csSrc b n n).toNat + 32 * n ≤ 2048 ∨
        (2080 ≤ (Csub.csSrc b n n).toNat ∧ (Csub.csSrc b n n).toNat + 32 * n ≤ 2624) ∨
        2656 ≤ (Csub.csSrc b n n).toNat := by
      rw [hsrc]
      split <;> omega
    have hbytes := readPadded_eq hs.1 (Csub.csSrc b n n).toNat (32 * n) hout
    simp only [Csub.subResultMemory, csSrc_eq a b h n n hn32, hbytes]
    exact write_same hs.1 _ _

theorem fastRepresents_iff (a b : ByteArray) (h : Agree a b) (ptr n value : Nat)
    (hout : ptr + 32 * n ≤ 2048 ∨ (2080 ≤ ptr ∧ ptr + 32 * n ≤ 2624) ∨ 2656 ≤ ptr) :
    Model.FastRepresents a ptr n value ↔ Model.FastRepresents b ptr n value := by
  have hlimbs : Model.fastLimbs a ptr n = Model.fastLimbs b ptr n := by
    unfold Model.fastLimbs
    apply List.map_congr_left
    intro k hk
    have hk' : k < n := List.mem_range.mp hk
    rw [readWord_eq h (ptr + 32 * (n - 1 - k)) (by omega)]
  simp only [Model.FastRepresents, hlimbs]

end CountAgree

/-! ## A staged round, the internal loop, and the caller's initial copy -/

def roundDst (_c : Nat) : Nat := 2368

def sqRound (s : State) (n c : Nat) (mem : ByteArray) : ByteArray :=
  Csub.csResultMemory
    (SquareLoopBlocks.countMem (sqRowsCarry (mpZeroed s mem n) n n) c) n (roundDst c)

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

theorem tn_le_one (s : State) (mem : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 8)
    (_hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm) (ham : a < mm)
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
  exact sqRowsCarry_tn_le_one (mpZeroed s mem (p + 2)) p a mm (by omega)
    ha0 hm0 hminv0 (tValue_mpZeroed s mem (p + 2)) ham

theorem sqRound_represents (s : State) (mem : ByteArray) (p a mm c : Nat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqRound s (p + 2) c mem) (roundDst c) (p + 2)
      (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) := by
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
  have hrep := sqRowsCarry_represents (mpZeroed s mem (p + 2)) p a mm (roundDst c) (by omega)
    (by simp only [roundDst]; omega) ha0 hm0 hodd ham hminv0 (tValue_mpZeroed s mem (p + 2))
  have hagree := CountAgree.csResult_agree _ _ (CountAgree.countMem_agree _ c) (p + 2) (roundDst c)
    (by omega) hn32 (tn_le_one s mem p a mm hn32 hfast ha hm ham hminv)
  exact (CountAgree.fastRepresents_iff _ _ hagree (roundDst c) (p + 2) _
    (by simp only [roundDst]; omega)).2 hrep

theorem sqRound_readWord_outside (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (_hfast : n = 4 ∨ n = 8)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2624 ≤ addr)
    (hdst : addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (sqRound s n c mem) addr = MachineState.readWord mem addr := by
  have hd : addr + 32 ≤ roundDst c ∨ roundDst c + 32 * n ≤ addr := by
    simp only [roundDst]; omega
  rw [sqRound, csResultMemory_readWord_outside _ n (roundDst c) addr hn hsubb hd,
    SquareLoopBlocks.readWord_countMem_disjoint _ c addr hcount,
    readWord_sqRowsCarry _ n addr hn32 hscratch n le_rfl,
    readWord_mpZeroed s _ n addr hn32 hscratch]

/-- Everything at or above 2656 survives a round. -/
theorem sqRound_readWord_high (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hfast : n = 4 ∨ n = 8) (haddr : 2656 ≤ addr) :
    MachineState.readWord (sqRound s n c mem) addr = MachineState.readWord mem addr :=
  sqRound_readWord_outside s mem n c addr hn hn32 hfast (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

/-- The counter word holds the decremented value after a round. -/
theorem sqRound_count (s : State) (mem : ByteArray) (n c : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (_hfast : n = 4 ∨ n = 8) (hc : c < 2 ^ 256) :
    MachineState.readWord (sqRound s n c mem) 2624 = UInt256.ofNat c := by
  rw [sqRound, csResultMemory_readWord_outside _ n (roundDst c) 2624 hn (Or.inr (by omega))
    (by simp only [roundDst]; omega)]
  exact SquareLoopBlocks.readWord_countMem _ c hc

/-- Blocks disjoint from `SUBB`, the scratch, the destination and the counter survive. -/
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

/-! ## The whole loop -/

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

/-- The five configuration words survive the whole loop. -/
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

/-- A positive staged loop leaves the final result at the caller's destination. -/
theorem sqRunMem_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hn32 : p + 2 ≤ 8) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqRunMem s (p + 2) k mem) 2368 (p + 2)
      ((fun x => Model.montMul mm (Limbs.radix ^ (p + 2)) x x)^[k] a) := by
  induction k generalizing mem a with
  | zero => omega
  | succ k ih =>
      have hrep := sqRound_represents s mem p a mm k hn32 hfast ha hm hodd ham hminv
      cases k with
      | zero => simpa [sqRunMem, roundDst] using hrep
      | succ j =>
        have hmod : Model.FastRepresents (sqRound s (p + 2) (j + 1) mem) 0 (p + 2) mm :=
          sqRound_fastRepresents_outside s mem (p + 2) (j + 1) 0 (p + 2) mm (by omega) hn32 hfast
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hm
        have hminv' : ((MachineState.readWord (sqRound s (p + 2) (j + 1) mem)
            (32 * (p + 2) - 32)).toNat *
            (MachineState.readWord (sqRound s (p + 2) (j + 1) mem) 2720).toNat + 1) % 2 ^ 256 = 0 := by
          rw [sqRound_readWord_outside s mem (p + 2) (j + 1) (32 * (p + 2) - 32) (by omega) hn32 hfast
              (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
            sqRound_readWord_high s mem (p + 2) (j + 1) 2720 (by omega) hn32 hfast (by omega)]
          exact hminv
        have hstage : roundDst (j + 1) = 2368 := by simp [roundDst]
        rw [hstage] at hrep
        rw [sqRunMem_succ, Function.iterate_succ_apply]
        exact ih (sqRound s (p + 2) (j + 1) mem) (Model.montMul mm (Limbs.radix ^ (p + 2)) a a)
          (by omega) hrep hmod (Model.montMul_lt hmpos _ _ _) hminv'

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

/-- The five configuration words survive the whole loop. -/
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

/-- Initial staging followed by the internal square loop has the original caller contract. -/
theorem sqLoopMem_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hn32 : p + 2 ≤ 8) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 512 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqLoopMem s (p + 2) k mem) 2368 (p + 2)
      ((fun x => Model.montMul mm (Limbs.radix ^ (p + 2)) x x)^[k] a) := by
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
      exact sqRunMem_represents s (stage mem 512 (p + 2)) p a mm (k + 1) hfast hn32 (by omega)
        (represents_stage mem (p + 2) a ha) hm' hodd ham hmpos hminv'

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
