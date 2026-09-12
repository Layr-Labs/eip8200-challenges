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
      = CSUB (9280 := c) (rows (re-stage, re-zero) mem)

`SquareResult.sqMem s mem n` is the same composition **without** the counter store, so the
two memories agree everywhere except the CIOS top word `[8192, 8224)` (where the machine
model already differs from the Monpro-style one) and the counter word `[9280, 9312)`.
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

/-- Byte agreement outside `[8192, 8224)` (the machine model's scratch word) and outside
`[9280, 9312)` (the squaring counter). -/
def Agree (a b : ByteArray) : Prop :=
  ∀ i, i < 8192 ∨ (8224 ≤ i ∧ i < 9280) ∨ 9312 ≤ i → a[i]?.getD 0 = b[i]?.getD 0

theorem refl (a : ByteArray) : Agree a a := fun _ _ => rfl

theorem symm {a b : ByteArray} (h : Agree a b) : Agree b a := fun i hi => (h i hi).symm

theorem trans {a b c : ByteArray} (hab : Agree a b) (hbc : Agree b c) : Agree a c :=
  fun i hi => (hab i hi).trans (hbc i hi)

/-- The scratch agreement of `CarryScratchAgreement` is stronger. -/
theorem of_scratch {a b : ByteArray} (h : CarryScratchAgreement.Agree a b) : Agree a b :=
  fun i hi => h i (by omega)

/-- Storing the counter at 9280 changes nothing that `Agree` sees. -/
theorem countMem_agree (a : ByteArray) (c : Nat) :
    Agree (SquareLoopBlocks.countMem a c) a := by
  intro i hi
  rw [SquareLoopBlocks.countMem, MachineState.writeBytes_getElem?_getD, if_neg]
  intro h
  rw [show (Data.Bytes.natToBytesPadded c 32).size = 32 by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]] at h
  omega

theorem readPadded_eq {a b : ByteArray} (h : Agree a b) (start count : Nat)
    (hout : start + count ≤ 8192 ∨ (8224 ≤ start ∧ start + count ≤ 9280) ∨ 9312 ≤ start) :
    MachineState.readPadded a start count = MachineState.readPadded b start count := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  exact h (start + i) (by omega)

theorem readWord_eq {a b : ByteArray} (h : Agree a b) (start : Nat)
    (hout : start + 32 ≤ 8192 ∨ (8224 ≤ start ∧ start + 32 ≤ 9280) ∨ 9312 ≤ start) :
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

theorem csStep_agree (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 32) :
    Agree (Csub.csStep a n j).memory (Csub.csStep b n j).memory ∧
      (Csub.csStep a n j).flag = (Csub.csStep b n j).flag := by
  induction j with
  | zero => exact ⟨h, rfl⟩
  | succ j ih =>
    have ht := readWord_eq ih.1 (8256 + 32 * (n - 1 - j)) (Or.inr (Or.inl (by omega)))
    have hm := readWord_eq ih.1 (32 * (n - 1 - j)) (Or.inl (by omega))
    simp only [Csub.csStep, ht, hm, ih.2]
    exact ⟨write_same ih.1 _ _, True.intro⟩

theorem csUse_eq (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 32) :
    Csub.csUse a n j = Csub.csUse b n j := by
  have hs := csStep_agree a b h n j hn
  simp only [Csub.csUse, hs.2, readWord_eq hs.1 8224 (Or.inr (Or.inl (by decide)))]

theorem csSrc_eq (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 32) :
    Csub.csSrc a n j = Csub.csSrc b n j := by
  unfold Csub.csSrc
  rw [csUse_eq a b h n j hn]

theorem csResult_agree (a b : ByteArray) (h : Agree a b) (n dst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (htn : (MachineState.readWord b 8224).toNat ≤ 1) :
    Agree (Csub.csResultMemory a n dst) (Csub.csResultMemory b n dst) := by
  have hg : EarlyCsub.Skip a = EarlyCsub.Skip b := by
    unfold EarlyCsub.Skip EarlyCsub.guardWord
    rw [readWord_eq h 8224 (Or.inr (Or.inl (by decide))),
      readWord_eq h 8256 (Or.inr (Or.inl (by decide))), readWord_eq h 0 (Or.inl (by decide))]
  simp only [Csub.csResultMemory, hg]
  split
  · rw [readPadded_eq h 8256 (32 * n) (Or.inr (Or.inl (by omega)))]
    exact write_same h _ _
  ·
    have hs := csStep_agree a b h n n hn32
    have htn' : (MachineState.readWord (Csub.csStep b n n).memory 8224).toNat ≤ 1 := by
      rw [Csub.csStep_readWord_disjoint b n 8224 hn (Or.inr (by omega)) n le_rfl]
      exact htn
    have hsrc := Csub.csSrc_toNat b n n (Csub.csUse_le_one b n n htn')
    have hout : (Csub.csSrc b n n).toNat + 32 * n ≤ 8192 ∨
        (8224 ≤ (Csub.csSrc b n n).toNat ∧ (Csub.csSrc b n n).toNat + 32 * n ≤ 9280) ∨
        9312 ≤ (Csub.csSrc b n n).toNat := by
      rw [hsrc]
      split <;> omega
    have hbytes := readPadded_eq hs.1 (Csub.csSrc b n n).toNat (32 * n) hout
    simp only [Csub.subResultMemory, csSrc_eq a b h n n hn32, hbytes]
    exact write_same hs.1 _ _

theorem fastRepresents_iff (a b : ByteArray) (h : Agree a b) (ptr n value : Nat)
    (hout : ptr + 32 * n ≤ 8192 ∨ (8224 ≤ ptr ∧ ptr + 32 * n ≤ 9280) ∨ 9312 ≤ ptr) :
    Model.FastRepresents a ptr n value ↔ Model.FastRepresents b ptr n value := by
  have hlimbs : Model.fastLimbs a ptr n = Model.fastLimbs b ptr n := by
    unfold Model.fastLimbs
    apply List.map_congr_left
    intro k hk
    have hk' : k < n := List.mem_range.mp hk
    rw [readWord_eq h (ptr + 32 * (n - 1 - k)) (by omega)]
  simp only [Model.FastRepresents, hlimbs]

end CountAgree

/-! ## One round and the loop -/

/-- One square inside the loop: re-stage the operand, re-zero the accumulator, run the `n`
rows, store the decremented counter `c` at 9280, and subtract conditionally. -/
def sqRound (s : State) (n c : Nat) (mem : ByteArray) : ByteArray :=
  Csub.csResultMemory
    (SquareLoopBlocks.countMem (sqRowsCarry (mpZeroed s (stage mem 2048 n) n) n n) c) n 2048

/-- The memory after the `k` squares of one kernel call whose counter word holds `k`. -/
def sqLoopMem (s : State) (n : Nat) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k + 1, mem => sqLoopMem s n k (sqRound s n k mem)

theorem sqLoopMem_zero (s : State) (n : Nat) (mem : ByteArray) :
    sqLoopMem s n 0 mem = mem := rfl

theorem sqLoopMem_succ (s : State) (n k : Nat) (mem : ByteArray) :
    sqLoopMem s n (k + 1) mem = sqLoopMem s n k (sqRound s n k mem) := rfl

/-! ## A round agrees with a plain `SQUARE` call -/

theorem sqMem_eq_csResult (s : State) (mem : ByteArray) (n : Nat) (hn : n = 4 ∨ n = 8) :
    sqMem s mem n =
      Csub.csResultMemory (sqRowsCarry (mpZeroed s (stage mem 2048 n) n) n n) n 2048 := by
  rw [sqMem_of_fast s mem n hn, show inputMemory mem 2048 n = stage mem 2048 n from by
    unfold inputMemory; rw [if_pos hn]]

/-- The row-0 memory of a square: the operand staged at 8960 and the accumulator zeroed. -/
theorem tn_le_one (s : State) (mem : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2048 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    (MachineState.readWord
      (sqRowsCarry (mpZeroed s (stage mem 2048 (p + 2)) (p + 2)) (p + 2) (p + 2)) 8224).toNat
        ≤ 1 := by
  have hread (addr : Nat) (hd : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
      MachineState.readWord (mpZeroed s (stage mem 2048 (p + 2)) (p + 2)) addr =
        MachineState.readWord mem addr :=
    (readWord_mpZeroed s _ (p + 2) addr hn32 hd).trans
      (read_stage_outside mem 2048 (p + 2) addr (by omega))
  have ha0 : Model.FastRepresents (mpZeroed s (stage mem 2048 (p + 2)) (p + 2)) 2048 (p + 2) a := by
    refine (Model.fastRepresents_congr (a := mem) ?_ a).1 ha
    intro j hj
    rw [hread (2048 + 32 * j) (Or.inl (by omega))]
  have hm0 : Model.FastRepresents (mpZeroed s (stage mem 2048 (p + 2)) (p + 2)) 0 (p + 2) mm := by
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [hread (0 + 32 * j) (Or.inl (by omega))]
  have hminv0 : ((MachineState.readWord (mpZeroed s (stage mem 2048 (p + 2)) (p + 2))
      (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord (mpZeroed s (stage mem 2048 (p + 2)) (p + 2)) 9376).toNat + 1) %
        2 ^ 256 = 0 := by
    rw [hread (32 * (p + 2) - 32) (Or.inl (by omega)), hread 9376 (Or.inr (by decide))]
    exact hminv
  exact sqRowsCarry_tn_le_one (mpZeroed s (stage mem 2048 (p + 2)) (p + 2)) p a mm hn32
    ha0 hm0 hminv0 (tValue_mpZeroed s _ (p + 2)) ham

/-- A round and a plain `SQUARE` call differ only in the counter word (and in the CIOS top
word, where the machine model already differs). -/
theorem sqRound_agree (s : State) (mem : ByteArray) (p a mm c : Nat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2048 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    CountAgree.Agree (sqRound s (p + 2) c mem) (sqMem s mem (p + 2)) := by
  rw [sqMem_eq_csResult s mem (p + 2) hfast]
  exact CountAgree.csResult_agree _ _ (CountAgree.countMem_agree _ c) (p + 2) 2048 (by omega) hn32
    (tn_le_one s mem p a mm hn32 hfast ha hm ham hminv)

/-! ## Value and preservation lemmas for one round -/

theorem sqRound_represents (s : State) (mem : ByteArray) (p a mm c : Nat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha : Model.FastRepresents mem 2048 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqRound s (p + 2) c mem) 2048 (p + 2)
      (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) :=
  (CountAgree.fastRepresents_iff _ _ (sqRound_agree s mem p a mm c hn32 hfast ha hm ham hminv)
    2048 (p + 2) _ (Or.inl (by omega))).2
    (sqMem_represents s mem p a mm hn32 ha hm hodd ham hminv)

/-- Every word outside `SUBB`, the CIOS scratch, the destination block and the counter
survives a round. -/
theorem sqRound_readWord_outside (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hfast : n = 4 ∨ n = 8)
    (hsubb : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 8192 ∨ 9280 ≤ addr)
    (hdst : addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 9280 ∨ 9312 ≤ addr) :
    MachineState.readWord (sqRound s n c mem) addr = MachineState.readWord mem addr := by
  rw [sqRound, csResultMemory_readWord_outside _ n 2048 addr hn hsubb hdst,
    SquareLoopBlocks.readWord_countMem_disjoint _ c addr hcount,
    readWord_sqRowsCarry _ n addr hn32 hscratch n le_rfl,
    readWord_mpZeroed s _ n addr hn32 hscratch,
    read_stage_outside mem 2048 n addr (by rcases hfast with h | h <;> omega)]

/-- Everything at or above 9312 survives a round. -/
theorem sqRound_readWord_high (s : State) (mem : ByteArray) (n c addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hfast : n = 4 ∨ n = 8) (haddr : 9312 ≤ addr) :
    MachineState.readWord (sqRound s n c mem) addr = MachineState.readWord mem addr :=
  sqRound_readWord_outside s mem n c addr hn hn32 hfast (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

/-- The counter word holds the decremented value after a round. -/
theorem sqRound_count (s : State) (mem : ByteArray) (n c : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hc : c < 2 ^ 256) :
    MachineState.readWord (sqRound s n c mem) 9280 = UInt256.ofNat c := by
  rw [sqRound, csResultMemory_readWord_outside _ n 2048 9280 hn (Or.inr (by omega))
    (Or.inr (by omega))]
  exact SquareLoopBlocks.readWord_countMem _ c hc

/-- Blocks disjoint from `SUBB`, the scratch, the destination and the counter survive. -/
theorem sqRound_fastRepresents_outside (s : State) (mem : ByteArray) (n c ptr cnt v : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hfast : n = 4 ∨ n = 8)
    (hsubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 8192 ∨ 9280 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 2048 ∨ 2048 + 32 * n ≤ ptr)
    (hcount : ptr + 32 * cnt ≤ 9280 ∨ 9312 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqRound s n c mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [sqRound_readWord_outside s mem n c (ptr + 32 * j) hn hn32 hfast (by omega) (by omega)
    (by omega) (by omega)]

/-! ## The whole loop -/

theorem sqLoopMem_readWord_outside (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 8192 ∨ 9280 ≤ addr)
    (hdst : addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr)
    (hcount : addr + 32 ≤ 9280 ∨ 9312 ≤ addr) :
    MachineState.readWord (sqLoopMem s n k mem) addr = MachineState.readWord mem addr := by
  induction k generalizing mem with
  | zero => rfl
  | succ k ih =>
      rw [sqLoopMem_succ, ih (sqRound s n k mem),
        sqRound_readWord_outside s mem n k addr hn hn32 hfast hsubb hscratch hdst hcount]

theorem sqLoopMem_readWord_high (s : State) (mem : ByteArray) (n k addr : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 32) (haddr : 9312 ≤ addr) :
    MachineState.readWord (sqLoopMem s n k mem) addr = MachineState.readWord mem addr :=
  sqLoopMem_readWord_outside s mem n k addr hfast hn hn32 (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr haddr)

/-- The five configuration words survive the whole loop. -/
theorem sqLoopMem_frame (s : State) (mem : ByteArray) (n k : Nat) (hfast : n = 4 ∨ n = 8)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    MachineState.readWord (sqLoopMem s n k mem) 9344 = MachineState.readWord mem 9344 ∧
      MachineState.readWord (sqLoopMem s n k mem) 9376 = MachineState.readWord mem 9376 ∧
      MachineState.readWord (sqLoopMem s n k mem) 9408 = MachineState.readWord mem 9408 ∧
      MachineState.readWord (sqLoopMem s n k mem) 9440 = MachineState.readWord mem 9440 ∧
      MachineState.readWord (sqLoopMem s n k mem) 9472 = MachineState.readWord mem 9472 :=
  ⟨sqLoopMem_readWord_high s mem n k 9344 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 9376 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 9408 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 9440 hfast hn hn32 (by omega),
   sqLoopMem_readWord_high s mem n k 9472 hfast hn hn32 (by omega)⟩

theorem sqLoopMem_fastRepresents_outside (s : State) (mem : ByteArray) (n k ptr cnt v : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 8192 ∨ 9312 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ 2048 ∨ 2048 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqLoopMem s n k mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [sqLoopMem_readWord_outside s mem n k (ptr + 32 * j) hfast hn hn32 (by omega) (by omega)
    (by omega) (by omega)]

/-- **The value of the loop**: `k` Montgomery squares. -/
theorem sqLoopMem_represents (s : State) (mem : ByteArray) (p a mm k : Nat)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hn32 : p + 2 ≤ 32)
    (ha : Model.FastRepresents mem 2048 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (sqLoopMem s (p + 2) k mem) 2048 (p + 2)
      ((fun x => Model.montMul mm (Limbs.radix ^ (p + 2)) x x)^[k] a) := by
  induction k generalizing mem a with
  | zero => exact ha
  | succ k ih =>
      have hrep := sqRound_represents s mem p a mm k hn32 hfast ha hm hodd ham hminv
      have hmod : Model.FastRepresents (sqRound s (p + 2) k mem) 0 (p + 2) mm :=
        sqRound_fastRepresents_outside s mem (p + 2) k 0 (p + 2) mm (by omega) hn32 hfast
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hm
      have hminv' : ((MachineState.readWord (sqRound s (p + 2) k mem)
          (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord (sqRound s (p + 2) k mem) 9376).toNat + 1) % 2 ^ 256 = 0 := by
        rw [sqRound_readWord_outside s mem (p + 2) k (32 * (p + 2) - 32) (by omega) hn32 hfast
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
          sqRound_readWord_high s mem (p + 2) k 9376 (by omega) hn32 hfast (by omega)]
        exact hminv
      have hlt : Model.montMul mm (Limbs.radix ^ (p + 2)) a a < mm :=
        Model.montMul_lt hmpos (Limbs.radix ^ (p + 2)) a a
      have h := ih (mem := sqRound s (p + 2) k mem)
        (a := Model.montMul mm (Limbs.radix ^ (p + 2)) a a) hrep hmod hlt hminv'
      rw [sqLoopMem_succ]
      rw [Function.iterate_succ_apply]
      exact h

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
