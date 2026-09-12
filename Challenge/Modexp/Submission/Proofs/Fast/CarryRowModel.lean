import Challenge.Modexp.Submission.Proofs.Fast.CarryScratchAgreement
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryScratchAgreement

/-- Overflow is carried in a stack slot, rather than the scratch word. -/
def overflow (mem : ByteArray) (c : UInt256) : UInt256 :=
  UInt256.lt (MachineState.readWord mem 4128 + c) c

def tailCarry (mem : ByteArray) (c f : UInt256) : ByteArray :=
  MachineState.writeBytes (tailMem1 mem c)
    (Data.Bytes.natToBytesPadded (f + UInt256.lt (MachineState.readWord mem 4128 + c) c).toNat 32) 4128

def rowOverflow (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  overflow (rowL1 mem pa pb n i).memory (rowL1 mem pa pb n i).carry

def rowMidCarry (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  midMem1 (rowL1 mem pa pb n i).memory (rowL1 mem pa pb n i).carry

def rowL2Carry (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  let q := rowL1 mem pa pb n i
  l2Step (midMem1 q.memory q.carry) (rowMu q.memory n) (rowC0 q.memory n) n (n-1)

def rowCarry (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  let q := rowL1 mem pa pb n i
  let r := rowL2Carry mem pa pb n i
  tailCarry r.memory r.carry (overflow q.memory q.carry)

def rowsCarry (mem : ByteArray) (pa pb n : Nat) : Nat → ByteArray
  | 0 => mem
  | i+1 => rowCarry (rowsCarry mem pa pb n i) pa pb n i

theorem l1_agree (a b : ByteArray) (h : Agree a b) (bi : UInt256) (pa n j : Nat)
    (hpa : pa + 32*n ≤ 4096) (hj : j ≤ n) :
    Agree (l1Step a bi pa n j).memory (l1Step b bi pa n j).memory ∧
      (l1Step a bi pa n j).carry = (l1Step b bi pa n j).carry := by
  induction j with
  | zero => exact ⟨h, rfl⟩
  | succ j ih =>
    have prev := ih (by omega)
    have hx := readWord_eq prev.1 (pa + 32*(n-1-j)) (Or.inl (by omega))
    have ht := readWord_eq prev.1 (4160 + 32*(n-1-j)) (Or.inr (by omega))
    simp only [l1Step, hx, ht, prev.2]
    exact ⟨write_same prev.1 _ _, True.intro⟩

theorem l2_agree (a b : ByteArray) (h : Agree a b) (mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 32) :
    Agree (l2Step a mu c0 n k).memory (l2Step b mu c0 n k).memory ∧
      (l2Step a mu c0 n k).carry = (l2Step b mu c0 n k).carry := by
  induction k with
  | zero => exact ⟨h, rfl⟩
  | succ k ih =>
    have hx := readWord_eq ih.1 (32*(n-2-k)) (Or.inl (by omega))
    have ht := readWord_eq ih.1 (4160 + 32*(n-2-k)) (Or.inr (by omega))
    simp only [l2Step, hx, ht, ih.2]
    exact ⟨write_same ih.1 _ _, True.intro⟩

theorem middle_agree (a b : ByteArray) (h : Agree a b) (c : UInt256) :
    Agree (midMem1 a c) (midMem b c) := by
  have ht := readWord_eq h 4128 (Or.inr (by decide))
  have same : Agree (midMem1 a c) (midMem1 b c) := by
    simp only [midMem1, ht]
    exact write_same h _ _
  exact trans same (symm (scratch_word (midMem1 b c) (overflow b c)))

theorem overflow_eq (a b : ByteArray) (h : Agree a b) (c : UInt256) :
    overflow a c = overflow b c := by
  unfold overflow
  rw [readWord_eq h 4128 (Or.inr (by decide))]

theorem rowMu_eq (a b : ByteArray) (h : Agree a b) (n : Nat) :
    rowMu a n = rowMu b n := by
  unfold rowMu
  rw [readWord_eq h 5280 (Or.inr (by decide)),
    readWord_eq h (4128+32*n) (Or.inr (by omega))]

theorem rowC0_eq (a b : ByteArray) (h : Agree a b) (n : Nat) (hn : n ≤ 32) :
    rowC0 a n = rowC0 b n := by
  unfold rowC0
  rw [readWord_eq h (32*n-32) (Or.inl (by omega)), rowMu_eq a b h n]

theorem tail_agree (a b : ByteArray) (h : Agree a b) (c f : UInt256)
    (hf : MachineState.readWord b 4096 = f) :
    Agree (tailCarry a c f) (tailMem b c) := by
  have ht := readWord_eq h 4128 (Or.inr (by decide))
  have hflag : MachineState.readWord (tailMem1 b c) 4096 = f := by
    unfold tailMem1
    rw [readWord_storeWord_outside b _ 4160 4096 (Or.inl (by decide))]
    exact hf
  have same : Agree (tailMem1 a c) (tailMem1 b c) := by
    simp only [tailMem1, ht]
    exact write_same h _ _
  simp only [tailCarry, tailMem, ht, hflag]
  exact write_same same _ _

theorem row_agree (a b : ByteArray) (h : Agree a b) (pa pb n i : Nat)
    (hpa : pa+32*n ≤ 4096) (hpb : pb+32*n ≤ 4096)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n) :
    Agree (rowCarry a pa pb n i) (rowMem b pa pb n i) := by
  have hbi : rowBi a pb n i = rowBi b pb n i := by
    unfold rowBi
    exact readWord_eq h _ (Or.inl (by omega))
  have hl1 : Agree (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory ∧
      (rowL1 a pa pb n i).carry = (rowL1 b pa pb n i).carry := by
    simp only [rowL1, hbi]
    exact l1_agree a b h _ pa n n hpa (by omega)
  have hm := middle_agree (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1
    (rowL1 b pa pb n i).carry
  have hmu := rowMu_eq (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1 n
  have hc0 := rowC0_eq (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1 n hn32
  have hflag := overflow_eq (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1 (rowL1 b pa pb n i).carry
  have hl2 := l2_agree _ _ hm (rowMu (rowL1 b pa pb n i).memory n)
    (rowC0 (rowL1 b pa pb n i).memory n) n (n-1) hn32
  have hf : MachineState.readWord (rowL2 b pa pb n i).memory 4096 =
      overflow (rowL1 b pa pb n i).memory (rowL1 b pa pb n i).carry := by
    simp only [rowL2, rowMid]
    rw [readWord_l2Step_low _ _ _ n 4096 (n-1) (by decide), readWord_midMem_tnp]
    rfl
  simpa only [rowCarry, rowL2Carry, rowMem, rowL2, rowMid, hl1.2, hmu, hc0, hflag, hl2.2] using
    tail_agree _ _ hl2.1 _ _ hf

theorem rows_agree (mem : ByteArray) (pa pb n j : Nat)
    (hpa : pa+32*n ≤ 4096) (hpb : pb+32*n ≤ 4096)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hj : j ≤ n) :
    Agree (rowsCarry mem pa pb n j) (rowsMem mem pa pb n j) := by
  induction j with
  | zero => exact refl mem
  | succ j ih =>
    exact row_agree _ _ (ih (by omega)) pa pb n j hpa hpb hn hn32 (by omega)


theorem csStep_agree (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 32) :
    Agree (Csub.csStep a n j).memory (Csub.csStep b n j).memory ∧
      (Csub.csStep a n j).flag = (Csub.csStep b n j).flag := by
  induction j with
  | zero => exact ⟨h, rfl⟩
  | succ j ih =>
    have ht := readWord_eq ih.1 (4160+32*(n-1-j)) (Or.inr (by omega))
    have hm := readWord_eq ih.1 (32*(n-1-j)) (Or.inl (by omega))
    simp only [Csub.csStep, ht, hm, ih.2]
    exact ⟨write_same ih.1 _ _, True.intro⟩

theorem csUse_eq (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 32) :
    Csub.csUse a n j = Csub.csUse b n j := by
  have hs := csStep_agree a b h n j hn
  simp only [Csub.csUse, hs.2, readWord_eq hs.1 4128 (Or.inr (by decide))]

theorem csSrc_eq (a b : ByteArray) (h : Agree a b) (n j : Nat) (hn : n ≤ 32) :
    Csub.csSrc a n j = Csub.csSrc b n j := by
  unfold Csub.csSrc
  rw [csUse_eq a b h n j hn]

theorem csResult_agree (a b : ByteArray) (h : Agree a b) (n dst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (htn : (MachineState.readWord b 4128).toNat ≤ 1) :
    Agree (Csub.csResultMemory a n dst) (Csub.csResultMemory b n dst) := by
  have hg : EarlyCsub.Skip a = EarlyCsub.Skip b := by
    unfold EarlyCsub.Skip EarlyCsub.guardWord
    rw [readWord_eq h 4128 (Or.inr (by decide)),
      readWord_eq h 4160 (Or.inr (by decide)), readWord_eq h 0 (Or.inl (by decide))]
  simp only [Csub.csResultMemory, hg]
  split
  · rw [readPadded_eq h 4160 (32*n) (Or.inr (by decide))]
    exact write_same h _ _
  ·
    have hs := csStep_agree a b h n n hn32
    have htn' : (MachineState.readWord (Csub.csStep b n n).memory 4128).toNat ≤ 1 := by
      rw [Csub.csStep_readWord_disjoint b n 4128 hn (Or.inr (by omega)) n le_rfl]
      exact htn
    have hsrc := Csub.csSrc_toNat b n n (Csub.csUse_le_one b n n htn')
    have hout : (Csub.csSrc b n n).toNat + 32*n ≤ 4096 ∨ 4128 ≤ (Csub.csSrc b n n).toNat := by
      rw [hsrc]
      split <;> omega
    have hbytes := readPadded_eq hs.1 (Csub.csSrc b n n).toNat (32*n) hout
    simp only [Csub.subResultMemory, csSrc_eq a b h n n hn32, hbytes]
    exact write_same hs.1 _ _


theorem fastRepresents_iff (a b : ByteArray) (h : Agree a b) (ptr n value : Nat)
    (hout : ptr+32*n ≤ 4096 ∨ 4128 ≤ ptr) :
    Model.FastRepresents a ptr n value ↔ Model.FastRepresents b ptr n value := by
  have hlimbs : Model.fastLimbs a ptr n = Model.fastLimbs b ptr n := by
    unfold Model.fastLimbs
    apply List.map_congr_left
    intro k hk
    have hk' : k < n := List.mem_range.mp hk
    rw [readWord_eq h (ptr+32*(n-1-k)) (by omega)]
  simp only [Model.FastRepresents, hlimbs]


theorem readWord_tailCarry (mem : ByteArray) (c f : UInt256) (addr : Nat)
    (hout : addr+32 ≤ 4096 ∨ 5184 ≤ addr) :
    MachineState.readWord (tailCarry mem c f) addr = MachineState.readWord mem addr := by
  unfold tailCarry
  rw [readWord_storeWord_outside _ _ 4128 addr (by omega),
    readWord_tailMem1 mem c addr (by omega)]

theorem readWord_rowCarry (mem : ByteArray) (pa pb n i addr : Nat) (hn : n ≤ 32)
    (hout : addr+32 ≤ 4096 ∨ 5184 ≤ addr) :
    MachineState.readWord (rowCarry mem pa pb n i) addr = MachineState.readWord mem addr := by
  unfold rowCarry rowL2Carry
  rw [readWord_tailCarry _ _ _ addr hout, readWord_l2Step _ _ _ n addr (n-1) hn hout,
    readWord_midMem1 _ _ addr (by omega)]
  unfold rowL1
  exact readWord_l1Step mem _ pa n addr n hn hout

theorem readWord_rowsCarry (mem : ByteArray) (pa pb n addr : Nat) (hn : n ≤ 32)
    (hout : addr+32 ≤ 4096 ∨ 5184 ≤ addr) (i : Nat) :
    MachineState.readWord (rowsCarry mem pa pb n i) addr = MachineState.readWord mem addr := by
  induction i with
  | zero => rfl
  | succ i ih =>
    unfold rowsCarry
    rw [readWord_rowCarry _ pa pb n i addr hn hout, ih]

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
