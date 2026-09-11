import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true

/-! Memory correspondence for carrying the top CIOS bit on the stack.
The existing arithmetic model writes that bit at 8192. The register variant
defers that store until the last row. Overlaying the register reconstructs
the model memory; the limb loops operate outside this word. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryMemory

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def writeWord (mem : ByteArray) (a : Nat) (v : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) a

def setCarry (mem : ByteArray) (v : UInt256) : ByteArray := writeWord mem 8192 v

theorem writeWord_comm (mem : ByteArray) (a b : Nat) (v w : UInt256)
    (hab : a+32 ≤ b ∨ b+32 ≤ a) :
    writeWord (writeWord mem a v) b w = writeWord (writeWord mem b w) a v := by
  apply ByteArray.ext_getElem
  · simp only [writeWord, MachineState.writeBytes_size,
      BytesLemmas.natToBytesPadded_size]
    simp [Nat.max_comm, Nat.max_left_comm]
  · intro i hl hr
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hl,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hr]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      BytesLemmas.natToBytesPadded_size]
    by_cases ha : a ≤ i ∧ i < a+32
    · rw [if_neg (by omega), if_pos ha, if_pos ha]
    · by_cases hb : b ≤ i ∧ i < b+32
      · rw [if_pos hb, if_neg ha, if_pos hb]
      · rw [if_neg hb, if_neg ha, if_neg ha, if_neg hb]

theorem writeWord_overwrite (mem : ByteArray) (a : Nat) (v w : UInt256) :
    writeWord (writeWord mem a v) a w = writeWord mem a w := by
  apply ByteArray.ext_getElem
  · simp [writeWord, MachineState.writeBytes_size,
      BytesLemmas.natToBytesPadded_size]
  · intro i hl hr
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hl,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hr]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      BytesLemmas.natToBytesPadded_size]
    split <;> simp_all

theorem setCarry_writeWord (mem : ByteArray) (a : Nat) (v bit : UInt256)
    (ha : a+32 ≤ 8192 ∨ 8224 ≤ a) :
    setCarry (writeWord mem a v) bit = writeWord (setCarry mem bit) a v :=
  writeWord_comm mem a 8192 v bit ha

@[simp] theorem setCarry_setCarry (mem : ByteArray) (old bit : UInt256) :
    setCarry (setCarry mem old) bit = setCarry mem bit :=
  writeWord_overwrite mem 8192 old bit

theorem read_setCarry (mem : ByteArray) (bit : UInt256) (a : Nat)
    (ha : a+32 ≤ 8192 ∨ 8224 ≤ a) :
    MachineState.readWord (setCarry mem bit) a = MachineState.readWord mem a := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [BytesLemmas.natToBytesPadded_size] using ha

@[simp] theorem read_setCarry_same (mem : ByteArray) (bit : UInt256) :
    MachineState.readWord (setCarry mem bit) 8192 = bit := by
  change MachineState.readWord (MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded bit.toNat 32) 8192) 8192 = bit
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt mem 8192 bit.toNat bit.val.isLt]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat bit).symm

theorem l1Step_setCarry (mem : ByteArray) (bit bi : UInt256) (pa n j : Nat)
    (hn : 1 ≤ n) (hpa : pa+32*n ≤ 8192) :
    (l1Step (setCarry mem bit) bi pa n j).memory =
      setCarry (l1Step mem bi pa n j).memory bit ∧
    (l1Step (setCarry mem bit) bi pa n j).carry = (l1Step mem bi pa n j).carry := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    have ha : pa+32*(n-1-j)+32 ≤ 8192 := by omega
    have ht : 8224 ≤ 8256+32*(n-1-j) := by omega
    simp only [l1Step, ih.1, ih.2,
      read_setCarry _ bit _ (Or.inl ha), read_setCarry _ bit _ (Or.inr ht)]
    constructor
    · exact (setCarry_writeWord _ _ _ bit (Or.inr ht)).symm
    · trivial

theorem l2Step_setCarry (mem : ByteArray) (bit mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 32) :
    (l2Step (setCarry mem bit) mu c0 n k).memory =
      setCarry (l2Step mem mu c0 n k).memory bit ∧
    (l2Step (setCarry mem bit) mu c0 n k).carry = (l2Step mem mu c0 n k).carry := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hx : 32*(n-2-k)+32 ≤ 8192 := by omega
    have ht : 8224 ≤ 8256+32*(n-2-k) := by omega
    have hs : 8224 ≤ 8256+32*(n-1-k) := by omega
    simp only [l2Step, ih.1, ih.2,
      read_setCarry _ bit _ (Or.inl hx), read_setCarry _ bit _ (Or.inr ht)]
    constructor
    · exact (setCarry_writeWord _ _ _ bit (Or.inr hs)).symm
    · trivial

theorem midMem1_setCarry (mem : ByteArray) (bit c : UInt256) :
    midMem1 (setCarry mem bit) c = setCarry (midMem1 mem c) bit := by
  unfold midMem1
  rw [read_setCarry mem bit 8224 (Or.inr (by decide))]
  exact (setCarry_writeWord mem 8224 _ bit (Or.inr (by decide))).symm

theorem midMem_setCarry (mem : ByteArray) (bit c : UInt256) :
    midMem (setCarry mem bit) c = midMem mem c := by
  unfold midMem
  rw [midMem1_setCarry, read_setCarry mem bit 8224 (Or.inr (by decide))]
  exact setCarry_setCarry _ _ _

theorem rowMu_setCarry (mem : ByteArray) (bit : UInt256) (n : Nat) :
    rowMu (setCarry mem bit) n = rowMu mem n := by
  unfold rowMu
  rw [read_setCarry mem bit 9376 (Or.inr (by decide)),
    read_setCarry mem bit (8224+32*n) (Or.inr (by omega))]

theorem rowC0_setCarry (mem : ByteArray) (bit : UInt256) (n : Nat) (hn : n ≤ 32) :
    rowC0 (setCarry mem bit) n = rowC0 mem n := by
  unfold rowC0
  rw [rowMu_setCarry,
    read_setCarry mem bit (32*n-32) (Or.inl (by omega))]

def tailRegisterMem (mem : ByteArray) (c bit : UInt256) : ByteArray :=
  writeWord (tailMem1 mem c) 8224
    (bit + UInt256.lt (MachineState.readWord mem 8224+c) c)

theorem tailMem1_setCarry (mem : ByteArray) (bit c : UInt256) :
    tailMem1 (setCarry mem bit) c = setCarry (tailMem1 mem c) bit := by
  unfold tailMem1
  rw [read_setCarry mem bit 8224 (Or.inr (by decide))]
  exact (setCarry_writeWord mem 8256 _ bit (Or.inr (by decide))).symm

theorem tailRegisterMem_spec (mem : ByteArray) (c bit : UInt256) :
    setCarry (tailRegisterMem mem c bit) bit = tailMem (setCarry mem bit) c := by
  unfold tailMem
  rw [tailMem1_setCarry, read_setCarry_same,
    read_setCarry mem bit 8224 (Or.inr (by decide))]
  exact setCarry_writeWord _ 8224 _ bit (Or.inr (by decide))

def midCarry (mem : ByteArray) (c : UInt256) : UInt256 :=
  UInt256.lt (MachineState.readWord mem 8224+c) c

/-- A complete row with the top carry stored in the returned register. -/
def rowRegister (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  let first := rowL1 mem pa pb n i
  let bit := midCarry first.memory first.carry
  let second := l2Step (midMem1 first.memory first.carry)
    (rowMu first.memory n) (rowC0 first.memory n) n (n-1)
  ⟨tailRegisterMem second.memory second.carry bit, bit⟩

theorem rowRegister_spec (mem : ByteArray) (pa pb n i : Nat) (hn : n ≤ 32) :
    setCarry (rowRegister mem pa pb n i).memory (rowRegister mem pa pb n i).carry =
      rowMem mem pa pb n i := by
  let first := rowL1 mem pa pb n i
  let bit := midCarry first.memory first.carry
  have hL := l2Step_setCarry (midMem1 first.memory first.carry) bit
    (rowMu first.memory n) (rowC0 first.memory n) n (n-1) hn
  change setCarry (tailRegisterMem _ _ bit) bit = _
  unfold rowMem rowL2 rowMid
  change setCarry (tailRegisterMem _ _ bit) bit =
    tailMem (l2Step (setCarry (midMem1 first.memory first.carry) bit)
      (rowMu first.memory n) (rowC0 first.memory n) n (n-1)).memory
      (l2Step (setCarry (midMem1 first.memory first.carry) bit)
      (rowMu first.memory n) (rowC0 first.memory n) n (n-1)).carry
  rw [hL.1, hL.2]
  exact tailRegisterMem_spec _ _ bit

theorem rowBi_setCarry (mem : ByteArray) (bit : UInt256) (pb n i : Nat)
    (hn : 1 ≤ n) (hpb : pb+32*n ≤ 8192) :
    rowBi (setCarry mem bit) pb n i = rowBi mem pb n i := by
  unfold rowBi
  exact read_setCarry mem bit _ (Or.inl (by omega))

/-- Every row overwrites the old top carry before consuming it. -/
theorem rowMem_setCarry (mem : ByteArray) (bit : UInt256) (pa pb n i : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hpa : pa+32*n ≤ 8192) (hpb : pb+32*n ≤ 8192) :
    rowMem (setCarry mem bit) pa pb n i = rowMem mem pa pb n i := by
  have hL := l1Step_setCarry mem bit (rowBi mem pb n i) pa n n hn hpa
  simp only [rowMem, rowL2, rowMid, rowL1, rowBi_setCarry mem bit pb n i hn hpb,
    hL.1, hL.2, midMem_setCarry, rowMu_setCarry, rowC0_setCarry _ bit n hn32]

def rowsRegister (mem : ByteArray) (pa pb n : Nat) : Nat → MacState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | i+1 => rowRegister (rowsRegister mem pa pb n i).memory pa pb n i

/-- One final store reconstructs the complete original model after any
positive number of rows. No intermediate carry-store is necessary. -/
theorem rowsRegister_spec (mem : ByteArray) (pa pb n j : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hpa : pa+32*n ≤ 8192) (hpb : pb+32*n ≤ 8192) :
    setCarry (rowsRegister mem pa pb n (j+1)).memory
      (rowsRegister mem pa pb n (j+1)).carry = rowsMem mem pa pb n (j+1) := by
  induction j with
  | zero => exact rowRegister_spec mem pa pb n 0 hn32
  | succ j ih =>
    change setCarry (rowRegister (rowsRegister mem pa pb n (j+1)).memory pa pb n (j+1)).memory
      (rowRegister (rowsRegister mem pa pb n (j+1)).memory pa pb n (j+1)).carry =
      rowMem (rowsMem mem pa pb n (j+1)) pa pb n (j+1)
    rw [← ih, rowMem_setCarry _ _ pa pb n (j+1) hn hn32 hpa hpb]
    exact rowRegister_spec _ pa pb n (j+1) hn32

#print axioms l1Step_setCarry
#print axioms l2Step_setCarry
#print axioms midMem_setCarry
#print axioms tailRegisterMem_spec
#print axioms rowRegister_spec
#print axioms rowsRegister_spec

end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryMemory
