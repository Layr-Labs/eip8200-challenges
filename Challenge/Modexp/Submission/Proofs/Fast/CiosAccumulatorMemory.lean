import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorMemory
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Monpro CiosCarryMemory

def setTN (mem : ByteArray) (v : UInt256) : ByteArray := writeWord mem 8224 v

theorem setTN_writeWord (mem : ByteArray) (a : Nat) (v t : UInt256)
    (ha : a+32 ≤ 8224 ∨ 8256 ≤ a) :
    setTN (writeWord mem a v) t = writeWord (setTN mem t) a v :=
  writeWord_comm mem a 8224 v t ha

theorem read_setTN (mem : ByteArray) (t : UInt256) (a : Nat)
    (ha : a+32 ≤ 8224 ∨ 8256 ≤ a) :
    MachineState.readWord (setTN mem t) a = MachineState.readWord mem a := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [BytesLemmas.natToBytesPadded_size] using ha

theorem read_setTN_same (mem : ByteArray) (t : UInt256) :
    MachineState.readWord (setTN mem t) 8224 = t := by
  change MachineState.readWord (MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded t.toNat 32) 8224) 8224 = t
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt mem 8224 t.toNat t.val.isLt]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat t).symm

theorem l2Step_setTN (mem : ByteArray) (t mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 32) :
    (l2Step (setTN mem t) mu c0 n k).memory =
      setTN (l2Step mem mu c0 n k).memory t ∧
    (l2Step (setTN mem t) mu c0 n k).carry = (l2Step mem mu c0 n k).carry := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hx : 32*(n-2-k)+32 ≤ 8224 := by omega
    have ht : 8256 ≤ 8256+32*(n-2-k) := by omega
    have hs : 8256 ≤ 8256+32*(n-1-k) := by omega
    simp only [l2Step, ih.1, ih.2,
      read_setTN _ t _ (Or.inl hx), read_setTN _ t _ (Or.inr ht)]
    constructor
    · exact (setTN_writeWord _ _ _ t (Or.inr hs)).symm
    · trivial

/-- Actual final writes when the middle accumulator sum is carried in a register. -/
def tailWithTN (mem : ByteArray) (c bit t : UInt256) : ByteArray :=
  writeWord (writeWord mem 8256 (t+c)) 8224 (bit + UInt256.lt (t+c) c)

theorem tailWithTN_eq (mem : ByteArray) (c bit t : UInt256) :
    tailWithTN mem c bit t = tailRegisterMem (setTN mem t) c bit := by
  unfold tailRegisterMem tailMem1
  rw [read_setTN_same]
  change _ = writeWord (writeWord (setTN mem t) 8256 (t+c)) 8224 _
  rw [← setTN_writeWord mem 8256 (t+c) t (Or.inr (by decide))]
  exact (writeWord_overwrite (writeWord mem 8256 (t+c)) 8224 t _).symm

def rowWithTN (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  let first := rowL1 mem pa pb n i
  let t := MachineState.readWord first.memory 8224 + first.carry
  let bit := midCarry first.memory first.carry
  let second := l2Step first.memory (rowMu first.memory n) (rowC0 first.memory n) n (n-1)
  tailWithTN second.memory second.carry bit t

/-- The middle memory write can be delayed through all correction-sweep steps
and then absorbed by the final store. Every final byte remains identical. -/
theorem rowWithTN_eq (mem : ByteArray) (pa pb n i : Nat) (hn : n ≤ 32) :
    rowWithTN mem pa pb n i = (rowRegister mem pa pb n i).memory := by
  let first := rowL1 mem pa pb n i
  let t := MachineState.readWord first.memory 8224 + first.carry
  let bit := midCarry first.memory first.carry
  have h := l2Step_setTN first.memory t (rowMu first.memory n) (rowC0 first.memory n) n (n-1) hn
  change tailWithTN (l2Step first.memory _ _ n (n-1)).memory
    (l2Step first.memory _ _ n (n-1)).carry bit t =
    tailRegisterMem (l2Step (setTN first.memory t) _ _ n (n-1)).memory
      (l2Step (setTN first.memory t) _ _ n (n-1)).carry bit
  rw [h.1, h.2]
  exact tailWithTN_eq _ _ bit t

def rowsWithTN (mem : ByteArray) (pa pb n : Nat) : Nat → ByteArray
  | 0 => mem
  | i+1 => rowWithTN (rowsWithTN mem pa pb n i) pa pb n i

theorem rowsWithTN_eq (mem : ByteArray) (pa pb n j : Nat) (hn : n ≤ 32) :
    rowsWithTN mem pa pb n j = (rowsRegister mem pa pb n j).memory := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rowsWithTN, rowsRegister, ih, rowWithTN_eq _ _ _ _ _ hn]

#print axioms rowsWithTN_eq
end Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorMemory
