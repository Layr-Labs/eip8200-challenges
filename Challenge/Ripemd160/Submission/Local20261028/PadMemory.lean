import Challenge.Ripemd160.Submission.Local20261028.PadValues
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def length (n : Fin 3) : UInt256 := UInt256.ofNat (64*(n.val+1))
def memory (n : Fin 3) : ByteArray := StaggerTablePad.padRealChain ByteArray.empty (length n)
def storedByte (prior : Nat → UInt8) (address : Nat) (value : UInt256) (i : Nat) : UInt8 :=
  if address ≤ i ∧ i < address + 32 then
    UInt8.ofNat (value.toNat / 256 ^ (32 - 1 - (i-address)) % 256)
  else prior i

theorem write_word_byte (memory : ByteArray) (address : Nat) (value : UInt256) (i : Nat) :
    (PairedScheduleMemory.writeWord memory address value)[i]?.getD 0 =
      storedByte (fun j => memory[j]?.getD 0) address value i := by
  rw [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  unfold storedByte
  by_cases h : address ≤ i ∧ i < address + 32
  · rw [if_pos h, if_pos h,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  · rw [if_neg h, if_neg h]

def padByte (n : UInt256) : Nat → UInt8 :=
  storedByte (storedByte (storedByte (storedByte (storedByte (storedByte
    (fun _ => 0) 162 (StaggerTablePad.lowDirty n)) 666 (StaggerTablePad.lowDirty n))
    144 (StaggerTablePad.lowDirty n)) 522 (UInt256.ofNat 128))
    54 (UInt256.ofNat 128)) 36 (UInt256.ofNat 128)

theorem pad_byte_model (n : UInt256) (i : Nat) :
    (StaggerTablePad.padRealChain ByteArray.empty n)[i]?.getD 0 = padByte n i := by
  simp only [StaggerTablePad.padRealChain, StaggerTablePad.lowChainOver, write_word_byte,
    StaggerTableSparse.zeroSuffix_getD]
  have hempty (j : Nat) : (ByteArray.empty[j]?).getD 0 = 0 := by rfl
  simp only [hempty, ite_self]
  rfl

def padReadNat (n : UInt256) (address : Nat) : Nat → Nat
  | 0 => 0
  | width+1 => padReadNat n address width * 256 + (padByte n (address+width)).toNat

theorem pad_read_model (n : UInt256) (address width : Nat) :
    Precompile.bytesToNatPadded (StaggerTablePad.padRealChain ByteArray.empty n)
      address width = padReadNat n address width := by
  induction width with
  | zero => simp [padReadNat]
  | succ width ih =>
    rw [Bytes.bytesToNatPadded_succ, ih, padReadNat]
    congr 2
    have hbyte (m : ByteArray) (i : Nat) :
        YulSemantics.EVM.byteFrom m.toList i = m[i]?.getD 0 := by
      rw [YulEvmCompiler.ByteArray.toList_eq_data]
      unfold YulSemantics.EVM.byteFrom
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
      rfl
    rw [hbyte, pad_byte_model]


theorem load_eq (n : Fin 3) (j : Fin 61) :
    MachineState.readWord (memory n) (18*j.val) = PadValues.load (length n) (18*j.val) := by
  have closed : ∀ n : Fin 3, ∀ j : Fin 61,
      padReadNat (length n) (18*j.val) 32 = (PadValues.load (length n) (18*j.val)).toNat := by decide
  apply Word.word_ext
  rw [memory, Bytes.readWord_toNat, pad_read_model]
  exact closed n j
#print axioms load_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadMemory
