import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

/-- Writing an already-present byte window is an exact memory identity. -/
theorem storeWord_id (mem : ByteArray) (a : Nat) (w : UInt256)
    (hsize : a+32 ≤ mem.size)
    (hbytes : MachineState.readPadded mem a 32 = Data.Bytes.natToBytesPadded w.toNat 32) :
    storeWord mem a w = mem := by
  apply ByteArray.ext_getElem
  · rw [storeWord_size]; omega
  · intro i hleft hright
    rw [← getD0_eq_getElem _ _ hleft, ← getD0_eq_getElem _ _ hright]
    simp only [storeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hi : a ≤ i ∧ i < a+32
    · rw [if_pos hi]
      have h := congrArg (fun b : ByteArray => b[i-a]?.getD 0) hbytes
      rw [readPadded_getElem?_getD, if_pos (by omega),
        show a+(i-a)=i by omega] at h
      exact h.symm
    · rw [if_neg hi]

theorem padded_mpZeroed (s : State) (mem : ByteArray) (n a : Nat)
    (hlo : 8192 ≤ a) (hhi : a+32 ≤ 8256+32*n) :
    MachineState.readPadded (mpZeroed s mem n) a 32 = Data.Bytes.natToBytesPadded 0 32 := by
  apply ByteArray.ext_getElem
  · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hi hj
    have hi32 : i < 32 := by simpa using hi
    rw [← getD0_eq_getElem _ _ hi, ← getD0_eq_getElem _ _ hj,
      readPadded_getElem?_getD, if_pos hi32]
    simp only [mpZeroed, MachineState.writeBytes_getElem?_getD, readPadded_size]
    rw [if_pos (by omega), readPadded_getElem?_getD, if_pos (by omega),
      getElem?_getD_eq_zero_of_size_le _ _ (by omega),
      natToBytesPadded_zero_byte 32 i hi32]

theorem storeWord_mpZeroed (s : State) (mem : ByteArray) (n a : Nat)
    (hlo : 8192 ≤ a) (hhi : a+32 ≤ 8256+32*n) :
    storeWord (mpZeroed s mem n) a (UInt256.ofNat 0) = mpZeroed s mem n := by
  apply storeWord_id
  · simp only [mpZeroed, MachineState.writeBytes_size, readPadded_size]
    rw [if_neg (by omega)]
    omega
  · exact padded_mpZeroed s mem n a hlo hhi

def initial (s : State) (mem : ByteArray) (n : Nat) : CachedMemory :=
  ⟨mpZeroed s mem n, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩

theorem virtual_initial (s : State) (mem : ByteArray) (n : Nat) (hn : 3 ≤ n) :
    (initial s mem n).virtual = mpZeroed s mem n := by
  unfold initial CachedMemory.virtual
  rw [storeWord_mpZeroed s mem n 8256 (by omega) (by omega),
    storeWord_mpZeroed s mem n 8288 (by omega) (by omega),
    storeWord_mpZeroed s mem n 8320 (by omega) (by omega)]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit.virtual_initial
