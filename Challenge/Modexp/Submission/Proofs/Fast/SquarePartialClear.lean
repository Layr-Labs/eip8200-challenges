import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

/-- The square entry clears only the scratch word used by the exact-memory bridge. -/
def memory (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) 2048

theorem scratchZero (mem : ByteArray) : R8RowZeroExact.ScratchZero (memory mem) := by
  intro i hlo hhi
  simp only [memory, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_pos (by omega)]
  exact Monpro.natToBytesPadded_zero_byte 32 (i - 2048) (by omega)

theorem readWord_outside (mem : ByteArray) (addr : Nat)
    (hout : addr + 32 ≤ 2048 ∨ 2080 ≤ addr) :
    MachineState.readWord (memory mem) addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hout

theorem fastRepresents_outside (mem : ByteArray) (ptr n value : Nat)
    (hout : ptr + 32*n ≤ 2048 ∨ 2080 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr n value) :
    Model.FastRepresents (memory mem) ptr n value := by
  refine (Model.fastRepresents_congr (a := mem) ?_ value).1 hrep
  intro j hj
  rw [readWord_outside mem (ptr + 32*j) (by omega)]

/-- The full model clear overwrites the partial store, including its array extent. -/
theorem mpZeroed_eq (s : State) (mem : ByteArray) (n : Nat) :
    Monpro.mpZeroed s (memory mem) n = Monpro.mpZeroed s mem n := by
  have hsize : (Monpro.mpZeroed s (memory mem) n).size =
      (Monpro.mpZeroed s mem n).size := by
    simp only [Monpro.mpZeroed, memory, MachineState.writeBytes_size,
      Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [Monpro.mpZeroed, memory, MachineState.writeBytes_getElem?_getD,
    Challenge.EvmProof.Memory.readPadded_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  split_ifs <;> first | rfl | omega

theorem sqRound_eq (s : State) (n c : Nat) (mem : ByteArray) :
    SquareLoopMem.sqRound s n c (memory mem) =
      SquareLoopMem.sqRound s n c mem := by
  unfold SquareLoopMem.sqRound
  rw [mpZeroed_eq]

theorem sqRunMem_eq (s : State) (n k : Nat) (mem : ByteArray) (hk : 1 ≤ k) :
    SquareLoopMem.sqRunMem s n k (memory mem) =
      SquareLoopMem.sqRunMem s n k mem := by
  cases k with
  | zero => omega
  | succ k => rw [SquareLoopMem.sqRunMem_succ, SquareLoopMem.sqRunMem_succ, sqRound_eq]

#print axioms scratchZero
#print axioms mpZeroed_eq
#print axioms sqRunMem_eq
end Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
