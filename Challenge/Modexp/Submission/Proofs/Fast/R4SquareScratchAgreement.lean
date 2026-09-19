import Challenge.Modexp.Submission.Proofs.Fast.R4Loop
import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R4SquareScratchAgreement

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro R4Bridge R4Loop

/-- The two entry memories agree outside the R4 output window. -/
private theorem entry_byte_eq (s : State) (mem : ByteArray) (i : Nat)
    (hi : i < 2080 ∨ 2240 ≤ i) :
    (SquarePartialClear.memory mem)[i]?.getD 0 =
      (Monpro.mpZeroed s mem 4)[i]?.getD 0 := by
  rcases hi with hi | hi
  · by_cases hlow : i < 2048
    · simp only [SquarePartialClear.memory, Monpro.mpZeroed,
        MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
        Challenge.EvmProof.Memory.readPadded_size]
      rw [if_neg (by omega), if_neg (by omega)]
    · have hlo : 2048 ≤ i := by omega
      have hp := SquarePartialClear.scratchZero mem i hlo (by omega)
      have hm := (R8RowZeroExact.scratchZero_mpZeroed s mem 4 (by norm_num))
        i hlo (by omega)
      exact hp.trans hm.symm
  · simp only [SquarePartialClear.memory, Monpro.mpZeroed,
      MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      Challenge.EvmProof.Memory.readPadded_size]
    rw [if_neg (by omega), if_neg (by omega)]

private theorem partial_size (mem : ByteArray) :
    (SquarePartialClear.memory mem).size = max mem.size 2080 := by
  unfold SquarePartialClear.memory
  rw [MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    if_neg (by decide)]
  norm_num

private theorem mpZeroed_size (s : State) (mem : ByteArray) :
    (Monpro.mpZeroed s mem 4).size = max mem.size 2240 := by
  unfold Monpro.mpZeroed
  rw [MachineState.writeBytes_size, Challenge.EvmProof.Memory.readPadded_size,
    if_neg (by decide)]
  norm_num

private theorem r4Mem_size (mem : ByteArray) (W : R4Math.W5) :
    (R4Bridge.r4Mem mem W).size = max mem.size 2240 := by
  simp only [R4Bridge.r4Mem, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  split_ifs <;> omega

private theorem r4Mem_eq_of_base (s : State) (mem : ByteArray) (W : R4Math.W5) :
    R4Bridge.r4Mem (SquarePartialClear.memory mem) W =
      R4Bridge.r4Mem (Monpro.mpZeroed s mem 4) W := by
  have hsize :
      (R4Bridge.r4Mem (SquarePartialClear.memory mem) W).size =
        (R4Bridge.r4Mem (Monpro.mpZeroed s mem 4) W).size := by
    rw [r4Mem_size, r4Mem_size, partial_size, mpZeroed_size]
    simp [Nat.max_assoc]
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [R4Bridge.r4Mem, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  split_ifs <;> first | rfl | omega | exact entry_byte_eq s mem i (by omega)

/-- The exact R4 row memory is unchanged by replacing the partial clear with the
full four-limb clear. -/
theorem rows4_partial_eq (s : State) (mem : ByteArray) :
    R4Bridge.rows4 (SquarePartialClear.memory mem) =
      R4Bridge.rows4 (Monpro.mpZeroed s mem 4) := by
  have hread (addr : Nat) (hout : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
      MachineState.readWord (SquarePartialClear.memory mem) addr =
        MachineState.readWord (Monpro.mpZeroed s mem 4) addr := by
    exact
      (SquarePartialClear.readWord_outside mem addr (by
        rcases hout with h | h <;> omega)).trans
        (SquareResult.readWord_mpZeroed_far s mem 4 addr (by
          rcases hout with h | h <;> omega)).symm
  have hfinal :
      R4Bridge.r4Final (SquarePartialClear.memory mem) maxWord
          (MachineState.readWord (SquarePartialClear.memory mem) 96)
          (MachineState.readWord (SquarePartialClear.memory mem) 64)
          (MachineState.readWord (SquarePartialClear.memory mem) 32)
          (MachineState.readWord (SquarePartialClear.memory mem) 2720) =
        R4Bridge.r4Final (Monpro.mpZeroed s mem 4) maxWord
          (MachineState.readWord (Monpro.mpZeroed s mem 4) 96)
          (MachineState.readWord (Monpro.mpZeroed s mem 4) 64)
          (MachineState.readWord (Monpro.mpZeroed s mem 4) 32)
          (MachineState.readWord (Monpro.mpZeroed s mem 4) 2720) := by
    unfold R4Bridge.r4Final
    rw [hread 2464 (Or.inr (by omega)),
      hread 2432 (Or.inr (by omega)),
      hread 2400 (Or.inr (by omega)),
      hread 2368 (Or.inr (by omega)),
      hread 96 (Or.inl (by omega)),
      hread 64 (Or.inl (by omega)),
      hread 32 (Or.inl (by omega)),
      hread 2720 (Or.inr (by omega))]
  unfold R4Bridge.rows4
  rw [hfinal]
  exact r4Mem_eq_of_base s mem _

private theorem r4Round_partial_eq (s : State) (mem : ByteArray) (k : Nat) :
    R4Loop.r4Round k (SquarePartialClear.memory mem) =
      R4Loop.r4Round k (Monpro.mpZeroed s mem 4) := by
  unfold R4Loop.r4Round
  rw [rows4_partial_eq s mem]

/-- A positive R4 run has the same memory after partial or full entry clearing. -/
theorem r4RunMem_partial_eq (s : State) (mem : ByteArray) (k : Nat) (hk : 1 ≤ k) :
    R4Loop.r4RunMem k (SquarePartialClear.memory mem) =
      R4Loop.r4RunMem k (Monpro.mpZeroed s mem 4) := by
  cases k with
  | zero => omega
  | succ j =>
      rw [R4Loop.r4RunMem_succ, R4Loop.r4RunMem_succ,
        r4Round_partial_eq s mem j]

end Challenge.Modexp.Submission.Proofs.Fast.R4SquareScratchAgreement
