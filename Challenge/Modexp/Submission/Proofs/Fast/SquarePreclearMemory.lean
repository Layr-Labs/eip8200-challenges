import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquarePreclearMemory

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

private theorem writeBytes_comm_disjoint (bs b1 b2 : ByteArray) (a1 a2 : Nat)
    (h1 : b1.size ≠ 0) (h2 : b2.size ≠ 0)
    (hd : a1 + b1.size ≤ a2 ∨ a2 + b2.size ≤ a1) :
    MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2 =
      MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1 := by
  have hsize : (MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2).size =
      (MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1).size := by
    rw [MachineState.writeBytes_size, MachineState.writeBytes_size,
      MachineState.writeBytes_size, MachineState.writeBytes_size,
      if_neg h1, if_neg h2, if_neg h2, if_neg h1]
    omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [MachineState.writeBytes_getElem?_getD]
  split_ifs <;> first | rfl | omega

private theorem stage_zero (mem : ByteArray) (pa : Nat) :
    StagedOperand.stage mem pa 0 = mem := by
  simp [StagedOperand.stage, MachineState.writeBytes]

private theorem zero_prefix_byte (s : State) (n k : Nat) (hk : k < 32) :
    (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
      (64 + 32 * n))[k]?.getD 0 =
      (Data.Bytes.natToBytesPadded 0 32)[k]?.getD 0 := by
  rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD,
    if_pos (by omega),
    Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega),
    Monpro.natToBytesPadded_zero_byte 32 k hk]

private theorem partial_after_mpZeroed (s : State) (mem : ByteArray) (n : Nat) :
    SquarePartialClear.memory (Monpro.mpZeroed s mem n) = Monpro.mpZeroed s mem n := by
  unfold SquarePartialClear.memory Monpro.mpZeroed
  have hsize :
      (SquarePartialClear.memory (Monpro.mpZeroed s mem n)).size =
        (Monpro.mpZeroed s mem n).size := by
    simp only [SquarePartialClear.memory, Monpro.mpZeroed,
      MachineState.writeBytes_size,
      Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [SquarePartialClear.memory, Monpro.mpZeroed,
    MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    Challenge.EvmProof.Memory.readPadded_size]
  by_cases hp : 2048 ≤ i ∧ i < 2080
  · rw [if_pos hp, if_pos (by omega)]
    exact (zero_prefix_byte s n (i - 2048) (by omega)).symm
  · rw [if_neg hp]

theorem mpZeroed_idem (s : State) (mem : ByteArray) (n : Nat) :
    Monpro.mpZeroed s (Monpro.mpZeroed s mem n) n = Monpro.mpZeroed s mem n := by
  unfold Monpro.mpZeroed
  have hsize :
      (MachineState.writeBytes
          (MachineState.writeBytes mem
            (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
              (64 + 32 * n)) 2048)
          (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
            (64 + 32 * n)) 2048).size =
        (MachineState.writeBytes mem
          (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
            (64 + 32 * n)) 2048).size := by
    simp only [MachineState.writeBytes_size,
      Challenge.EvmProof.Memory.readPadded_size]
    split_ifs <;> omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi',
    MachineState.writeBytes_getElem?_getD
      (MachineState.writeBytes mem
        (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
          (64 + 32 * n)) 2048)
      (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
        (64 + 32 * n)) 2048 i]
  split_ifs with h
  · rw [MachineState.writeBytes_getElem?_getD mem, if_pos h]
  · rfl

theorem stage_preclear_comm (s : State) (mem : ByteArray) (pa n : Nat)
    (hn : n ≤ 8) (hpa : pa + 32 * n ≤ 2048 ∨ pa = 2368) :
    StagedOperand.stage (Monpro.mpZeroed s mem n) pa n =
      Monpro.mpZeroed s (StagedOperand.stage mem pa n) n := by
  have hsource :
      MachineState.readPadded
          (MachineState.writeBytes mem
            (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
              (64 + 32 * n)) 2048)
          pa (32 * n) =
        MachineState.readPadded mem pa (32 * n) := by
    apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
    rw [Challenge.EvmProof.Memory.readPadded_size]
    rcases hpa with hpa | rfl
    · exact Or.inl hpa
    · exact Or.inr (by omega)
  by_cases hn0 : n = 0
  · subst n
    simp only [stage_zero]
  · unfold Monpro.mpZeroed StagedOperand.stage
    rw [hsource]
    apply writeBytes_comm_disjoint
    · rw [Challenge.EvmProof.Memory.readPadded_size]
      omega
    · rw [Challenge.EvmProof.Memory.readPadded_size]
      omega
    · left
      rw [Challenge.EvmProof.Memory.readPadded_size]
      omega

theorem model_stage_preclear_eq (s : State) (mem : ByteArray) (pa n : Nat)
    (hn : n ≤ 8) (hpa : pa + 32 * n ≤ 2048 ∨ pa = 2368) :
    Monpro.mpZeroed s (StagedOperand.stage (Monpro.mpZeroed s mem n) pa n) n =
      Monpro.mpZeroed s (StagedOperand.stage mem pa n) n := by
  rw [stage_preclear_comm s mem pa n hn hpa, mpZeroed_idem]

theorem partial_stage_preclear_eq (s : State) (mem : ByteArray) (pa n : Nat)
    (hn : n ≤ 8) (hpa : pa + 32 * n ≤ 2048 ∨ pa = 2368) :
    SquarePartialClear.memory
        (StagedOperand.stage (Monpro.mpZeroed s mem n) pa n) =
      Monpro.mpZeroed s (StagedOperand.stage mem pa n) n := by
  rw [stage_preclear_comm s mem pa n hn hpa]
  exact partial_after_mpZeroed s (StagedOperand.stage mem pa n) n

end Challenge.Modexp.Submission.Proofs.Fast.SquarePreclearMemory
