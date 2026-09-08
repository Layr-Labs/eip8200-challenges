import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPaddingMemory

open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.EvmProof
open EvmSemantics

theorem fullCopySentinel_eq_topByte (memory input : ByteArray)
    (hbase : memory.size ≤ Padding.messageOffset) :
    MachineState.writeBytes
        (MachineState.writeBytes memory
          (MachineState.readPadded input 0 (Padding.paddedLength input.size))
          Padding.messageOffset)
        (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
      = MachineState.writeBytes (Padding.sentinelMemory memory input)
          (ByteArray.mk #[0])
          (Padding.messageOffset + Padding.paddedLength input.size - 1) := by
  have hfit := Padding.input_and_footer_fit input.size
  unfold Padding.sentinelMemory Padding.copiedMemory
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size,
      Challenge.EvmProof.Memory.readPadded_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl,
      show (ByteArray.mk #[0]).size = 1 by rfl,
      Nat.one_ne_zero, if_false]
    split <;> split <;> omega
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    rw [MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD]
    simp only [show (ByteArray.mk #[0x80]).size = 1 by rfl,
      show (ByteArray.mk #[0]).size = 1 by rfl,
      Challenge.EvmProof.Memory.readPadded_size]
    have hiTop : i < Padding.messageOffset + Padding.paddedLength input.size := by
      have hi := hi₁
      rw [MachineState.writeBytes_size, MachineState.writeBytes_size] at hi
      simp only [show (ByteArray.mk #[0x80]).size = 1 by rfl,
        Challenge.EvmProof.Memory.readPadded_size, Nat.one_ne_zero, if_false] at hi
      have hp : Padding.paddedLength input.size ≠ 0 :=
        Nat.ne_of_gt (Padding.paddedLength_pos input.size)
      have hm : memory.size ≤ Padding.messageOffset +
          Padding.paddedLength input.size := by omega
      have hn : Padding.messageOffset + input.size + 1 ≤
          Padding.messageOffset + Padding.paddedLength input.size := by omega
      rw [if_neg hp, Nat.max_eq_right hm, Nat.max_eq_left hn] at hi
      exact hi
    by_cases hbefore : i < Padding.messageOffset
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    · have hbase' : Padding.messageOffset ≤ i := by omega
      by_cases hinput : i < Padding.messageOffset + input.size
      · rw [if_neg (by omega), if_pos (by omega),
          Challenge.EvmProof.Memory.readPadded_getElem?_getD,
          if_pos (by omega), Nat.zero_add,
          if_neg (by omega), if_neg (by omega),
          if_pos ⟨hbase', hinput⟩]
      · by_cases hsentinel : i = Padding.messageOffset + input.size
        · subst i
          rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        · have hafter : Padding.messageOffset + input.size < i := by omega
          by_cases hlast : i < Padding.messageOffset + Padding.paddedLength input.size - 1
          · rw [if_neg (by omega), if_pos (by omega),
              Challenge.EvmProof.Memory.readPadded_getElem?_getD,
              if_pos (by omega), Nat.zero_add,
              if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            rw [Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
                input (i - Padding.messageOffset) (by omega),
              Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
                memory i (by omega)]
          · have hlast' : i = Padding.messageOffset +
                Padding.paddedLength input.size - 1 := by omega
            subst i
            rw [if_neg (by omega), if_pos (by omega),
              Challenge.EvmProof.Memory.readPadded_getElem?_getD,
              if_pos (by omega), Nat.zero_add,
              show Padding.messageOffset + Padding.paddedLength input.size - 1 -
                  Padding.messageOffset = Padding.paddedLength input.size - 1 by omega,
              Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
                input (Padding.paddedLength input.size - 1) (by omega),
              if_pos (by omega),
              show (Padding.messageOffset + Padding.paddedLength input.size - 1) -
                  (Padding.messageOffset + Padding.paddedLength input.size - 1) = 0 by omega]
            rfl

theorem fullCopySentinel_activeWords (active : Nat) (input : ByteArray) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active Padding.messageOffset
          (Padding.paddedLength input.size))
        (Padding.messageOffset + input.size) 1
      = MachineState.activeWordsAfter
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter active Padding.messageOffset input.size)
            (Padding.messageOffset + input.size) 1)
          (Padding.messageOffset + Padding.paddedLength input.size - 1) 1 := by
  have hp := Padding.paddedLength_pos input.size
  have hp0 : Padding.paddedLength input.size ≠ 0 := Nat.ne_of_gt hp
  by_cases hn : input.size = 0
  · simp only [MachineState.activeWordsAfter, if_pos hn, if_neg hp0,
      Nat.one_ne_zero, if_false, Nat.add_sub_cancel]
    norm_num [Padding.paddedLength, Padding.messageOffset,
      Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
  · simp only [MachineState.activeWordsAfter, if_neg hn, if_neg hp0,
      Nat.one_ne_zero, if_false, Nat.add_sub_cancel]
    have hword : (Padding.messageOffset + input.size - 1) / 32 ≤
        (Padding.messageOffset + input.size) / 32 := by omega
    have hword' : (Padding.messageOffset + input.size - 1) / 32 + 1 ≤
        (Padding.messageOffset + input.size) / 32 + 1 := by omega
    have hmax :
        (active.max ((Padding.messageOffset + input.size - 1) / 32 + 1)).max
            ((Padding.messageOffset + input.size) / 32 + 1) =
          active.max ((Padding.messageOffset + input.size) / 32 + 1) := by
      calc
        _ = active.max (((Padding.messageOffset + input.size - 1) / 32 + 1).max
              ((Padding.messageOffset + input.size) / 32 + 1)) :=
          Nat.max_assoc _ _ _
        _ = active.max ((Padding.messageOffset + input.size) / 32 + 1) :=
          congrArg (fun x => active.max x) (Nat.max_eq_right hword')
    calc
      (active.max ((Padding.messageOffset + Padding.paddedLength input.size - 1) / 32 + 1)).max
          ((Padding.messageOffset + input.size) / 32 + 1) =
          active.max (((Padding.messageOffset + Padding.paddedLength input.size - 1) / 32 + 1).max
            ((Padding.messageOffset + input.size) / 32 + 1)) := Nat.max_assoc _ _ _
      _ = active.max (((Padding.messageOffset + input.size) / 32 + 1).max
            ((Padding.messageOffset + Padding.paddedLength input.size - 1) / 32 + 1)) := by
          exact congrArg (fun x => active.max x) (Nat.max_comm _ _)
      _ = (active.max ((Padding.messageOffset + input.size) / 32 + 1)).max
            ((Padding.messageOffset + Padding.paddedLength input.size - 1) / 32 + 1) :=
          (Nat.max_assoc _ _ _).symm
      _ = ((active.max ((Padding.messageOffset + input.size - 1) / 32 + 1)).max
            ((Padding.messageOffset + input.size) / 32 + 1)).max
            ((Padding.messageOffset + Padding.paddedLength input.size - 1) / 32 + 1) := by
          exact congrArg (fun x => x.max
            ((Padding.messageOffset + Padding.paddedLength input.size - 1) / 32 + 1)) hmax.symm

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPaddingMemory
