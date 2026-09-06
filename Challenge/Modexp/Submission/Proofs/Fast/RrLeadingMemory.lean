import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTraceComposition

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Memory frame for the direct RR counter helper

This private development module is independent of the future concrete
Artifact and of `Fast.Exp`.  It records the memory and active-word facts that
will bridge the functional helper trace to the inherited RR loop.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

/-- Loading the established limb-size word at 9344 does not expand memory
once the setup frame has allocated at least 298 words. -/
theorem loadActiveWords_eq (template : State)
    (hactive : 298 ≤ template.activeWords.toNat) :
    loadActiveWords template = template.activeWords := by
  unfold loadActiveWords State.activeWordsAfterUInt256
  rw [activeWordsAfter_eq_of_end_le]
  · exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  · omega

/-- Both ranges touched by the CC-to-RR `MCOPY` are already inside the
298-word setup frame, so the direct helper preserves the active-word count. -/
theorem copiedActiveWords_eq (template : State) (n : Nat)
    (hn32 : n ≤ 32) (hactive : 298 ≤ template.activeWords.toNat) :
    copiedActiveWords template n = template.activeWords := by
  unfold copiedActiveWords State.activeWordsAfterUInt256_2
  rw [loadActiveWords_eq template hactive]
  change UInt256.ofNat
      (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter template.activeWords.toNat
          6144 (32 * n)) 5120 (32 * n)) = template.activeWords
  have hdest : MachineState.activeWordsAfter template.activeWords.toNat
      6144 (32 * n) = template.activeWords.toNat := by
    apply activeWordsAfter_eq_of_end_le
    omega
  rw [hdest]
  have hsrc : MachineState.activeWordsAfter template.activeWords.toNat
      5120 (32 * n) = template.activeWords.toNat := by
    apply activeWordsAfter_eq_of_end_le
    omega
  rw [hsrc]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-- A word at or above byte 7168 is disjoint from the copied RR destination. -/
theorem copiedMemory_readWord_above (mem : ByteArray) (n addr : Nat)
    (hn32 : n ≤ 32) (haddr : 7168 ≤ addr) :
    MachineState.readWord (copiedMemory mem n) addr =
      MachineState.readWord mem addr := by
  unfold copiedMemory
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

theorem copiedMemory_sizeWord (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readWord (copiedMemory mem n) 9344 =
      MachineState.readWord mem 9344 :=
  copiedMemory_readWord_above mem n 9344 hn32 (by omega)

theorem copiedMemory_bsizeWord (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readWord (copiedMemory mem n) 9376 =
      MachineState.readWord mem 9376 :=
  copiedMemory_readWord_above mem n 9376 hn32 (by omega)

theorem copiedMemory_esizeWord (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readWord (copiedMemory mem n) 9408 =
      MachineState.readWord mem 9408 :=
  copiedMemory_readWord_above mem n 9408 hn32 (by omega)

theorem copiedMemory_msizeWord (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readWord (copiedMemory mem n) 9440 =
      MachineState.readWord mem 9440 :=
  copiedMemory_readWord_above mem n 9440 hn32 (by omega)

theorem copiedMemory_exponentPtrWord (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readWord (copiedMemory mem n) 9472 =
      MachineState.readWord mem 9472 :=
  copiedMemory_readWord_above mem n 9472 hn32 (by omega)

theorem copiedMemory_exponentSizeWord (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readWord (copiedMemory mem n) 9504 =
      MachineState.readWord mem 9504 :=
  copiedMemory_readWord_above mem n 9504 hn32 (by omega)

/-- An entire byte range ending before the RR destination is unchanged. -/
theorem copiedMemory_readPadded_before (mem : ByteArray)
    (n ptr count : Nat) (hbefore : ptr + count ≤ 6144) :
    MachineState.readPadded (copiedMemory mem n) ptr count =
      MachineState.readPadded mem ptr count := by
  unfold copiedMemory
  apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
  left
  exact hbefore

theorem copiedMemory_modulusBlock (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readPadded (copiedMemory mem n) 0 (32 * n) =
      MachineState.readPadded mem 0 (32 * n) :=
  copiedMemory_readPadded_before mem n 0 (32 * n) (by omega)

theorem copiedMemory_accumulatorBlock (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readPadded (copiedMemory mem n) 1024 (32 * n) =
      MachineState.readPadded mem 1024 (32 * n) :=
  copiedMemory_readPadded_before mem n 1024 (32 * n) (by omega)

theorem copiedMemory_baseBlock (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readPadded (copiedMemory mem n) 2048 (32 * n) =
      MachineState.readPadded mem 2048 (32 * n) :=
  copiedMemory_readPadded_before mem n 2048 (32 * n) (by omega)

theorem copiedMemory_oneBlock (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readPadded (copiedMemory mem n) 3072 (32 * n) =
      MachineState.readPadded mem 3072 (32 * n) :=
  copiedMemory_readPadded_before mem n 3072 (32 * n) (by omega)

theorem copiedMemory_r1Block (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readPadded (copiedMemory mem n) 4096 (32 * n) =
      MachineState.readPadded mem 4096 (32 * n) :=
  copiedMemory_readPadded_before mem n 4096 (32 * n) (by omega)

theorem copiedMemory_ccBlock (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    MachineState.readPadded (copiedMemory mem n) 5120 (32 * n) =
      MachineState.readPadded mem 5120 (32 * n) :=
  copiedMemory_readPadded_before mem n 5120 (32 * n) (by omega)

/-- Every represented block ending no later than the RR destination survives
the copy.  This packages the only disjointness argument needed for all legacy
blocks from modulus through CC. -/
theorem fastRepresents_copied_before (mem : ByteArray)
    (n ptr count value : Nat) (hbefore : ptr + 32 * count ≤ 6144)
    (hrep : Model.FastRepresents mem ptr count value) :
    Model.FastRepresents (copiedMemory mem n) ptr count value := by
  unfold copiedMemory
  apply Csub.fastRepresents_mcopy_disjoint
  · right
    exact hbefore
  · exact hrep

/-- The source CC representation is reproduced at RR. -/
theorem fastRepresents_rr_of_cc (mem : ByteArray) (n value : Nat)
    (hn2 : 2 ≤ n) (hcc : Model.FastRepresents mem 5120 n value) :
    Model.FastRepresents (copiedMemory mem n) 6144 n value := by
  unfold copiedMemory
  exact Csub.fastRepresents_mcopy mem 5120 6144 n value (by omega) hcc

theorem fastRepresents_modulus_preserved (mem : ByteArray) (n value : Nat)
    (hn32 : n ≤ 32) (hrep : Model.FastRepresents mem 0 n value) :
    Model.FastRepresents (copiedMemory mem n) 0 n value :=
  fastRepresents_copied_before mem n 0 n value (by omega) hrep

theorem fastRepresents_accumulator_preserved (mem : ByteArray) (n value : Nat)
    (hn32 : n ≤ 32) (hrep : Model.FastRepresents mem 1024 n value) :
    Model.FastRepresents (copiedMemory mem n) 1024 n value :=
  fastRepresents_copied_before mem n 1024 n value (by omega) hrep

theorem fastRepresents_base_preserved (mem : ByteArray) (n value : Nat)
    (hn32 : n ≤ 32) (hrep : Model.FastRepresents mem 2048 n value) :
    Model.FastRepresents (copiedMemory mem n) 2048 n value :=
  fastRepresents_copied_before mem n 2048 n value (by omega) hrep

theorem fastRepresents_one_preserved (mem : ByteArray) (n value : Nat)
    (hn32 : n ≤ 32) (hrep : Model.FastRepresents mem 3072 n value) :
    Model.FastRepresents (copiedMemory mem n) 3072 n value :=
  fastRepresents_copied_before mem n 3072 n value (by omega) hrep

theorem fastRepresents_r1_preserved (mem : ByteArray) (n value : Nat)
    (hn32 : n ≤ 32) (hrep : Model.FastRepresents mem 4096 n value) :
    Model.FastRepresents (copiedMemory mem n) 4096 n value :=
  fastRepresents_copied_before mem n 4096 n value (by omega) hrep

theorem fastRepresents_cc_preserved (mem : ByteArray) (n value : Nat)
    (hn32 : n ≤ 32) (hrep : Model.FastRepresents mem 5120 n value) :
    Model.FastRepresents (copiedMemory mem n) 5120 n value :=
  fastRepresents_copied_before mem n 5120 n value (by omega) hrep

/-- Artifact-independent counterpart of the four-field invariant expected by
the inherited RR chain.  Keeping this small interface here lets the eventual
`Fast.Exp.RrInv` bridge be a constructor application rather than another
memory proof. -/
structure RrCopyInv (mem : ByteArray) (n mm R : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  r1 : Model.FastRepresents mem 4096 n (R % mm)
  cc : Model.FastRepresents mem 5120 n (Limbs.radix * R % mm)
  rr : Model.FastRepresents mem 6144 n (Limbs.radix * R % mm)

/-- Copying CC to RR establishes the exact residue required at the direct
counter helper's RR-loop rejoin while preserving modulus, R1, and CC. -/
theorem rrCopyInv_after_copy (mem : ByteArray) (n mm R : Nat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (R % mm))
    (hcc : Model.FastRepresents mem 5120 n (Limbs.radix * R % mm)) :
    RrCopyInv (copiedMemory mem n) n mm R where
  modulus := fastRepresents_modulus_preserved mem n mm hn32 hmod
  r1 := fastRepresents_r1_preserved mem n (R % mm) hn32 hr1
  cc := fastRepresents_cc_preserved mem n (Limbs.radix * R % mm) hn32 hcc
  rr := fastRepresents_rr_of_cc mem n (Limbs.radix * R % mm) hn2 hcc

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory

