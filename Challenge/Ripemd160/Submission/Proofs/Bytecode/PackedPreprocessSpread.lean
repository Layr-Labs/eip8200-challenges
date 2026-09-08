import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.EvmProof.Stepper

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Packed preprocessing spread trace

The packed runtime reads a 32-byte word for each message word, but `AND
0xffffffff` retains only the last four bytes of that read.  Earlier descending
stores overlap the unused prefix of some later reads.  The four-byte source
tail is disjoint from every spread destination, so it remains frozen against
the memory at loop entry.

This module states that narrow invariant, proves that the actual descending
recurrence equals `PackedGapInvariant.spreadWords`, and gives the generic
six-instruction evaluator theorem for one spread group.  The artifact-specific
composition of all sixteen groups is intentionally separate.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpread

open Challenge.Ripemd160 Challenge.EvmProof
open Challenge.EvmProof.Word
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open PackedPreprocessLayout

/-- Execute a straight instruction list, requiring every intermediate state to
remain running.  Kept local so the preprocessing memory proof does not import
the round-template closure. -/
def runInstrSeq : List Instr → State → Option State
  | [], s => some s
  | instruction :: rest, s =>
      match Challenge.EvmProof.Stepper.runInstr instruction s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runInstrSeq rest next
              | _ => none

def pcAfter (pc : UInt256) : List Instr → UInt256
  | [] => pc
  | instruction :: rest =>
      pcAfter (pc + UInt256.ofNat instruction.size) rest

/-- The four bytes retained by the spread group's `AND 0xffffffff`. -/
def lowFour (memory : ByteArray) (n : Nat) : Nat :=
  EVM.Precompile.bytesToNatPadded memory (sourceAddress n + 28) 4

/-- Projecting an EVM memory word to `UInt32` depends only on its last four
bytes. -/
theorem toUInt32_readWord_eq_lowFour (memory : ByteArray) (n : Nat) :
    Word.toUInt32 (MachineState.readWord memory (sourceAddress n)) =
      Word.toUInt32 (UInt256.ofNat (lowFour memory n)) := by
  apply UInt32.toNat_inj.mp
  rw [Word.toUInt32_toNat, Word.toUInt32_toNat,
    Challenge.EvmProof.Bytes.readWord_toNat]
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    memory (sourceAddress n) 28 4
  rw [show 28 + 4 = 32 by norm_num] at hsplit
  rw [hsplit]
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    memory (sourceAddress n + 28) 4
  have htail256 : lowFour memory n < 2 ^ 256 :=
    htail.trans (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt htail256]
  rw [show 256 ^ 4 = 2 ^ 32 by norm_num]
  simp [lowFour, Nat.add_mod]

/-- Equality of exactly the source windows used by all sixteen groups. -/
def SourceTailsEq (base current : ByteArray) : Prop :=
  ∀ n, n < 16 → lowFour current n = lowFour base n

theorem SourceTailsEq.refl (memory : ByteArray) :
    SourceTailsEq memory memory := by
  intro _ _
  rfl

/-- A destination word store cannot touch any retained four-byte source
window. -/
theorem lowFour_storeWord (memory : ByteArray) (value : UInt256) (n k : Nat)
    (hn : n < 16) (hk : k < 16) :
    lowFour
        (PackedGapInvariant.storeWord memory (destinationAddress k) value) n =
      lowFour memory n := by
  unfold lowFour PackedGapInvariant.storeWord
  unfold EVM.Precompile.bytesToNatPadded
  rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint]
  right
  have hsize :
      (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  exact destination_before_source_tail n k hn hk

theorem SourceTailsEq.storeWord {base current : ByteArray}
    (h : SourceTailsEq base current) (value : UInt256) (k : Nat)
    (hk : k < 16) :
    SourceTailsEq base
      (PackedGapInvariant.storeWord current (destinationAddress k) value) := by
  intro n hn
  rw [lowFour_storeWord current value n k hn hk]
  exact h n hn

/-- Equal retained source windows imply equal masked spread values. -/
theorem spreadValue_eq_of_sourceTails {base current : ByteArray}
    (h : SourceTailsEq base current) (n : Nat) (hn : n < 16) :
    spreadValue current n = spreadValue base n := by
  change Word.mask32 (MachineState.readWord current (sourceAddress n)) =
    Word.mask32 (MachineState.readWord base (sourceAddress n))
  rw [Word.mask32_eq_ofUInt32, Word.mask32_eq_ofUInt32,
    toUInt32_readWord_eq_lowFour, toUInt32_readWord_eq_lowFour, h n hn]

/-- The memory recurrence executed by the descending groups.  The selected
word is intentionally read from the current memory; the invariant below is
what justifies freezing it against the loop-entry memory. -/
def runtimeSpread : Nat → ByteArray → ByteArray
  | 0, memory => memory
  | n + 1, memory =>
      runtimeSpread n
        (PackedGapInvariant.storeWord memory (destinationAddress n)
          (spreadValue memory n))

theorem runtimeSpread_eq_spreadWords (base current : ByteArray) (n : Nat)
    (hn : n ≤ 16) (htails : SourceTailsEq base current) :
    runtimeSpread n current =
      PackedGapInvariant.spreadWords (spreadValue base) n current := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih =>
      rw [runtimeSpread, PackedGapInvariant.spreadWords,
        spreadValue_eq_of_sourceTails htails n (by omega)]
      simpa only [destinationAddress] using
        ih (PackedGapInvariant.storeWord current (destinationAddress n)
            (spreadValue base n)) (by omega)
          (htails.storeWord (spreadValue base n) n (by omega))

theorem runtimeSpread_full (memory : ByteArray) :
    runtimeSpread 16 memory = spreadMemory memory := by
  exact runtimeSpread_eq_spreadWords memory memory 16 (Nat.le_refl 16)
    (SourceTailsEq.refl memory)

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

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  have hofNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
    cases w with
    | mk value => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, hofNat]

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem explicit_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    UInt256.add (u + UInt256.ofNat a) (UInt256.ofNat b) =
      u + UInt256.ofNat (a + b) := by
  change (u + UInt256.ofNat a) + UInt256.ofNat b =
    u + UInt256.ofNat (a + b)
  exact word_add_ofNat_assoc u a b

private theorem activeWordsAfterUInt256_congr (s t : State)
    (h : s.activeWords = t.activeWords) (offset size : Nat) :
    s.activeWordsAfterUInt256 offset size =
      t.activeWordsAfterUInt256 offset size := by
  unfold State.activeWordsAfterUInt256
  rw [h]

def spreadStoreEntry (s : State) (startPC : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := startPC, stack := UInt256.ofNat mask32 :: rest }

/-- Exact memory-expansion state after the group's `MLOAD` and `MSTORE`. -/
def spreadActiveWords (s : State) (n : Nat) : UInt256 :=
  ({ s with activeWords :=
      s.activeWordsAfterUInt256 (sourceAddress n) 32 }).activeWordsAfterUInt256
    (destinationAddress n) 32

theorem spreadActiveWords_eq (s : State) (n : Nat) (hn : n < 16)
    (hactive : 11 ≤ s.activeWords.toNat) :
    spreadActiveWords s n = s.activeWords := by
  have hload :
      s.activeWordsAfterUInt256 (sourceAddress n) 32 = s.activeWords := by
    apply activeWordsAfterUInt256_eq
    unfold sourceAddress
    omega
  have hstore :
      s.activeWordsAfterUInt256 (destinationAddress n) 32 = s.activeWords := by
    apply activeWordsAfterUInt256_eq
    unfold destinationAddress
    omega
  simpa [spreadActiveWords, hload] using hstore

def spreadStoreReturned (s : State) (endPC : UInt256) (n : Nat)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := UInt256.ofNat mask32 :: rest
    memory := PackedGapInvariant.storeWord s.memory (destinationAddress n)
      (spreadValue s.memory n)
    activeWords := spreadActiveWords s n }

set_option linter.unusedSimpArgs false in
/-- Generic evaluator theorem for one exact six-instruction spread group. -/
theorem runInstrSeq_spreadStore (s : State) (startPC : UInt256) (n : Nat)
    (rest : List UInt256) (hn : n < 16)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq (spreadStoreTemplate n) (spreadStoreEntry s startPC rest) =
      some (spreadStoreReturned s
        (pcAfter startPC (spreadStoreTemplate n)) n rest) := by
  have hcap (m : Nat) (hm : m ≤ 3) : rest.length + m < 1024 := by
    omega
  have hsourceNat :
      (UInt256.ofNat (sourceAddress n)).toNat = sourceAddress n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    unfold sourceAddress
    omega
  have hdestinationNat :
      (UInt256.ofNat (destinationAddress n)).toNat = destinationAddress n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    unfold destinationAddress
    omega
  by_cases hn0 : n = 0
  · subst n
    simp (config := { maxSteps := 3000000 })
      [spreadStoreTemplate, spreadStoreEntry, spreadStoreReturned,
        sourceAddress, destinationAddress, destinationPush,
        PackedPreprocessLayout.mask32, PackedPreprocessLayout.push0,
        PackedPreprocessLayout.push1, PackedPreprocessLayout.push2,
        PackedPreprocessLayout.op, PackedPreprocessLayout.dup2,
        spreadValue, spreadActiveWords, PackedGapInvariant.storeWord, runInstrSeq,
        Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap,
        hsourceNat, hdestinationNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.ofNat_add_mod, UInt256.succ,
        Instr.size_push, Instr.size_op,
        Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm,
        word_add_assoc, word_add_ofNat_assoc, Nat.add_assoc]
    constructor
    · constructor
      · apply activeWordsAfterUInt256_congr
        rfl
      · rfl
    · rw [show (startPC + UInt256.ofNat 3).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 4 by
            simpa using explicit_add_ofNat_assoc startPC 3 1]
      rw [show (startPC + UInt256.ofNat 4).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 5 by
            simpa using explicit_add_ofNat_assoc startPC 4 1]
      rw [show (startPC + UInt256.ofNat 5).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 6 by
            simpa using explicit_add_ofNat_assoc startPC 5 1]
      rw [show (startPC + UInt256.ofNat 6).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 7 by
            simpa using explicit_add_ofNat_assoc startPC 6 1]
      simpa using explicit_add_ofNat_assoc startPC 7 1
  · simp (config := { maxSteps := 3000000 })
      [spreadStoreTemplate, spreadStoreEntry, spreadStoreReturned,
        destinationPush, hn0, PackedPreprocessLayout.push0,
        PackedPreprocessLayout.push1, PackedPreprocessLayout.push2,
        PackedPreprocessLayout.op, PackedPreprocessLayout.dup2,
        spreadValue, spreadActiveWords, PackedGapInvariant.storeWord,
        runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap,
        hsourceNat, hdestinationNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.ofNat_add_mod, UInt256.succ,
        Instr.size_push, Instr.size_op,
        Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm,
        word_add_assoc, word_add_ofNat_assoc, Nat.add_assoc]
    constructor
    · apply activeWordsAfterUInt256_congr
      rfl
    · rw [show (startPC + UInt256.ofNat 3).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 4 by
            simpa using explicit_add_ofNat_assoc startPC 3 1]
      rw [show (startPC + UInt256.ofNat 4).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 5 by
            simpa using explicit_add_ofNat_assoc startPC 4 1]
      rw [show (startPC + UInt256.ofNat 5).add (UInt256.ofNat 1) =
          startPC + UInt256.ofNat 6 by
            simpa using explicit_add_ofNat_assoc startPC 5 1]
      rw [show (startPC + UInt256.ofNat 6) + UInt256.ofNat 2 =
          startPC + UInt256.ofNat 8 by
            simpa using word_add_ofNat_assoc startPC 6 2]
      simpa using explicit_add_ofNat_assoc startPC 8 1

#print axioms runtimeSpread_full
#print axioms spreadActiveWords_eq
#print axioms runInstrSeq_spreadStore

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpread
