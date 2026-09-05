import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Limbs
import Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory
import Mathlib.Tactic

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop

open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.EvmProof.Memory

def B : Nat := Limbs.radix

def V (memory : ByteArray) (p k : Nat) : Nat :=
  Nat.ofDigits B (Limbs.memoryLimbs memory p k)

def wordProgress (memory : ByteArray) (x t : Nat)
    (word carry0 : UInt256) : Nat → ByteArray × UInt256
  | 0 => (memory, carry0)
  | j + 1 =>
      let before := wordProgress memory x t word carry0 j
      Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep before.1 x t j word before.2

def addMulMemory (memory : ByteArray) (x t n : Nat)
    (word carry0 : UInt256) : ByteArray :=
  let progress := wordProgress memory x t word carry0 n
  Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop progress.1 t n progress.2

private theorem padded_word_size (value : Nat) :
    (Data.Bytes.natToBytesPadded value 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

private theorem memoryLimbs_succ (memory : ByteArray) (ptr count : Nat) :
    Limbs.memoryLimbs memory ptr (count + 1) =
      Limbs.memoryLimbs memory ptr count ++
        [(MachineState.readWord memory (ptr + 32 * count)).toNat] := by
  simp [Limbs.memoryLimbs, List.range_succ]

private theorem value_succ (memory : ByteArray) (ptr count : Nat) :
    V memory ptr (count + 1) =
      V memory ptr count + B ^ count *
        (MachineState.readWord memory (ptr + 32 * count)).toNat := by
  unfold V
  rw [memoryLimbs_succ, Nat.ofDigits_append]
  simp [B]

private theorem wordStep_read_disjoint (memory : ByteArray)
    (x t j readStart : Nat) (word carry : UInt256)
    (hdisjoint : readStart + 32 ≤ t + 32 * j ∨
      t + 32 * (j + 1) ≤ readStart) :
    MachineState.readWord
        (Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep memory x t j word carry).1 readStart =
      MachineState.readWord memory readStart := by
  unfold Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep
  apply readWord_writeBytes_disjoint
  rcases hdisjoint with hbefore | hafter
  · exact Or.inl hbefore
  · right
    rw [padded_word_size]
    omega

private theorem wordStep_read_future (memory : ByteArray)
    (x t j i : Nat) (word carry : UInt256) (hji : j < i) :
    MachineState.readWord
        (Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep memory x t j word carry).1
          (t + 32 * i) =
      MachineState.readWord memory (t + 32 * i) := by
  apply wordStep_read_disjoint
  exact Or.inr (by omega)

private theorem foldTop_read_disjoint (memory : ByteArray)
    (t n readStart : Nat) (carry : UInt256)
    (hdisjoint : readStart + 32 ≤ t + 32 * n ∨
      t + 32 * (n + 2) ≤ readStart) :
    MachineState.readWord
        (Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop memory t n carry) readStart =
      MachineState.readWord memory readStart := by
  rw [Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop]
  calc
    _ = MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded
            (MachineState.readWord memory (t + 32 * n) + carry).toNat 32)
          (t + 32 * n)) readStart := by
      apply readWord_writeBytes_disjoint
      rcases hdisjoint with hbefore | hafter
      · exact Or.inl (by omega)
      · right
        rw [padded_word_size]
        omega
    _ = MachineState.readWord memory readStart := by
      apply readWord_writeBytes_disjoint
      rcases hdisjoint with hbefore | hafter
      · exact Or.inl hbefore
      · right
        rw [padded_word_size]
        omega

private theorem foldTop_read_prefix (memory : ByteArray)
    (t n i : Nat) (carry : UInt256) (hi : i < n) :
    MachineState.readWord
        (Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop memory t n carry) (t + 32 * i) =
      MachineState.readWord memory (t + 32 * i) := by
  apply foldTop_read_disjoint
  exact Or.inl (by omega)

private theorem value_eq_of_readWords_eq (memory other : ByteArray)
    (ptr count : Nat)
    (hread : ∀ i, i < count →
      MachineState.readWord memory (ptr + 32 * i) =
        MachineState.readWord other (ptr + 32 * i)) :
    V memory ptr count = V other ptr count := by
  unfold V Limbs.memoryLimbs
  congr 1
  apply List.map_congr_left
  intro i hi
  exact congrArg UInt256.toNat (hread i (by simpa using hi))

private theorem wordStep_value_prefix (memory : ByteArray)
    (x t j : Nat) (word carry : UInt256) :
    V (Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep memory x t j word carry).1 t j =
      V memory t j := by
  apply value_eq_of_readWords_eq
  intro i hi
  apply wordStep_read_disjoint
  exact Or.inl (by omega)

theorem wordProgress_correct (memory : ByteArray) (x t n : Nat)
    (word carry0 : UInt256)
    (hcarry0 : carry0.toNat ≤ word.toNat)
    (hxfit : x + 32 * n < B)
    (htfit : t + 32 * (n + 2) < B)
    (hdisjoint : x + 32 * n ≤ t ∨
      t + 32 * (n + 2) ≤ x)
    (j : Nat) (hj : j ≤ n) :
    let progress := wordProgress memory x t word carry0 j
    progress.2.toNat ≤ word.toNat ∧
      (∀ i, i < n →
        MachineState.readWord progress.1 (x + 32 * i) =
          MachineState.readWord memory (x + 32 * i)) ∧
      (∀ i, j ≤ i → i < n + 2 →
        MachineState.readWord progress.1 (t + 32 * i) =
          MachineState.readWord memory (t + 32 * i)) ∧
      (∀ a, a < t ∨ t + 32 * j ≤ a →
        progress.1[a]?.getD 0 = memory[a]?.getD 0) ∧
      V progress.1 t j + B ^ j * progress.2.toNat =
        V memory t j + word.toNat * V memory x j + carry0.toNat := by
  induction j with
  | zero =>
      dsimp only [wordProgress]
      refine ⟨hcarry0, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rfl
      · intro i hji hi
        rfl
      · intro a ha
        rfl
      · simp [V, Limbs.memoryLimbs, B]
  | succ j ih =>
      have hjn : j < n := by omega
      have hprev := ih (by omega)
      dsimp only at hprev
      let before := wordProgress memory x t word carry0 j
      let after :=
        Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep before.1 x t j word before.2
      change
        after.2.toNat ≤ word.toNat ∧
          (∀ i, i < n →
            MachineState.readWord after.1 (x + 32 * i) =
              MachineState.readWord memory (x + 32 * i)) ∧
          (∀ i, j + 1 ≤ i → i < n + 2 →
            MachineState.readWord after.1 (t + 32 * i) =
              MachineState.readWord memory (t + 32 * i)) ∧
          (∀ a, a < t ∨ t + 32 * (j + 1) ≤ a →
            after.1[a]?.getD 0 = memory[a]?.getD 0) ∧
          V after.1 t (j + 1) + B ^ (j + 1) * after.2.toNat =
            V memory t (j + 1) + word.toNat * V memory x (j + 1) +
              carry0.toNat
      have hprevCarry : before.2.toNat ≤ word.toNat := by
        simpa [before] using hprev.1
      have hprevSource : ∀ i, i < n →
          MachineState.readWord before.1 (x + 32 * i) =
            MachineState.readWord memory (x + 32 * i) := by
        simpa [before] using hprev.2.1
      have hprevUnprocessed : ∀ i, j ≤ i → i < n + 2 →
          MachineState.readWord before.1 (t + 32 * i) =
            MachineState.readWord memory (t + 32 * i) := by
        simpa [before] using hprev.2.2.1
      have hprevOutside : ∀ a, a < t ∨ t + 32 * j ≤ a →
          before.1[a]?.getD 0 = memory[a]?.getD 0 := by
        simpa [before] using hprev.2.2.2.1
      have hprevValue :
          V before.1 t j + B ^ j * before.2.toNat =
            V memory t j + word.toNat * V memory x j +
              carry0.toNat := by
        simpa [before] using hprev.2.2.2.2
      have hxf : x + 32 * j < Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B := by
        have h : x + 32 * j < B := by omega
        simpa [B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using h
      have htf : t + 32 * j < Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B := by
        have h : t + 32 * j < B := by omega
        simpa [B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using h
      have hstep := Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep_correct
        before.1 x t j word before.2 hprevCarry hxf htf
      have hlow :
          (MachineState.readWord after.1 (t + 32 * j)).toNat =
            ((MachineState.readWord before.1 (x + 32 * j)).toNat *
                word.toNat +
              (MachineState.readWord before.1 (t + 32 * j)).toNat +
                before.2.toNat) % B := by
        simpa [after, before, B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using hstep.1
      have hnext : after.2.toNat =
          ((MachineState.readWord before.1 (x + 32 * j)).toNat *
              word.toNat +
            (MachineState.readWord before.1 (t + 32 * j)).toNat +
              before.2.toNat) / B := by
        simpa [after, before, B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using hstep.2.1
      have hnextLe : after.2.toNat ≤ word.toNat := by
        simpa [after, before] using hstep.2.2.1
      have hsourceAfter : ∀ i, i < n →
          MachineState.readWord after.1 (x + 32 * i) =
            MachineState.readWord memory (x + 32 * i) := by
        intro i hi
        have hwrite := wordStep_read_disjoint before.1 x t j
          (x + 32 * i) word before.2 (by
            rcases hdisjoint with hbefore | hafter
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
        calc
          MachineState.readWord after.1 (x + 32 * i) =
              MachineState.readWord before.1 (x + 32 * i) := by
                simpa [after] using hwrite
          _ = MachineState.readWord memory (x + 32 * i) :=
            hprevSource i hi
      have hUnprocessedAfter : ∀ i, j + 1 ≤ i → i < n + 2 →
          MachineState.readWord after.1 (t + 32 * i) =
            MachineState.readWord memory (t + 32 * i) := by
        intro i hji hi
        have hwrite := wordStep_read_future before.1 x t j i word
          before.2 (by omega)
        calc
          MachineState.readWord after.1 (t + 32 * i) =
              MachineState.readWord before.1 (t + 32 * i) := by
                simpa [after] using hwrite
          _ = MachineState.readWord memory (t + 32 * i) :=
            hprevUnprocessed i (by omega) hi
      have hOutsideAfter : ∀ a,
          a < t ∨ t + 32 * (j + 1) ≤ a →
            after.1[a]?.getD 0 = memory[a]?.getD 0 := by
        intro a ha
        have hstepOutside := hstep.2.2.2 a (by
          intro hwin
          rcases ha with hbefore | hafter
          · omega
          · omega)
        calc
          after.1[a]?.getD 0 = before.1[a]?.getD 0 := by
            simpa [after] using hstepOutside
          _ = memory[a]?.getD 0 := hprevOutside a (by
            rcases ha with hbefore | hafter
            · exact Or.inl hbefore
            · exact Or.inr (by omega))
      have hsource := hprevSource j hjn
      have hold := hprevUnprocessed j (by omega) (by omega)
      have hsourceNat := congrArg UInt256.toNat hsource
      have holdNat := congrArg UInt256.toNat hold
      have hsum :
          (MachineState.readWord before.1 (x + 32 * j)).toNat *
                word.toNat +
              (MachineState.readWord before.1 (t + 32 * j)).toNat +
                before.2.toNat =
            (MachineState.readWord after.1 (t + 32 * j)).toNat +
              B * after.2.toNat := by
        rw [hlow, hnext]
        simpa only using
          (Nat.mod_add_div
            ((MachineState.readWord before.1 (x + 32 * j)).toNat *
                word.toNat +
              (MachineState.readWord before.1 (t + 32 * j)).toNat +
                before.2.toNat) B).symm
      have hvalueAfter := value_succ after.1 t j
      have hprefix := wordStep_value_prefix before.1 x t j word before.2
      have hprefix' : V after.1 t j = V before.1 t j := by
        simpa [after] using hprefix
      have hvalue :
          V after.1 t (j + 1) + B ^ (j + 1) * after.2.toNat =
            V memory t (j + 1) + word.toNat * V memory x (j + 1) +
              carry0.toNat := by
        calc
          V after.1 t (j + 1) + B ^ (j + 1) * after.2.toNat =
              V after.1 t j + B ^ j *
                  (MachineState.readWord after.1 (t + 32 * j)).toNat +
                B ^ (j + 1) * after.2.toNat := by
            rw [hvalueAfter]
          _ = V before.1 t j + B ^ j *
                ((MachineState.readWord before.1 (x + 32 * j)).toNat *
                    word.toNat +
                  (MachineState.readWord before.1 (t + 32 * j)).toNat +
                    before.2.toNat) := by
            rw [hprefix']
            rw [show B ^ (j + 1) = B ^ j * B by rw [pow_succ]]
            calc
              V before.1 t j + B ^ j *
                    (MachineState.readWord after.1 (t + 32 * j)).toNat +
                  B ^ j * B * after.2.toNat =
                  V before.1 t j + B ^ j *
                    ((MachineState.readWord after.1 (t + 32 * j)).toNat +
                      B * after.2.toNat) := by ring
              _ = V before.1 t j + B ^ j *
                    ((MachineState.readWord before.1 (x + 32 * j)).toNat *
                        word.toNat +
                      (MachineState.readWord before.1 (t + 32 * j)).toNat +
                        before.2.toNat) := by rw [← hsum]
          _ = (V before.1 t j + B ^ j * before.2.toNat) +
                B ^ j *
                  ((MachineState.readWord before.1 (x + 32 * j)).toNat *
                      word.toNat +
                    (MachineState.readWord before.1 (t + 32 * j)).toNat) := by
            ring
          _ = (V memory t j + word.toNat * V memory x j +
                carry0.toNat) +
                B ^ j *
                  ((MachineState.readWord before.1 (x + 32 * j)).toNat *
                      word.toNat +
                    (MachineState.readWord before.1 (t + 32 * j)).toNat) := by
            rw [hprevValue]
          _ = V memory t (j + 1) + word.toNat * V memory x (j + 1) +
                carry0.toNat := by
            rw [value_succ memory t j, value_succ memory x j]
            rw [hsourceNat, holdNat]
            ring
      exact ⟨hnextLe, hsourceAfter, hUnprocessedAfter,
        hOutsideAfter, hvalue⟩

private theorem value_split (memory : ByteArray)
    (ptr start count : Nat) :
    V memory ptr (start + count) =
    V memory ptr start + B ^ start *
        V memory (ptr + 32 * start) count := by
  induction count with
  | zero => simp [V, Limbs.memoryLimbs, B]
  | succ count ih =>
      calc
        V memory ptr (start + (count + 1)) =
            V memory ptr (start + count) + B ^ (start + count) *
              (MachineState.readWord memory
                (ptr + 32 * (start + count))).toNat := by
                rw [show start + (count + 1) = (start + count) + 1 by omega]
                exact value_succ memory ptr (start + count)
        _ = (V memory ptr start + B ^ start *
              V memory (ptr + 32 * start) count) +
              B ^ (start + count) *
                (MachineState.readWord memory
                  (ptr + 32 * (start + count))).toNat := by rw [ih]
        _ = V memory ptr start + B ^ start *
              (V memory (ptr + 32 * start) count + B ^ count *
                (MachineState.readWord memory
                  ((ptr + 32 * start) + 32 * count)).toNat) := by
                have haddr : ptr + 32 * (start + count) =
                    (ptr + 32 * start) + 32 * count := by omega
                rw [haddr]
                rw [show B ^ (start + count) = B ^ start * B ^ count by
                  rw [Nat.pow_add]]
                ring
        _ = V memory ptr start + B ^ start *
              V memory (ptr + 32 * start) (count + 1) := by
                rw [value_succ (memory) (ptr + 32 * start) count]

private theorem value_suffix_eq (memory other : ByteArray)
    (t j n : Nat)
    (hread : ∀ i, j ≤ i → i < n + 2 →
      MachineState.readWord memory (t + 32 * i) =
        MachineState.readWord other (t + 32 * i)) :
    V memory (t + 32 * j) (n + 2 - j) =
      V other (t + 32 * j) (n + 2 - j) := by
  apply value_eq_of_readWords_eq
  intro i hi
  have hji : j ≤ j + i := by omega
  have hsum : i + j < n + 2 := (Nat.lt_sub_iff_add_lt).mp hi
  have hjiN : j + i < n + 2 := by omega
  have h := hread (j + i) hji hjiN
  have haddr : t + 32 * (j + i) = (t + 32 * j) + 32 * i := by omega
  rw [haddr] at h
  exact h

private theorem value_two_succ (memory : ByteArray) (ptr count : Nat) :
    V memory ptr (count + 2) =
      V memory ptr count + B ^ count *
          (MachineState.readWord memory (ptr + 32 * count)).toNat +
        B ^ (count + 1) *
          (MachineState.readWord memory (ptr + 32 * (count + 1))).toNat := by
  have h := value_succ memory ptr (count + 1)
  rw [show count + 2 = (count + 1) + 1 by omega] at h
  rw [value_succ memory ptr count] at h
  have haddr : ptr + 32 * (count + 1) = ptr + 32 * count + 32 := by omega
  rw [haddr] at h
  exact h

theorem wordProgress_complete (memory : ByteArray) (x t n : Nat)
    (word carry0 : UInt256)
    (hcarry0 : carry0.toNat ≤ word.toNat)
    (hxfit : x + 32 * n < B)
    (htfit : t + 32 * (n + 2) < B)
    (hdisjoint : x + 32 * n ≤ t ∨
      t + 32 * (n + 2) ≤ x)
    (j : Nat) (hj : j ≤ n) :
    let progress := wordProgress memory x t word carry0 j
    V progress.1 t (n + 2) + B ^ j * progress.2.toNat =
      V memory t (n + 2) + word.toNat * V memory x j + carry0.toNat := by
  have hprefix := wordProgress_correct memory x t n word carry0 hcarry0
    hxfit htfit hdisjoint j hj
  dsimp only at hprefix ⊢
  let progress := wordProgress memory x t word carry0 j
  have hsuffix := value_suffix_eq progress.1 memory t j n
    (fun i hji hi => hprefix.2.2.1 i hji hi)
  have hsplitProgress := value_split progress.1 t j (n + 2 - j)
  have hsplitProgress' :
      V progress.1 t (n + 2) =
        V progress.1 t j + B ^ j *
          V progress.1 (t + 32 * j) (n + 2 - j) := by
    have hjle : j ≤ n + 2 := by omega
    simpa [Nat.add_sub_of_le hjle] using hsplitProgress
  have hsplitMemory := value_split memory t j (n + 2 - j)
  have hsplitMemory' :
      V memory t (n + 2) =
        V memory t j + B ^ j *
          V memory (t + 32 * j) (n + 2 - j) := by
    have hjle : j ≤ n + 2 := by omega
    simpa [Nat.add_sub_of_le hjle] using hsplitMemory
  have hvalue := hprefix.2.2.2.2
  have hresult :
      V progress.1 t (n + 2) + B ^ j * progress.2.toNat =
        V memory t (n + 2) + word.toNat * V memory x j + carry0.toNat := by
    calc
      V progress.1 t (n + 2) + B ^ j * progress.2.toNat =
          (V progress.1 t j + B ^ j *
              V progress.1 (t + 32 * j) (n + 2 - j)) +
            B ^ j * progress.2.toNat := by rw [hsplitProgress']
      _ = (V progress.1 t j + B ^ j * progress.2.toNat) +
            B ^ j * V progress.1 (t + 32 * j) (n + 2 - j) := by ring
      _ = (V memory t j + word.toNat * V memory x j + carry0.toNat) +
            B ^ j * V memory (t + 32 * j) (n + 2 - j) := by
              rw [hvalue, hsuffix]
      _ = (V memory t j + B ^ j *
            V memory (t + 32 * j) (n + 2 - j)) +
            word.toNat * V memory x j + carry0.toNat := by ring
      _ = V memory t (n + 2) + word.toNat * V memory x j +
            carry0.toNat := by rw [hsplitMemory']
  simpa [progress] using hresult

theorem addMulMemory_noWrap (memory : ByteArray) (x t n : Nat)
    (word carry0 : UInt256)
    (hcarry0 : carry0.toNat ≤ word.toNat)
    (hxfit : x + 32 * n < B)
    (htfit : t + 32 * (n + 2) < B)
    (hdisjoint : x + 32 * n ≤ t ∨
      t + 32 * (n + 2) ≤ x)
    (hbound :
      V memory t (n + 2) + word.toNat * V memory x n + carry0.toNat <
        B ^ (n + 2)) :
    let progress := wordProgress memory x t word carry0 n
    (MachineState.readWord progress.1 (t + 32 * n + 32)).toNat +
        (UInt256.lt
          (MachineState.readWord progress.1 (t + 32 * n) + progress.2)
          (MachineState.readWord progress.1 (t + 32 * n))).toNat < B := by
  dsimp only
  let progress := wordProgress memory x t word carry0 n
  let h := MachineState.readWord progress.1 (t + 32 * n)
  let k := MachineState.readWord progress.1 (t + 32 * n + 32)
  let c := progress.2
  have hprefix := wordProgress_correct memory x t n word carry0 hcarry0
    hxfit htfit hdisjoint n (by omega)
  dsimp only at hprefix
  have hcLe : c.toNat ≤ word.toNat := by
    simpa [c, progress] using hprefix.1
  have hwordlt : word.toNat < B := by
    change word.val.val < 2 ^ 256
    exact word.val.isLt
  have hc : c.toNat < B := lt_of_le_of_lt hcLe hwordlt
  have hcomplete := wordProgress_complete memory x t n word carry0 hcarry0
    hxfit htfit hdisjoint n (by omega)
  dsimp only at hcomplete
  have htotal :
      V progress.1 t (n + 2) + B ^ n * c.toNat < B ^ (n + 2) := by
    calc
      V progress.1 t (n + 2) + B ^ n * c.toNat =
          V memory t (n + 2) + word.toNat * V memory x n +
            carry0.toNat := by simpa [progress] using hcomplete
      _ < B ^ (n + 2) := hbound
  have hsplit := value_two_succ progress.1 t n
  have hsplit' :
      V progress.1 t (n + 2) =
        V progress.1 t n + B ^ n * h.toNat +
          B ^ (n + 1) * k.toNat := by
    rw [show t + 32 * (n + 1) = t + 32 * n + 32 by omega] at hsplit
    simpa [h, k] using hsplit
  have hfull :
      V progress.1 t (n + 2) + B ^ n * c.toNat =
        V progress.1 t n + B ^ n *
          (h.toNat + c.toNat + B * k.toNat) := by
    rw [hsplit']
    rw [show B ^ (n + 1) = B ^ n * B by rw [pow_succ]]
    ring
  have hscaled :
      B ^ n * (h.toNat + c.toNat + B * k.toNat) < B ^ n * B ^ 2 := by
    calc
      B ^ n * (h.toNat + c.toNat + B * k.toNat) ≤
          V progress.1 t n + B ^ n *
            (h.toNat + c.toNat + B * k.toNat) := by omega
      _ = V progress.1 t (n + 2) + B ^ n * c.toNat := by
        rw [← hfull]
      _ < B ^ (n + 2) := htotal
      _ = B ^ n * B ^ 2 := Nat.pow_add B n 2
  have hscaled' : h.toNat + c.toNat + B * k.toNat < B ^ 2 :=
    Nat.lt_of_mul_lt_mul_left hscaled
  have hk : k.toNat < B := by
    change k.val.val < 2 ^ 256
    exact k.val.isLt
  have hz : (h + c).toNat = (h.toNat + c.toNat) % B := by
    simpa [B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using
      Challenge.EvmProof.Word.word_toNat_add h c
  have he : (UInt256.lt (h + c) h).toNat =
      if (h + c).toNat < h.toNat then 1 else 0 :=
    Challenge.EvmProof.Word.word_toNat_lt (h + c) h
  change k.toNat + (UInt256.lt (h + c) h).toNat < B
  by_cases hsumLt : h.toNat + c.toNat < B
  · have heZero : (UInt256.lt (h + c) h).toNat = 0 := by
      rw [he, hz, Nat.mod_eq_of_lt hsumLt]
      split <;> omega
    rw [heZero]
    exact hk
  · have hsumGe : B ≤ h.toNat + c.toNat := by omega
    have hmul : B * (k.toNat + 1) ≤
        h.toNat + c.toNat + B * k.toNat := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hmulLt : B * (k.toNat + 1) < B ^ 2 :=
      lt_of_le_of_lt hmul hscaled'
    have hk1lt : k.toNat + 1 < B := by
      apply Nat.lt_of_mul_lt_mul_left
      simpa [pow_two] using hmulLt
    have heLe : (UInt256.lt (h + c) h).toNat ≤ 1 := by
      rw [he]
      split <;> omega
    omega

theorem addMulMemory_correct (memory : ByteArray) (x t n : Nat)
    (word carry0 : UInt256)
    (hcarry0 : carry0.toNat ≤ word.toNat)
    (hxfit : x + 32 * n < B)
    (htfit : t + 32 * (n + 2) < B)
    (hdisjoint : x + 32 * n ≤ t ∨
      t + 32 * (n + 2) ≤ x)
    (hbound :
      V memory t (n + 2) + word.toNat * V memory x n + carry0.toNat <
        B ^ (n + 2)) :
    let result := addMulMemory memory x t n word carry0
    V result t (n + 2) =
        V memory t (n + 2) + word.toNat * V memory x n + carry0.toNat ∧
      (∀ i, i < n →
        MachineState.readWord result (x + 32 * i) =
          MachineState.readWord memory (x + 32 * i)) ∧
      (∀ a, a < t ∨ t + 32 * (n + 2) ≤ a →
        result[a]?.getD 0 = memory[a]?.getD 0) := by
  dsimp only
  let progress := wordProgress memory x t word carry0 n
  let result := Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop progress.1 t n progress.2
  change
    V result t (n + 2) =
        V memory t (n + 2) + word.toNat * V memory x n + carry0.toNat ∧
      (∀ i, i < n →
        MachineState.readWord result (x + 32 * i) =
          MachineState.readWord memory (x + 32 * i)) ∧
      (∀ a, a < t ∨ t + 32 * (n + 2) ≤ a →
        result[a]?.getD 0 = memory[a]?.getD 0)
  have hprogress := wordProgress_correct memory x t n word carry0 hcarry0
    hxfit htfit hdisjoint n (by omega)
  dsimp only at hprogress
  have hcarryLe : progress.2.toNat ≤ word.toNat := by
    simpa [progress] using hprogress.1
  have hwordlt : word.toNat < B := by
    change word.val.val < 2 ^ 256
    exact word.val.isLt
  have hcarry : progress.2.toNat < Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B := by
    have hc : progress.2.toNat < B := lt_of_le_of_lt hcarryLe hwordlt
    simpa [B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using hc
  have hno0 := addMulMemory_noWrap memory x t n word carry0 hcarry0
    hxfit htfit hdisjoint hbound
  dsimp only at hno0
  have hno :
      (MachineState.readWord progress.1 (t + 32 * n + 32)).toNat +
          (UInt256.lt
            (MachineState.readWord progress.1 (t + 32 * n) + progress.2)
            (MachineState.readWord progress.1 (t + 32 * n))).toNat < B := by
    simpa [progress] using hno0
  have hfold := Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop_correct progress.1 t n
    progress.2 hcarry hno
  dsimp only at hfold
  let h := MachineState.readWord progress.1 (t + 32 * n)
  let k := MachineState.readWord progress.1 (t + 32 * n + 32)
  let c := progress.2
  have htop :
      (MachineState.readWord result (t + 32 * n)).toNat =
        (h.toNat + c.toNat) % B := by
    have htop0 := hfold.1
    simpa [result, h, c, B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using htop0
  have hnext :
      (MachineState.readWord result (t + 32 * n + 32)).toNat =
        k.toNat + (h.toNat + c.toNat) / B := by
    have hnext0 := hfold.2.1
    simpa [result, h, k, c, B, Limbs.radix, Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.B] using hnext0
  have hlow : V result t n = V progress.1 t n := by
    apply value_eq_of_readWords_eq
    intro i hi
    have hread := foldTop_read_prefix progress.1 t n i progress.2 hi
    simpa [result] using hread
  have hresultValue :
      V result t (n + 2) =
        V progress.1 t n + B ^ n * ((h.toNat + c.toNat) % B) +
          B ^ (n + 1) * (k.toNat + (h.toNat + c.toNat) / B) := by
    have hvalue := value_two_succ result t n
    rw [show t + 32 * (n + 1) = t + 32 * n + 32 by omega] at hvalue
    rw [htop, hnext, hlow] at hvalue
    simpa [h, k] using hvalue
  have hprogressValue :
      V progress.1 t (n + 2) + B ^ n * c.toNat =
        V progress.1 t n + B ^ n * ((h.toNat + c.toNat) % B) +
          B ^ (n + 1) * (k.toNat + (h.toNat + c.toNat) / B) := by
    have hvalue := value_two_succ progress.1 t n
    rw [show t + 32 * (n + 1) = t + 32 * n + 32 by omega] at hvalue
    have hvalue' :
        V progress.1 t (n + 2) =
          V progress.1 t n + B ^ n * h.toNat +
            B ^ (n + 1) * k.toNat := by
      simpa [h, k] using hvalue
    have hmoddiv : h.toNat + c.toNat =
        (h.toNat + c.toNat) % B + B * ((h.toNat + c.toNat) / B) := by
      exact (Nat.mod_add_div (h.toNat + c.toNat) B).symm
    have hmoddivMul : B ^ n * (h.toNat + c.toNat) =
        B ^ n * ((h.toNat + c.toNat) % B +
          B * ((h.toNat + c.toNat) / B)) :=
      congrArg (fun q => B ^ n * q) hmoddiv
    calc
      V progress.1 t (n + 2) + B ^ n * c.toNat =
          (V progress.1 t n + B ^ n * h.toNat +
            B ^ (n + 1) * k.toNat) + B ^ n * c.toNat := by
              rw [hvalue']
      _ = V progress.1 t n + B ^ n * (h.toNat + c.toNat) +
            B ^ (n + 1) * k.toNat := by ring
      _ = V progress.1 t n + B ^ n *
            ((h.toNat + c.toNat) % B +
              B * ((h.toNat + c.toNat) / B)) +
            B ^ (n + 1) * k.toNat := by rw [hmoddivMul]
      _ = V progress.1 t n + B ^ n * ((h.toNat + c.toNat) % B) +
            B ^ (n + 1) * (k.toNat + (h.toNat + c.toNat) / B) := by
              rw [show B ^ (n + 1) = B ^ n * B by rw [pow_succ]]
              ring
  have hcomplete := wordProgress_complete memory x t n word carry0 hcarry0
    hxfit htfit hdisjoint n (by omega)
  dsimp only at hcomplete
  have hvalueFinal :
      V result t (n + 2) =
        V memory t (n + 2) + word.toNat * V memory x n + carry0.toNat := by
    calc
      V result t (n + 2) =
          V progress.1 t n + B ^ n * ((h.toNat + c.toNat) % B) +
            B ^ (n + 1) * (k.toNat + (h.toNat + c.toNat) / B) :=
        hresultValue
      _ = V progress.1 t (n + 2) + B ^ n * c.toNat :=
        hprogressValue.symm
      _ = V memory t (n + 2) + word.toNat * V memory x n +
            carry0.toNat := by
        simpa [progress, c] using hcomplete
  have hsourceFinal : ∀ i, i < n →
      MachineState.readWord result (x + 32 * i) =
        MachineState.readWord memory (x + 32 * i) := by
    intro i hi
    have hread := foldTop_read_disjoint progress.1 t n
      (x + 32 * i) progress.2 (by
        rcases hdisjoint with hbefore | hafter
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    calc
      MachineState.readWord result (x + 32 * i) =
          MachineState.readWord progress.1 (x + 32 * i) := by
            simpa [result] using hread
      _ = MachineState.readWord memory (x + 32 * i) := hprogress.2.1 i hi
  have houtsideFinal : ∀ a, a < t ∨ t + 32 * (n + 2) ≤ a →
      result[a]?.getD 0 = memory[a]?.getD 0 := by
    intro a ha
    have hfoldOutside := hfold.2.2.2.2 a (by
      rcases ha with hbefore | hafter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    calc
      result[a]?.getD 0 = progress.1[a]?.getD 0 := by
        simpa [result] using hfoldOutside
      _ = memory[a]?.getD 0 := hprogress.2.2.2.1 a (by
        rcases ha with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
  exact ⟨hvalueFinal, hsourceFinal, houtsideFinal⟩

end Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop
