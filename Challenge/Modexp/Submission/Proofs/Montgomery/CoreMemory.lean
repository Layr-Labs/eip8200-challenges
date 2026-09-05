import Challenge.Modexp.Submission.Proofs.Montgomery.CIOS
import Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop
import Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory

open EvmSemantics
open Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Limbs

abbrev B : Nat := radix

/-- Decode every word in the specified little-endian window. -/
def V (memory : ByteArray) (ptr count : Nat) : Nat :=
  Nat.ofDigits B (memoryLimbs memory ptr count)

/-- Equality of padded bytes, including addresses beyond either array size. -/
def Outside (after before : ByteArray) (t n : Nat) : Prop :=
  ∀ addr, addr < t ∨ t + 32 * (n + 2) ≤ addr →
    after[addr]?.getD 0 = before[addr]?.getD 0

/-- Only source-to-scratch disjointness; sources may alias each other. -/
def Disjoint (x t n : Nat) : Prop :=
  x + 32 * n ≤ t ∨ t + 32 * (n + 2) ≤ x

def clearProgress (memory : ByteArray) (t : Nat) : Nat → ByteArray
  | 0 => memory
  | j + 1 => MachineState.writeBytes (clearProgress memory t j)
      (Data.Bytes.natToBytesPadded 0 32) (t + 32 * j)

def clearScratch (memory : ByteArray) (t n : Nat) : ByteArray :=
  clearProgress memory t (n + 2)

/-- Both products and the quotient word read the actual current memory. -/
def coreStep (memory : ByteArray) (a b modulus t n i : Nat) (np : UInt256) :
    ByteArray :=
  let digit := MachineState.readWord memory (a + 32 * i)
  let first := Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory memory b t n digit 0
  let q := MachineState.readWord first t * np
  let second := Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory first modulus t n q 0
  Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown second t n

def coreProgress (memory : ByteArray) (a b modulus t n : Nat) (np : UInt256) :
    Nat → ByteArray
  | 0 => clearScratch memory t n
  | i + 1 => coreStep (coreProgress memory a b modulus t n np i)
      a b modulus t n i np

theorem value_lt (memory : ByteArray) (ptr count : Nat) :
    V memory ptr count < B ^ count := by
  simpa [V] using Nat.ofDigits_lt_base_pow_length radix_gt_one
    (fun _ hd => memoryLimb_lt memory ptr count hd)

/-- The digit bridge uses the full decoded value, not a scalar input oracle. -/
theorem read_digit (memory : ByteArray) (ptr count i : Nat) (hi : i < count) :
    (MachineState.readWord memory (ptr + 32 * i)).toNat =
      (V memory ptr count / B ^ i) % B := by
  rw [V, Nat.ofDigits_div_pow_eq_ofDigits_drop i radix_pos _
    (fun _ hd => memoryLimb_lt memory ptr count hd), Nat.ofDigits_mod_eq_head!]
  rw [List.head!_eq_head?_getD, List.head?_drop]
  simp [memoryLimbs, hi, Nat.mod_eq_of_lt
    (show (MachineState.readWord memory (ptr + 32 * i)).toNat < B from
      (MachineState.readWord memory (ptr + 32 * i)).val.isLt)]

theorem represented_digit {memory : ByteArray} {ptr count value i : Nat}
    (hrep : Represents memory ptr count value) (hi : i < count) :
    (MachineState.readWord memory (ptr + 32 * i)).toNat =
      (value / B ^ i) % B := by
  rw [read_digit memory ptr count i hi]
  exact congrArg (fun v => (v / B ^ i) % B) (value_of_represents hrep)

theorem source_value_eq {after before : ByteArray} {x t n : Nat}
    (hout : Outside after before t n) (hd : Disjoint x t n) :
    V after x n = V before x n := by
  unfold V memoryLimbs
  congr 1
  apply List.map_congr_left
  intro i hi
  apply congrArg UInt256.toNat
  unfold MachineState.readWord
  rw [readPadded_congr after before (x + 32 * i) 32 (by
    intro j hj
    apply hout
    have hi' := List.mem_range.mp hi
    rcases hd with h | h <;> omega)]

theorem source_represents {after before : ByteArray} {x t n value : Nat}
    (hout : Outside after before t n) (hd : Disjoint x t n)
    (hrep : Represents before x n value) : Represents after x n value := by
  apply (represents_iff_value hrep.1).2
  exact (source_value_eq hout hd).trans (value_of_represents hrep)

private theorem padded_zero_size :
    (Data.Bytes.natToBytesPadded 0 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

theorem clearProgress_readWord (memory : ByteArray) (t j k : Nat) :
    MachineState.readWord (clearProgress memory t j) (t + 32 * k) =
      if k < j then 0 else MachineState.readWord memory (t + 32 * k) := by
  induction j with
  | zero => simp [clearProgress]
  | succ j ih =>
      rw [clearProgress]
      by_cases hkj : k = j
      · subst k
        rw [readWord_writeBytes_of_lt _ _ _ (by norm_num)]
        simp
        rfl
      · rw [readWord_writeBytes_disjoint]
        · rw [ih]
          have hlt : (k < j + 1) ↔ k < j := by omega
          simp only [hlt]
        · rw [padded_zero_size]
          omega

theorem clearProgress_outside (memory : ByteArray) (t j addr : Nat)
    (hout : addr < t ∨ t + 32 * j ≤ addr) :
    (clearProgress memory t j)[addr]?.getD 0 = memory[addr]?.getD 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [clearProgress, MachineState.writeBytes_getElem?_getD, padded_zero_size,
        if_neg (by omega)]
      exact ih (by omega)

theorem clearScratch_correct (memory : ByteArray) (t n : Nat) :
    Represents (clearScratch memory t n) t (n + 2) 0 ∧
      Outside (clearScratch memory t n) memory t n := by
  constructor
  · apply (represents_iff_value (pow_pos radix_pos (n + 2))).2
    have hz : memoryLimbs (clearScratch memory t n) t (n + 2) =
        List.replicate (n + 2) 0 := by
      apply List.ext_getElem
      · simp
      · intro i hi _
        have hi' : i < n + 2 := by simpa using hi
        simp [memoryLimbs, clearScratch, clearProgress_readWord, hi']
        rfl
    rw [hz]
    simp
  · exact clearProgress_outside memory t (n + 2)

/-- Global bounds for both Task 10 calls. Neither top carry is assumed safe. -/
theorem step_bounds {acc digit b m q n : Nat}
    (hmR : m < B ^ n) (hacc : acc < 2 * m)
    (hd : digit < B) (hb : b ≤ m) (hq : q < B) :
    acc + digit * b < (B + 1) * m ∧
      (B + 1) * m < B ^ (n + 2) ∧
      acc + digit * b + q * m < 2 * B * m ∧
      2 * B * m < B ^ (n + 2) := by
  have hB : 2 ≤ B := by norm_num [B, radix]
  have hdle := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hd)
  have hdb := Nat.mul_le_mul_left digit hb
  have hqle := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hq)
  have hU : acc + digit * b < (B + 1) * m := by nlinarith
  have hN : acc + digit * b + q * m < 2 * B * m := by nlinarith
  have hB1 : B + 1 ≤ B ^ 2 := by nlinarith
  have hB2 : 2 * B ≤ B ^ 2 := by nlinarith
  have hfirst : (B + 1) * m < B ^ (n + 2) := by
    calc
      (B + 1) * m ≤ B ^ 2 * m := Nat.mul_le_mul_right m hB1
      _ < B ^ 2 * B ^ n := Nat.mul_lt_mul_of_pos_left hmR (pow_pos radix_pos 2)
      _ = B ^ (n + 2) := by rw [← pow_add]; congr 1; omega
  have hsecond : 2 * B * m < B ^ (n + 2) := by
    calc
      2 * B * m ≤ B ^ 2 * m := Nat.mul_le_mul_right m hB2
      _ < B ^ 2 * B ^ n := Nat.mul_lt_mul_of_pos_left hmR (pow_pos radix_pos 2)
      _ = B ^ (n + 2) := by rw [← pow_add]; congr 1; omega
  exact ⟨hU, hfirst, hN, hsecond⟩

/-- One complete memory step; the last equality records an exact shift. -/
theorem coreStep_correct (memory : ByteArray) (a b modulus t n i : Nat)
    (np : UInt256) (aValue bValue m acc : Nat)
    (ha : Represents memory a n aValue) (hb : Represents memory b n bValue)
    (hmemory : Represents memory modulus n m)
    (ht : Represents memory t (n + 2) acc)
    (hi : i < n) (hm : 0 < m) (hb_le : bValue ≤ m) (hacc : acc < 2 * m)
    (hinv : (m * np.toNat + 1) % B = 0)
    (hbfit : b + 32 * n < B) (hmfit : modulus + 32 * n < B)
    (htfit : t + 32 * (n + 2) < B)
    (hbdis : Disjoint b t n) (hmdis : Disjoint modulus t n) :
    let digit := (aValue / B ^ i) % B
    let value := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.step acc digit bValue m np.toNat
    let result := coreStep memory a b modulus t n i np
    Represents result t (n + 2) value ∧ value < 2 * m ∧
      Outside result memory t n ∧
      B * V result t (n + 2) = acc + digit * bValue +
        Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.quotient (acc + digit * bValue) np.toNat * m := by
  dsimp only
  let digit := MachineState.readWord memory (a + 32 * i)
  let U := acc + digit.toNat * bValue
  let first := Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory memory b t n digit 0
  let q := MachineState.readWord first t * np
  let second := Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory first modulus t n q 0
  let result := Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown second t n
  have hd : digit.toNat = (aValue / B ^ i) % B := represented_digit ha hi
  have hdlt : digit.toNat < B := digit.val.isLt
  have hqlt : q.toNat < B := q.val.isLt
  have bounds := step_bounds hmemory.1 hacc hdlt hb_le hqlt
  have hvT : V memory t (n + 2) = acc := value_of_represents ht
  have hvB : V memory b n = bValue := value_of_represents hb
  have hvM : V memory modulus n = m := value_of_represents hmemory
  have hfirstBound : Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.V memory t (n + 2) +
      digit.toNat * Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.V memory b n + (0 : UInt256).toNat <
        Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.B ^ (n + 2) := by
    change V memory t (n + 2) + digit.toNat * V memory b n + 0 < B ^ (n + 2)
    rw [hvT, hvB, Nat.add_zero]
    exact bounds.1.trans bounds.2.1
  have firstOK := Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory_correct memory b t n digit 0
    (Nat.zero_le _) hbfit htfit hbdis hfirstBound
  have hfirst : V first t (n + 2) = U := by
    have h := firstOK.1
    change V first t (n + 2) = V memory t (n + 2) + digit.toNat * V memory b n + 0 at h
    simpa only [hvT, hvB, Nat.add_zero] using h
  have houtFirst : Outside first memory t n := firstOK.2.2
  have hmFirst : V first modulus n = m := (source_value_eq houtFirst hmdis).trans hvM
  have hlow : (MachineState.readWord first t).toNat = U % B := by
    simpa only [Nat.mul_zero, Nat.add_zero, pow_zero, Nat.div_one, hfirst]
      using read_digit first t (n + 2) 0 (by omega)
  have hq : q.toNat = Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.quotient U np.toNat := by
    change ((MachineState.readWord first t).val * np.val).val = _
    rw [Fin.val_mul]
    change ((MachineState.readWord first t).toNat * np.toNat) % B = _
    rw [hlow]
    rfl
  have hsecondBound : Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.V first t (n + 2) +
      q.toNat * Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.V first modulus n + (0 : UInt256).toNat <
        Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.B ^ (n + 2) := by
    change V first t (n + 2) + q.toNat * V first modulus n + 0 < B ^ (n + 2)
    rw [hfirst, hmFirst, Nat.add_zero]
    exact bounds.2.2.1.trans bounds.2.2.2
  have secondOK := Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory_correct first modulus t n q 0
    (Nat.zero_le _) hmfit htfit hmdis hsecondBound
  have hsecond : V second t (n + 2) = U + q.toNat * m := by
    have h := secondOK.1
    change V second t (n + 2) = V first t (n + 2) + q.toNat * V first modulus n + 0 at h
    simpa only [hfirst, hmFirst, Nat.add_zero] using h
  have hcancel : V second t (n + 2) % B = 0 := by
    rw [hsecond, hq]
    exact Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.add_quotient_mod_eq_zero U m np.toNat hinv
  have hshift : V result t (n + 2) = V second t (n + 2) / B :=
    Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown_value second t n
  have hvalue : V result t (n + 2) =
      Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.step acc ((aValue / B ^ i) % B) bValue m np.toNat := by
    rw [hshift, hsecond, hq]
    change (acc + digit.toNat * bValue +
      Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.quotient (acc + digit.toNat * bValue) np.toNat * m) / B = _
    rw [hd]
    rfl
  have hlt : Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.step acc ((aValue / B ^ i) % B) bValue m np.toNat <
      2 * m := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.step_lt_two_modulus_of_le hm hacc
        (Nat.mod_lt _ radix_pos) hb_le
  refine ⟨?_, hlt, ?_, ?_⟩
  · exact (represents_iff_value (hvalue ▸ value_lt result t (n + 2))).2 hvalue
  · intro addr haddr
    exact (Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown_byte_outside second t n addr haddr).trans
      ((secondOK.2.2 addr haddr).trans (houtFirst addr haddr))
  · change B * V result t (n + 2) = _
    rw [hshift, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hcancel), hsecond, hq]
    dsimp only [U]
    rw [hd]

/-- Every prefix implements the accepted Nat CIOS run and retains all sources. -/
theorem coreProgress_correct (memory : ByteArray) (a b modulus t n : Nat)
    (np : UInt256) (aValue bValue m : Nat)
    (ha : Represents memory a n aValue) (hb : Represents memory b n bValue)
    (hmemory : Represents memory modulus n m)
    (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % B = 0)
    (_hafit : a + 32 * n < B) (hbfit : b + 32 * n < B)
    (hmfit : modulus + 32 * n < B) (htfit : t + 32 * (n + 2) < B)
    (hadis : Disjoint a t n) (hbdis : Disjoint b t n) (hmdis : Disjoint modulus t n)
    (i : Nat) (hi : i ≤ n) :
    let result := coreProgress memory a b modulus t n np i
    Represents result t (n + 2) (Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat i) ∧
      Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat i < 2 * m ∧
      Outside result memory t n ∧
      Represents result a n aValue ∧ Represents result b n bValue ∧
      Represents result modulus n m := by
  induction i with
  | zero =>
      have hc := clearScratch_correct memory t n
      exact ⟨hc.1, by change 0 < 2 * m; omega, hc.2,
        source_represents hc.2 hadis ha, source_represents hc.2 hbdis hb,
        source_represents hc.2 hmdis hmemory⟩
  | succ i ih =>
      have hp := ih (by omega)
      have hs := coreStep_correct (coreProgress memory a b modulus t n np i)
        a b modulus t n i np aValue bValue m (Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat i)
        hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hp.1 (by omega) hm hb_le hp.2.1
        hinv hbfit hmfit htfit hbdis hmdis
      have hout : Outside (coreProgress memory a b modulus t n np (i + 1)) memory t n := by
        intro addr haddr
        exact (hs.2.2.1 addr haddr).trans (hp.2.2.1 addr haddr)
      exact ⟨hs.1, hs.2.1, hout, source_represents hout hadis ha,
        source_represents hout hbdis hb, source_represents hout hmdis hmemory⟩

/-- The full raw scratch result, before Task 11 normalization. -/
theorem coreProgress_contract (memory : ByteArray) (a b modulus t n : Nat)
    (np : UInt256) (aValue bValue m : Nat)
    (ha : Represents memory a n aValue) (hb : Represents memory b n bValue)
    (hmemory : Represents memory modulus n m)
    (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % B = 0)
    (hafit : a + 32 * n < B) (hbfit : b + 32 * n < B)
    (hmfit : modulus + 32 * n < B) (htfit : t + 32 * (n + 2) < B)
    (hadis : Disjoint a t n) (hbdis : Disjoint b t n) (hmdis : Disjoint modulus t n) :
    let result := coreProgress memory a b modulus t n np n
    V result t (n + 2) = Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat n ∧
      V result t (n + 2) < 2 * m ∧
      (V result t (n + 2) * B ^ n) % m = (aValue * bValue) % m ∧
      Outside result memory t n ∧
      Represents result a n aValue ∧ Represents result b n bValue ∧
      Represents result modulus n m := by
  have hp := coreProgress_correct memory a b modulus t n np aValue bValue m ha hb hmemory
    hm hb_le hinv hafit hbfit hmfit htfit hadis hbdis hmdis n (Nat.le_refl n)
  have hn := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run_contract_of_le aValue bValue m np.toNat n
    hm hb_le ha.1 hinv
  have hv : V (coreProgress memory a b modulus t n np n) t (n + 2) =
      Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat n := value_of_represents hp.1
  exact ⟨hv, by rw [hv]; exact hn.1, by rw [hv]; exact hn.2, hp.2.2⟩

end Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory
