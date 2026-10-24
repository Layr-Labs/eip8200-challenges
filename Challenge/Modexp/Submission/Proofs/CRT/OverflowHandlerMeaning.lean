import Challenge.Modexp.Submission.Proofs.CRT.OverflowHandlerExecution
import Challenge.Modexp.Submission.Proofs.CRT.OverflowHandlerArith
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-!
# Meaning of the overflow handler

`handlerMemory` is the handler's memory effect in cell form: the counter word is
decremented and the nine operand digits are the digit-wise difference of the
retained column value `Q` and the modulus digits, with the borrow taken from bit 255.
`handler_model` identifies the generated execution model with it, and
`handler_represents` proves that the new digits represent `Q - N` whenever
`R ≤ Q < R + N`, which is exactly the overflow case of the squaring footer.
-/

namespace HistoricalSearch.OverflowHandlerMeaning
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Word Challenge.EvmProof.Memory
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.CRTMemoryCells
open HistoricalSearch.CRTWordPacking HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.MixedMontgomery HistoricalSearch.OverflowHandler HistoricalSearch.OverflowHandlerArith
open HistoricalSearch.ColumnMemory

/-- Digit `i < 8` of the retained value, masked exactly as the handler computes it. -/
def hdig (mem : ByteArray) (mask : UInt256) (i : Nat) : UInt256 :=
  UInt256.land mask (UInt256.lor (UInt256.shiftRight (rawDigits mem i) (UInt256.ofNat 96))
    (UInt256.shiftLeft (rawDigits mem (i+1)) (UInt256.ofNat 148)))

/-- The borrow out of a difference word: its sign bit. -/
def bout (t : UInt256) : UInt256 := UInt256.shiftRight t (UInt256.ofNat 255)

def ht0 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 0 - n 0
def ht1 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 1 - (n 1 + bout (ht0 mem mask n))
def ht2 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 2 - (n 2 + bout (ht1 mem mask n))
def ht3 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 3 - (n 3 + bout (ht2 mem mask n))
def ht4 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 4 - (n 4 + bout (ht3 mem mask n))
def ht5 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 5 - (n 5 + bout (ht4 mem mask n))
def ht6 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 6 - (n 6 + bout (ht5 mem mask n))
def ht7 (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  hdig mem mask 7 - (n 7 + bout (ht6 mem mask n))
def htop (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : UInt256 :=
  UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 96) - (n 8 + bout (ht7 mem mask n))

def handlerInput (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : Nat → UInt256
  | 0 => UInt256.land mask (ht0 mem mask n)
  | 1 => UInt256.land mask (ht1 mem mask n)
  | 2 => UInt256.land mask (ht2 mem mask n)
  | 3 => UInt256.land mask (ht3 mem mask n)
  | 4 => UInt256.land mask (ht4 mem mask n)
  | 5 => UInt256.land mask (ht5 mem mask n)
  | 6 => UInt256.land mask (ht6 mem mask n)
  | 7 => UInt256.land mask (ht7 mem mask n)
  | _ => htop mem mask n

def handlerMemory (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : ByteArray :=
  storeCells mem ((1728, MachineState.readWord mem 1728 - UInt256.ofNat 1) ::
    operandCells (handlerInput mem mask n))

theorem handler_model (s : State) (n : Nat → UInt256)
    (P minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256)
    (rest : List UInt256) :
    handlerBodyModel s P (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8)
      (UInt256.ofNat (2^244-1)) minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn
      aprev counter ret rest =
      {s with
        pc := UInt256.ofNat 8609
        memory := handlerMemory s.memory (UInt256.ofNat (2^244-1)) n
        stack := [UInt256.ofNat 5858, P, n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7, n 8,
          UInt256.ofNat (2^244-1), minv, pbi, hd, w3, ent, m32, allones, m128, m64,
          m0, tl, m96, inv, tn, aprev, counter, ret] ++ rest} := by
  simp (disch := omega) only [handlerBodyModel, handlerMemory, operandCells, handlerInput,
    ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, htop, hdig, bout, rawDigits, storeCells, writeCell,
    read_store_disjoint, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]

theorem handler_operand (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) (i : Nat) (hi : i < 9) :
    MachineState.readWord (handlerMemory mem mask n) (768+32*i) = handlerInput mem mask n i := by
  unfold handlerMemory
  rw [storeCells]
  exact operandCells_read _ _ i hi

theorem handler_keep (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) (addr width : Nat)
    (h : addr+width ≤ 768 ∨ 1792 ≤ addr) :
    MachineState.readPadded (handlerMemory mem mask n) addr width =
      MachineState.readPadded mem addr width := by
  apply scratch_preserves_live _ _ _ addr width h
  intro c hc
  rcases List.mem_cons.mp hc with he | ht
  · subst c
    norm_num
  · have hb := operandCells_bounds _ _ ht
    constructor <;> omega

theorem handler_counter (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) :
    MachineState.readWord (handlerMemory mem mask n) 1728 =
      MachineState.readWord mem 1728 - UInt256.ofNat 1 := by
  unfold handlerMemory
  rw [storeCells, readWord_storeCells]
  · exact readWord_writeWord mem 1728 _
  · intro c hc
    have hb := operandCells_bounds _ _ hc
    right
    omega

theorem handler_counter_toNat (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256)
    (h : 0 < (MachineState.readWord mem 1728).toNat) :
    (MachineState.readWord (handlerMemory mem mask n) 1728).toNat =
      (MachineState.readWord mem 1728).toNat - 1 := by
  rw [handler_counter, word_toNat_sub_cond]
  change (if (MachineState.readWord mem 1728).toNat < 1 then _ else _) = _
  rw [if_neg (by omega)]
  rfl

/-! ## The handler digits represent `Q - N` -/

/-- Borrow into digit `j`. -/
def cin (mem : ByteArray) (mask : UInt256) (n : Nat → UInt256) : Nat → Nat
  | 1 => (bout (ht0 mem mask n)).toNat
  | 2 => (bout (ht1 mem mask n)).toNat
  | 3 => (bout (ht2 mem mask n)).toNat
  | 4 => (bout (ht3 mem mask n)).toNat
  | 5 => (bout (ht4 mem mask n)).toNat
  | 6 => (bout (ht5 mem mask n)).toNat
  | 7 => (bout (ht6 mem mask n)).toNat
  | 8 => (bout (ht7 mem mask n)).toNat
  | _ => 0

theorem chain_first (d n : UInt256) (hd : d.toNat < B) (hn : n.toNat < B) :
    (bout (d - n)).toNat ≤ 1 ∧
      d.toNat + B * (bout (d - n)).toNat =
        (UInt256.land (UInt256.ofNat (2^244-1)) (d - n)).toNat + n.toNat + 0 := by
  have h := sub_step d n hd (le_of_lt hn)
  unfold bout
  rw [h.1]
  split_ifs at h ⊢ <;> constructor <;> omega

theorem chain_next (d n c : UInt256) (hd : d.toNat < B) (hn : n.toNat < B) (hc : c.toNat ≤ 1) :
    (bout (d - (n + c))).toNat ≤ 1 ∧
      d.toNat + B * (bout (d - (n + c))).toNat =
        (UInt256.land (UInt256.ofNat (2^244-1)) (d - (n + c))).toNat + n.toNat + c.toNat := by
  have hs := add_small n c hn hc
  have h := sub_step d (n + c) hd (by rw [hs]; omega)
  unfold bout
  rw [h.1]
  rw [hs] at h ⊢
  split_ifs at h ⊢ <;> constructor <;> omega

theorem hdig_toNat (mem : ByteArray) (i : Nat) (hi : i < 8)
    (hd : ∀ j < 9, (rawDigits mem j).toNat < 2^244) :
    (hdig mem (UInt256.ofNat (2^244-1)) i).toNat = value (rawDigits mem) / B^i % B := by
  have hw := retainedWord_toNat (rawDigits mem) i hi hd
  unfold retainedWord at hw
  rw [hdig, land_comm, hw, ← Nat.pow_mul]

theorem handler_represents (mem : ByteArray) (n : Nat → UInt256) (N : Nat)
    (hd : ∀ i < 9, (rawDigits mem i).toNat < 2^244)
    (hnlow : ∀ i < 8, (n i).toNat = N / 2^(244*i) % 2^244)
    (hnhigh : (n 8).toNat = N / 2^1952)
    (hN : N < 2^2048)
    (hR : 2^2048 ≤ value (rawDigits mem)) (hQ : value (rawDigits mem) < 2^2048 + N) :
    Represents (handlerMemory mem (UInt256.ofNat (2^244-1)) n) (value (rawDigits mem) - N) := by
  set mask := UInt256.ofNat (2^244-1) with hmask
  set Q := value (rawDigits mem) with hQdef
  have hq : ∀ i < 8, (hdig mem mask i).toNat = Q / B^i % B := fun i hi => hdig_toNat mem i hi hd
  have hqB : ∀ i < 8, (hdig mem mask i).toNat < B := by
    intro i hi; rw [hq i hi]; exact Nat.mod_lt _ (by positivity)
  have hn' : ∀ i < 8, (n i).toNat = N / B^i % B := by
    intro i hi; rw [hnlow i hi, ← Nat.pow_mul]
  have hnB : ∀ i < 8, (n i).toNat < B := by
    intro i hi; rw [hn' i hi]; exact Nat.mod_lt _ (by positivity)
  have h0 := chain_first (hdig mem mask 0) (n 0) (hqB 0 (by decide)) (hnB 0 (by decide))
  have h1 := chain_next (hdig mem mask 1) (n 1) (bout (ht0 mem mask n)) (hqB 1 (by decide)) (hnB 1 (by decide)) h0.1
  have h2 := chain_next (hdig mem mask 2) (n 2) (bout (ht1 mem mask n)) (hqB 2 (by decide)) (hnB 2 (by decide)) h1.1
  have h3 := chain_next (hdig mem mask 3) (n 3) (bout (ht2 mem mask n)) (hqB 3 (by decide)) (hnB 3 (by decide)) h2.1
  have h4 := chain_next (hdig mem mask 4) (n 4) (bout (ht3 mem mask n)) (hqB 4 (by decide)) (hnB 4 (by decide)) h3.1
  have h5 := chain_next (hdig mem mask 5) (n 5) (bout (ht4 mem mask n)) (hqB 5 (by decide)) (hnB 5 (by decide)) h4.1
  have h6 := chain_next (hdig mem mask 6) (n 6) (bout (ht5 mem mask n)) (hqB 6 (by decide)) (hnB 6 (by decide)) h5.1
  have h7 := chain_next (hdig mem mask 7) (n 7) (bout (ht6 mem mask n)) (hqB 7 (by decide)) (hnB 7 (by decide)) h6.1
  let r : Nat → Nat := fun i => (handlerInput mem mask n i).toNat
  have hstep : ∀ i < 8, (fun i => (hdig mem mask i).toNat) i + B * cin mem mask n (i+1) =
      r i + (fun i => (n i).toNat) i + cin mem mask n i := by
    intro i hi
    interval_cases i
    · exact h0.2
    · exact h1.2
    · exact h2.2
    · exact h3.2
    · exact h4.2
    · exact h5.2
    · exact h6.2
    · exact h7.2
  have hr : ∀ i < 8, r i < B := by
    intro i hi
    interval_cases i <;> simp only [r, handlerInput, hmask, land_mask_toNat] <;>
      exact Nat.mod_lt _ (Nat.two_pow_pos 244)
  have hT := retainedTop_toNat (rawDigits mem) hd
  have hB8 : (B:Nat)^8 = 2^1952 := by norm_num [B]
  have hn8 : (n 8).toNat = N / B^8 := by rw [hnhigh, hB8]
  have hNQ : N ≤ Q := by omega
  have hX : Q - N < 2^2048 := by omega
  have hsub := sub_digits Q N (UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 96)).toNat
    (fun i => (hdig mem mask i).toNat) (fun i => (n i).toNat) r (cin mem mask n)
    hq (by rw [hT, hB8]) hn' hn8 rfl hstep hr hNQ hX
  have hc8 : (bout (ht7 mem mask n)).toNat ≤ 1 := h7.1
  have hn8B : (n 8).toNat < B := by rw [hn8]; norm_num [B] at hN ⊢; omega
  have htop : (htop mem mask n).toNat =
      (UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 96)).toNat - (n 8).toNat - cin mem mask n 8 := by
    rw [htop, top_step _ _ (by rw [add_small _ _ hn8B hc8]; exact hsub.1), add_small _ _ hn8B hc8]
    show _ = _ - _ - (bout (ht7 mem mask n)).toNat
    omega
  refine ⟨hX, ?_, ?_⟩
  · intro i hi
    rw [aRead, handler_operand mem mask n i (by omega), Nat.pow_mul]
    exact (hsub.2.1 i hi).symm
  · rw [aRead, handler_operand mem mask n 8 (by decide)]
    simp only [handlerInput]
    rw [htop, ← hB8, hsub.2.2]

#print axioms handler_model
#print axioms handler_represents
end HistoricalSearch.OverflowHandlerMeaning
