import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopArithmetic
import Challenge.Modexp.Submission.Proofs.CRT.LegacyNormalize
import Challenge.Modexp.Submission.Proofs.CRT.StateIndependence
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 6000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.PureLoop
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.ColumnSequence HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.MixedMontgomery

abbrev R : Nat := 2^2048

def Live (after before : ByteArray) : Prop := ∀ addr, addr+32 ≤ 512 ∨ 2624 ≤ addr →
  MachineState.readWord after addr = MachineState.readWord before addr

theorem Live.refl (m : ByteArray) : Live m m := fun _ _ => rfl

theorem Live.trans {a b c : ByteArray} (hab : Live a b) (hbc : Live b c) : Live a c :=
  fun p hp => (hab p hp).trans (hbc p hp)

theorem Live.modulus {a b : ByteArray} (h : Live a b) (N : Nat)
    (hb : Model.FastRepresents b 0 8 N) : Model.FastRepresents a 0 8 N := by
  apply (Model.fastRepresents_congr (fun j hj => h (0+32*j) (Or.inl (by omega))) N).2 hb

def tailMemory (mem : ByteArray) (Q : Nat) : ByteArray :=
  if UInt256.ofNat (Q/R) = UInt256.ofNat 0 then SquareRoundC.copy8 mem
  else SquareRoundC.sub8 (TnCacheMemory.lift mem (UInt256.ofNat 5297))

theorem tail_live (mem : ByteArray) (Q : Nat) : Live (tailMemory mem Q) mem := by
  intro addr hd
  unfold tailMemory
  split
  · exact SquareRoundC.copy8_readWord mem addr (by omega)
  · rw [SquareRoundC.sub8_readWord _ addr (by omega)]
    exact TnCacheMemory.read_lift_outside mem _ addr (by omega)

theorem tail_represents (mem : ByteArray) (Q N : Nat)
    (ht : Model.FastRepresents mem 2112 8 (Q%R))
    (hm : Model.FastRepresents mem 0 8 N) (hQ : Q < R+N) :
    Model.FastRepresents (tailMemory mem Q) 2368 8 (MixedMontgomery.normalize R N Q) := by
  have hNR : N < R := by simpa only [LegacyNormalize.old_radix] using hm.1
  by_cases hlt : Q < R
  · have hz : Q/R = 0 := Nat.div_eq_of_lt hlt
    simp only [tailMemory, hz, ↓reduceIte, MixedMontgomery.normalize, if_neg (by omega : ¬R ≤ Q)]
    rw [Nat.mod_eq_of_lt hlt] at ht
    exact Csub.fastRepresents_mcopy mem 2112 2368 8 Q (by decide) ht
  · have hp : 0 < R := Nat.two_pow_pos 2048
    have hdlt : Q/R < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
    have hdpos : 0 < Q/R := Nat.div_pos (by omega) hp
    have h1 : Q/R = 1 := by omega
    simp only [tailMemory, h1, show UInt256.ofNat 1 ≠ UInt256.ofNat 0 from by decide,
      ↓reduceIte, MixedMontgomery.normalize, if_pos (by omega : R ≤ Q)]
    exact LegacyNormalize.sub8_lift_represents mem Q N _ ht hm (by change R ≤ Q; omega) hQ

variable (s : State) (minv : UInt256) (n : Nat → UInt256)

def raw (mem : ByteArray) : ByteArray := (result {s with memory := mem} minv n []).memory
def Q (mem : ByteArray) : Nat := CRTWordPacking.value (rawDigits (raw s minv n mem))
def checked (mem : ByteArray) : ByteArray := checkedMemory (raw s minv n mem)
def finish (mem : ByteArray) : ByteArray := tailMemory (exitMemory (checked s minv n mem)) (Q s minv n mem)
def next (remaining : Nat) (mem : ByteArray) : ByteArray :=
  if Q s minv n mem < R then retainedMemory (checked s minv n mem)
  else entryMemory (finish s minv n mem) (UInt256.ofNat (remaining-1))

def memory : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k+1, mem => if k=0 then finish s minv n mem
    else memory k (next s minv n k mem)

theorem raw_live (mem : ByteArray) : Live (raw s minv n mem) mem := by
  intro addr hd
  exact SequencePreservation.word_live {s with memory := mem} minv n [] 17 (by decide) addr (by omega)

theorem checked_live (mem : ByteArray) : Live (checked s minv n mem) mem := by
  intro addr hd
  exact (checked_word (raw s minv n mem) addr (by omega)).trans (raw_live s minv n mem addr hd)

theorem exit_live (mem : ByteArray) : Live (exitMemory (checked s minv n mem)) mem := by
  intro addr hd
  unfold MachineState.readWord
  rw [exit_keep _ addr 32 (by omega)]
  exact checked_live s minv n mem addr hd

theorem finish_live (mem : ByteArray) : Live (finish s minv n mem) mem :=
  (tail_live _ _).trans (exit_live s minv n mem)

theorem next_live (remaining : Nat) (mem : ByteArray) : Live (next s minv n remaining mem) mem := by
  intro addr hd
  unfold next
  split
  · unfold MachineState.readWord
    rw [retained_keep _ addr 32 (by omega)]
    exact checked_live s minv n mem addr hd
  · unfold MachineState.readWord
    rw [entry_keep _ _ addr 32 (by omega)]
    exact finish_live s minv n mem addr hd

theorem memory_live (k : Nat) (mem : ByteArray) : Live (memory s minv n k mem) mem := by
  induction k generalizing mem with
  | zero => exact Live.refl mem
  | succ k ih =>
    simp only [memory]
    split
    · exact finish_live s minv n mem
    · exact (ih (next s minv n k mem)).trans (next_live s minv n k mem)

theorem one_round (mem : ByteArray) (A N : Nat) (ha : Represents mem A)
    (hm : Model.FastRepresents mem 0 8 N) (hpos : 0 < N) (hodd : Odd N)
    (hnlow : ∀ i < 8, (n i).toNat = N / 2^(244*i) % 2^244)
    (hnhigh : (n 8).toNat = N / 2^1952) (hinv : (N*minv.toNat+1)%2^256=0) :
    let v := MixedMontgomery.normalize R N (Q s minv n mem)
    Model.FastRepresents (finish s minv n mem) 2368 8 v ∧
    (∀ remaining, Represents (next s minv n remaining mem) v) ∧
    v%N = Model.montMul N R A A := by
  have hN : N < R := by simpa only [LegacyNormalize.old_radix] using hm.1
  have hc := result_contract {s with memory := mem} minv n [] A N ha hN hpos hodd hnlow hnhigh hinv
  have ht := exit_representation (raw s minv n mem) hc.1
  have hm' := (exit_live s minv n mem).modulus N hm
  have hf := tail_represents (exitMemory (checked s minv n mem)) (Q s minv n mem) N ht hm' hc.2.1
  refine ⟨hf, ?_, hc.2.2.2⟩
  intro remaining
  unfold next
  by_cases hlt : Q s minv n mem < R
  · rw [if_pos hlt]
    have hv : MixedMontgomery.normalize R N (Q s minv n mem) = Q s minv n mem := by
      simp [MixedMontgomery.normalize, show ¬R ≤ Q s minv n mem from by omega]
    rw [hv]
    exact retained_represents (raw s minv n mem) hc.1 hlt
  · rw [if_neg hlt]
    exact entry_represents _ _ _ hf

theorem square_congr (N a b : Nat) (h : a%N=b%N) :
    Model.montMul N R a a = Model.montMul N R b b := by
  have hc : (a : ZMod N) = (b : ZMod N) := (ZMod.natCast_eq_natCast_iff a b N).2 h
  unfold Model.montMul
  rw [hc]

theorem iterate_congr (N k a b : Nat) (h : a%N=b%N) :
    ((fun x => Model.montMul N R x x)^[k] a)%N =
      ((fun x => Model.montMul N R x x)^[k] b)%N := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', square_congr N _ _ ih]

theorem memory_value (k : Nat) (hk : 1 ≤ k) (mem : ByteArray) (A N : Nat)
    (ha : Represents mem A) (hm : Model.FastRepresents mem 0 8 N) (hpos : 0 < N) (hodd : Odd N)
    (hnlow : ∀ i < 8, (n i).toNat = N / 2^(244*i) % 2^244)
    (hnhigh : (n 8).toNat = N / 2^1952) (hinv : (N*minv.toNat+1)%2^256=0) :
    ∃ v, Model.FastRepresents (memory s minv n k mem) 2368 8 v ∧
      v%N = ((fun x => Model.montMul N R x x)^[k] A)%N := by
  induction k generalizing mem A with
  | zero => omega
  | succ k ih =>
    have hr := one_round s minv n mem A N ha hm hpos hodd hnlow hnhigh hinv
    let v := MixedMontgomery.normalize R N (Q s minv n mem)
    have he : v%N = (Model.montMul N R A A)%N := by
      simpa only [Nat.mod_mod] using congrArg (fun x => x%N) hr.2.2
    by_cases hk0 : k=0
    · subst k
      refine ⟨v, ?_, ?_⟩
      · simpa only [memory, ↓reduceIte] using hr.1
      · simpa using he
    · obtain ⟨w, hw, hwv⟩ := ih (by omega) (next s minv n k mem) v (hr.2.1 k)
        ((next_live s minv n k mem).modulus N hm)
      refine ⟨w, ?_, ?_⟩
      · simpa only [memory, if_neg hk0] using hw
      · rw [hwv, iterate_congr N k v (Model.montMul N R A A) he, Function.iterate_succ_apply]

#print axioms tail_represents
#print axioms memory_live
#print axioms one_round
#print axioms memory_value
end HistoricalSearch.PureLoop
