import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Frame
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RecognitionAccumulator J2Accumulator J2Raw

def last (n : Nat) : Nat := 8*((n-1)/251)+(n-251*((n-1)/251))/32
def blockStart (k : Nat) : Nat := 251*(k/8)
def stop (n k : Nat) : Nat := min n (blockStart k+251)
def full (n k : Nat) : Nat := if k < 8 then blockStart k+32*((stop n k-blockStart k)/32) else stop n k - 32
def current (input : ByteArray) (n k : Nat) : J2Raw.Frame :=
  ⟨J2Accumulator.accumulate input n k, UInt256.ofNat (offset k), wordAt k,
    UInt256.ofNat (full n k), UInt256.ofNat (stop n k), UInt256.ofNat n⟩
def isTail (n k : Nat) : Prop := k=last n ∨ k%8=7
instance (n k : Nat) : Decidable (isTail n k) := inferInstanceAs (Decidable (_ ∨ _))

theorem last_lt (n : Nat) (hn : Allowed n) : last n < 32 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def Facts (n k : Nat) : Prop :=
  (UInt256.ofNat (offset k)).toNat = offset k ∧
  (UInt256.ofNat (full n k)).toNat = full n k ∧
  (UInt256.ofNat (stop n k)).toNat = stop n k ∧
  (UInt256.ofNat n).toNat = n ∧
  (offset k < full n k ↔ ¬ isTail n k) ∧
  (isTail n k → (stop n k = n ↔ k=last n)) ∧
  (¬ isTail n k → J2Accumulator.width n k = 32 ∧
    UInt256.add (UInt256.ofNat 32) (UInt256.ofNat (offset k)) = UInt256.ofNat (offset (k+1)) ∧
    full n k = full n (k+1) ∧ stop n k = stop n (k+1)) ∧
  (isTail n k → UInt256.sub (UInt256.ofNat 256)
    (UInt256.shiftLeft (UInt256.sub (UInt256.ofNat (stop n k)) (UInt256.ofNat (offset k))) (UInt256.ofNat 3)) =
       J2Accumulator.shift n k) ∧
  (isTail n k → k < last n →
    UInt256.ofNat (stop n k) = UInt256.ofNat (offset (k+1)) ∧
    emin (UInt256.ofNat (stop n k)) (UInt256.ofNat n) = UInt256.ofNat (stop n (k+1)) ∧
    UInt256.sub (UInt256.ofNat (stop n (k+1))) (UInt256.ofNat 32) = UInt256.ofNat (full n (k+1)))

private theorem facts_closed (n : Nat) (hn : Allowed n) :
    ∀ k : Fin 32, k.val ≤ last n → Facts n k.val := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Facts
  all_goals decide

theorem facts (n k : Nat) (hn : Allowed n) (hk : k≤last n) : Facts n k :=
  facts_closed n hn ⟨k,by have := last_lt n hn; omega⟩ hk

theorem init_current (input : ByteArray) (n : Nat) (hn : Allowed n) :
    initResult n = current input n 0 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private theorem shr0 (x : UInt256) : UInt256.shiftRight x (UInt256.ofNat 0) = x := by
  apply Word.word_ext
  rw [Word.shiftRight_toNat x (by decide)]
  simp only [Nat.shiftRight_zero]

private theorem word_next_normal (k : Nat) (hk : k%8≠7) :
    RecognitionRecurrence.advance 32 (wordAt k) = wordAt (k+1) := by simp only [wordAt, if_neg hk]

private theorem word_next_tail (k : Nat) (hk : k%8=7) :
    RecognitionRecurrence.advance 114 (wordAt k) = wordAt (k+1) := by simp only [wordAt, if_pos hk]

theorem normal_next (s : State) (n k : Nat) (hn : Allowed n) (hk : k≤last n)
    (ht : ¬ isTail n k) :
    normalResult s (current s.executionEnv.calldata n k) = current s.executionEnv.calldata n (k+1) := by
  obtain ⟨ho,hf,he,hl,hr,hfin,hnormal,htail,hnext⟩ := facts n k hn hk
  obtain ⟨hw,ha,hfn,hen⟩ := hnormal ht
  have hm : k%8≠7 := by intro h; exact ht (Or.inr h)
  simp only [normalResult, current, J2Accumulator.accumulate, J2Accumulator.piece,
    J2Accumulator.shift, hw, Nat.sub_self, Nat.zero_mul, shr0, ho, ha, hfn, hen,
    word_next_normal k hm]

theorem tail_acc (s : State) (n k : Nat) (hn : Allowed n) (hk : k≤last n)
    (ht : isTail n k) :
    tailResult s (current s.executionEnv.calldata n k) =
      {current s.executionEnv.calldata n k with acc := J2Accumulator.accumulate s.executionEnv.calldata n (k+1)} := by
  obtain ⟨ho,hf,he,hl,hr,hfin,hnormal,htail,hnext⟩ := facts n k hn hk
  simp only [tailResult, current, J2Accumulator.accumulate, J2Accumulator.piece,
    htail ht, ho, RawExpressionAC.xor_comm]

theorem transition_next (s : State) (n k : Nat) (hn : Allowed n) (hk : k<last n)
    (ht : isTail n k) :
    transitionResult (tailResult s (current s.executionEnv.calldata n k)) =
      current s.executionEnv.calldata n (k+1) := by
  obtain ⟨ho,hf,he,hl,hr,hfin,hnormal,htail,hnext⟩ := facts n k hn (by omega)
  obtain ⟨ha,hen,hfn⟩ := hnext ht hk
  have hm : k%8=7 := by rcases ht with h|h; omega; exact h
  rw [tail_acc s n k hn (by omega) ht]
  simp only [transitionResult, current, word_next_tail k hm]
  rw [hen, hfn, ha]

#print axioms facts
#print axioms normal_next
#print axioms tail_acc
#print axioms transition_next
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Frame
