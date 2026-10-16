import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Frame
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RecognitionAccumulator J2Accumulator J2Raw

def last (n : Nat) : Nat := 8*((n-1)/251)+(n-251*((n-1)/251)-1)/32
def blockStart (k : Nat) : Nat := 251*(k/8)
/-- The generic 1000-byte route leaves its segment stop unclamped. -/
def stop (n k : Nat) : Nat :=
  if n = 1000 then blockStart k + 251 else min n (blockStart k+251)
/-- Only the initial dispatch uses a segment-relative bound. Generic transitions
store the final calldata bound, even while further segments remain. -/
def fullW (n k : Nat) : UInt256 :=
  UInt256.sub (UInt256.ofNat (if n = 1000 ∧ 8 ≤ k then n else stop n k)) (UInt256.ofNat 32)
def current (input : ByteArray) (n k : Nat) : J2Raw.Frame :=
  ⟨J2Accumulator.accumulate input n k, UInt256.ofNat (offset k), wordAt k,
    fullW n k, UInt256.ofNat (stop n k), UInt256.ofNat n⟩
def isTail (n k : Nat) : Prop := k=last n ∨ k%8=7
instance (n k : Nat) : Decidable (isTail n k) := inferInstanceAs (Decidable (_ ∨ _))

theorem last_lt (n : Nat) (hn : Allowed n) : last n < 32 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Facts consumed by the unrolled scanner. There is deliberately no normal
word `off < full` guard: later generic segments store the final bound. -/
def Facts (n k : Nat) : Prop :=
  (UInt256.ofNat (offset k)).toNat = offset k ∧
  (UInt256.ofNat (stop n k)).toNat = stop n k ∧
  (UInt256.ofNat n).toNat = n ∧
  (isTail n k → (n ≤ stop n k ↔ k=last n)) ∧
  (¬ isTail n k → J2Accumulator.width n k = 32 ∧
    UInt256.add (UInt256.ofNat 32) (UInt256.ofNat (offset k)) = UInt256.ofNat (offset (k+1)) ∧
    fullW n k = fullW n (k+1) ∧ stop n k = stop n (k+1)) ∧
  (isTail n k →
    (if stop n k < n then UInt256.ofNat 40
      else UInt256.shiftLeft (UInt256.sub (UInt256.ofNat (offset k)) (fullW n k)) (UInt256.ofNat 3)) =
      J2Accumulator.shift n k) ∧
  (n ≠ 256 → isTail n k → k < last n →
    UInt256.ofNat (stop n k) = UInt256.ofNat (offset (k+1)) ∧
    (if UInt256.land (UInt256.ofNat n) (UInt256.ofNat 16) = 0
      then UInt256.add (UInt256.ofNat 251) (UInt256.ofNat (stop n k))
      else UInt256.ofNat n) = UInt256.ofNat (stop n (k+1)) ∧
    UInt256.sub (UInt256.ofNat n) (UInt256.ofNat 32) = fullW n (k+1))

private theorem facts_closed (n : Nat) (hn : Allowed n) :
    ∀ k : Fin 32, k.val ≤ last n → Facts n k.val := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Facts
  all_goals decide

theorem facts (n k : Nat) (hn : Allowed n) (hk : k≤last n) : Facts n k :=
  facts_closed n hn ⟨k,by have := last_lt n hn; omega⟩ hk

/-! ### Position in the unrolled word chain

Word `k` runs in chain block `blk n k`: its segment's tail is word `segTail n k`, and the chain ends at block 7
(the tail), so a word `r` places before its tail runs in block `7 - r`. -/

def segTail (n k : Nat) : Nat := min (last n) (8*(k/8)+7)
def blk (n k : Nat) : Nat := 7 - (segTail n k - k)

def ChainFacts (n k : Nat) : Prop :=
  blk n k ≤ 7 ∧
  (isTail n k → blk n k = 7) ∧
  (¬ isTail n k → blk n k < 7 ∧ blk n (k+1) = blk n k + 1) ∧
  (k = 0 → J2Raw.dispatchTarget (UInt256.ofNat 0) (fullW n 0) = UInt256.ofNat (J2Raw.blockPC (blk n 0)))

private theorem chain_closed (n : Nat) (hn : Allowed n) :
    ∀ k : Fin 32, k.val ≤ last n → ChainFacts n k.val := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold ChainFacts
  all_goals decide

theorem chain (n k : Nat) (hn : Allowed n) (hk : k≤last n) : ChainFacts n k :=
  chain_closed n hn ⟨k,by have := last_lt n hn; omega⟩ hk

/-- The surviving nonfinal boundaries have only length376 or1000. Their next
chain entry is block4 or block0 respectively, independently of the SWAR data. -/
theorem transition_chain (n k : Nat) (hn : Allowed n) (hn256 : n ≠ 256)
    (hk : k < last n) (ht : isTail n k) :
    J2Raw.transitionTarget (UInt256.ofNat n) = UInt256.ofNat (J2Raw.blockPC (blk n (k+1))) := by
  have hclosed : ∀ j : Fin 32, j.val < last n → isTail n j.val →
      J2Raw.transitionTarget (UInt256.ofNat n) = UInt256.ofNat (J2Raw.blockPC (blk n (j.val+1))) := by
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | contradiction | decide
  exact hclosed ⟨k, by have := last_lt n hn; omega⟩ hk ht

/-- Nonfinal boundaries project by the literal five-byte shift; only the
final tail consults `full`. This matches the ordered finish branch. -/
theorem tail_shift (n k : Nat) (hn : Allowed n) (hk : k ≤ last n) (ht : isTail n k) :
    (if stop n k < n then UInt256.ofNat 40
      else UInt256.shiftLeft (UInt256.sub (UInt256.ofNat (offset k)) (fullW n k)) (UInt256.ofNat 3)) =
      J2Accumulator.shift n k :=
  (facts n k hn hk).2.2.2.2.2.1 ht

theorem init_current (input : ByteArray) (n : Nat) (hn : Allowed n) :
    initResult n = current input n 0 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private theorem shr0 (x : UInt256) : UInt256.shiftRight x (UInt256.ofNat 0) = x := by
  apply Word.word_ext
  rw [Word.shiftRight_toNat x (by decide)]
  simp only [Nat.shiftRight_zero]

private theorem nw_closed : ∀ k : Fin 32, k.val % 8 ≠ 7 →
    J2Raw.nw (wordAt k.val) = wordAt (k.val+1) := by decide

private theorem nw_next (k : Nat) (hk32 : k < 32) (hk : k%8≠7) :
    J2Raw.nw (wordAt k) = wordAt (k+1) := nw_closed ⟨k, hk32⟩ hk

private theorem word_next_normal (k : Nat) (hk : k%8≠7) :
    RecognitionRecurrence.advance 32 (wordAt k) = wordAt (k+1) := by simp only [wordAt, if_neg hk]

private theorem tw_closed : ∀ k : Fin 32, k.val % 8 = 7 →
    J2Raw.tw (wordAt k.val) = wordAt (k.val+1) := by decide

private theorem tw_next (k : Nat) (hk32 : k < 32) (hk : k%8=7) :
    J2Raw.tw (wordAt k) = wordAt (k+1) := tw_closed ⟨k, hk32⟩ hk

private theorem word_next_tail (k : Nat) (hk : k%8=7) :
    RecognitionRecurrence.advance 114 (wordAt k) = wordAt (k+1) := by simp only [wordAt, if_pos hk]

theorem normal_next (s : State) (n k : Nat) (hn : Allowed n) (hk : k≤last n)
    (ht : ¬ isTail n k) :
    normalResult s (current s.executionEnv.calldata n k) = current s.executionEnv.calldata n (k+1) := by
  obtain ⟨ho,he,hl,hfin,hnormal,htail,hnext⟩ := facts n k hn hk
  obtain ⟨hw,ha,hfn,hen⟩ := hnormal ht
  have hm : k%8≠7 := by intro h; exact ht (Or.inr h)
  simp only [normalResult, current, J2Accumulator.accumulate, J2Accumulator.piece,
    J2Accumulator.shift, hw, Nat.sub_self, Nat.zero_mul, shr0, ho, ha, hfn, hen,
    nw_next k (by have := last_lt n hn; omega) hm]

theorem tail_acc (s : State) (n k : Nat) (hn : Allowed n) (hk : k≤last n)
    (ht : isTail n k) :
    tailResult s (current s.executionEnv.calldata n k) =
      {current s.executionEnv.calldata n k with acc := J2Accumulator.accumulate s.executionEnv.calldata n (k+1)} := by
  obtain ⟨ho,he,hl,hfin,hnormal,htail,hnext⟩ := facts n k hn hk
  simp only [tailResult, current, J2Accumulator.accumulate, J2Accumulator.piece,
    he, hl, htail ht, ho, RawExpressionAC.xor_comm]

theorem transition_next (s : State) (n k : Nat) (hn : Allowed n) (hk : k<last n)
    (ht : isTail n k) (hn256 : n ≠ 256) :
    transitionResult (tailResult s (current s.executionEnv.calldata n k)) =
      current s.executionEnv.calldata n (k+1) := by
  obtain ⟨ho,he,hl,hfin,hnormal,htail,hnext⟩ := facts n k hn (by omega)
  obtain ⟨ha,hen,hfn⟩ := hnext hn256 ht hk
  have hm : k%8=7 := by rcases ht with h|h; omega; exact h
  rw [tail_acc s n k hn (by omega) ht]
  simp only [transitionResult, transitionStop, current, tw_next k (by have := last_lt n hn; omega) hm]
  rw [hen, hfn, ha]

#print axioms facts
#print axioms chain
#print axioms normal_next
#print axioms tail_acc
#print axioms transition_next
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Frame
