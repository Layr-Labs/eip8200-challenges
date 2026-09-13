import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrologueNear
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerModeSeven
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
open Paired144WordRotation PairedLaneGroupTwoHoist
open Paired80Algorithm (leftFold rightFold)

/-- Thirteen instructions with the existing lower-lane selector. -/
def raw (b c d : UInt256) : UInt256 :=
  UInt256.xor d (UInt256.xor lowerWord
    (UInt256.land (UInt256.xor lowerWord b) (UInt256.xor c (UInt256.land b d))))

theorem canonical_formula (mask s b c d : BitVec w)
    (hs : Supported mask s) (hb : Supported mask b)
    (hc : Supported mask c) (hd : Supported mask d) :
    d ^^^ ((mask ^^^ s) ^^^ (((mask ^^^ s) ^^^ b) &&& (c ^^^ (b &&& d)))) =
      StaggerBoolean.canonical 7 mask s b c d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hs' := congrArg (fun x : BitVec w => x.getLsbD i) hs
  have hb' := congrArg (fun x : BitVec w => x.getLsbD i) hb
  have hc' := congrArg (fun x : BitVec w => x.getLsbD i) hc
  have hd' := congrArg (fun x : BitVec w => x.getLsbD i) hd
  simp only [Supported, BitVec.getLsbD_and] at hs' hb' hc' hd'
  simp only [StaggerBoolean.canonical, BitVec.getLsbD_xor,
    BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases hm0 : mask.getLsbD i <;> cases hs0 : s.getLsbD i <;>
    cases hb0 : b.getLsbD i <;> cases hc0 : c.getLsbD i <;>
    cases hd0 : d.getLsbD i <;> simp_all

theorem raw_canonical (b c d : UInt256)
    (hb : Supported pairMask (bits b)) (hc : Supported pairMask (bits c))
    (hd : Supported pairMask (bits d)) :
    bits (raw b c d) =
      StaggerBoolean.canonical 7 pairMask (StaggerBoolean.selector 7)
        (bits b) (bits c) (bits d) := by
  have ht : bits lowerWord = pairMask ^^^ StaggerBoolean.selector 7 := by decide
  simpa only [raw, bits_xor, bits_land, ht] using
    canonical_formula pairMask (StaggerBoolean.selector 7) (bits b) (bits c) (bits d)
      (StaggerBoolean.selector_supported 7) hb hc hd

def sum (a b c d message k : UInt256) : UInt256 :=
  UInt256.add (UInt256.add (UInt256.add a (raw b c d)) message) k

theorem sum_eq (a b c d message k : UInt256)
    (hb : Supported pairMask (bits b)) (hc : Supported pairMask (bits c))
    (hd : Supported pairMask (bits d)) :
    sum a b c d message k =
      StaggerWord.sum 7 a b c d message (StaggerWord.key 7 k) := by
  apply bits_injective
  rw [StaggerWord.bits_sum]
  change ((bits a + bits (raw b c d)) + bits message) + bits k = _
  rw [raw_canonical b c d hb hc hd]
  unfold StaggerRound.rawSum
  have hr := StaggerBoolean.raw_add_key 7 (by decide) pairMask
    (StaggerBoolean.selector 7) (bits b) (bits c) (bits d) (bits k)
    (StaggerBoolean.selector_supported 7) hb hc hd
  have rearrange (a b c d : BitVec 256) : ((a+b)+c)+d = (a+c)+(b+d) := by ac_rfl
  rw [rearrange, rearrange, hr]

def enabled (i : Nat) : Prop := 45 ≤ i ∧ i ≤ 47
instance (i : Nat) : Decidable (enabled i) := inferInstanceAs (Decidable (45 ≤ i ∧ i ≤ 47))
def physicalKey (i : Nat) : UInt256 :=
  if enabled i then StaggerAlgorithm.key i else StaggerAlgorithm.physicalKey i

def step (i : Nat) (message : UInt256) (q : WordLane) : WordLane :=
  if enabled i then
    ⟨q.e, UInt256.land (UInt256.add (wordRotate
      (sum q.a q.b q.c q.d message (physicalKey i))
      Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i+3]!) q.e) pairWord,
      q.b, UInt256.land (wordShift q.c 23) pairWord, q.d⟩
  else StaggerTerminal75.step i message q

def fold (message : Nat → UInt256) : Nat → WordLane → WordLane
  | 0,q => q
  | i+1,q => step i (message i) (fold message i q)

theorem step_eq (i : Nat) (message : UInt256) (q : WordLane)
    (hb : Supported pairMask (bits q.b)) (hc : Supported pairMask (bits q.c))
    (hd : Supported pairMask (bits q.d)) :
    step i message q = StaggerTerminal75.step i message q := by
  by_cases he : enabled i
  · have hm : StaggerAlgorithm.mode i = 7 := by
      unfold enabled at he
      simp only [StaggerAlgorithm.mode, if_neg (show ¬ i<13 from by omega),
        if_neg (show ¬ i<16 from by omega), if_neg (show ¬ i<29 from by omega),
        if_neg (show ¬ i<32 from by omega), if_neg (show ¬ i<45 from by omega),
        if_pos (show i<48 from by omega)]
    have hterminal : ¬(i=75 ∨ i=76) := by unfold enabled at he; omega
    rw [step, if_pos he, physicalKey, if_pos he,
      sum_eq q.a q.b q.c q.d message (StaggerAlgorithm.key i) hb hc hd]
    rw [StaggerTerminal75.step, if_neg hterminal]
    have ha : ¬ StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! := by
      have hi : i = 45 ∨ i = 46 ∨ i = 47 := by unfold enabled at he; omega
      rcases hi with rfl | rfl | rfl <;> decide
    unfold StaggerAlgorithm.step StaggerAlgorithm.physicalKey
    rw [if_neg ha, hm]
    rfl
  · exact if_neg he

theorem fold_crypto (message : Nat → UInt256) (words : Nat → UInt32)
    (count : Nat) (hcount : count ≤ 75) (l r : CryptoLane)
    (hm : StaggerAlgorithm.MessageReady message words count) :
    fold message count (packCrypto l (rightFold words 3 r)) =
      packCrypto (leftFold words count l) (rightFold words (count+3) r) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have ht : StaggerAlgorithm.MessageReady message words i := fun j hj => hm j (by omega)
    rw [fold, ih (by omega) ht]
    rw [step_eq i (message i) (packCrypto (leftFold words i l) (rightFold words (i+3) r))
      (StaggerBoolean.pack_supported _ _) (StaggerBoolean.pack_supported _ _)
      (StaggerBoolean.pack_supported _ _)]
    rw [StaggerTerminal75.step, if_neg (by omega)]
    exact StaggerAlgorithm.step_of_crypto words i (by omega) (message i) _ _
      (hm i (by omega))

private theorem fold_lastTwo (message : Nat → UInt256) (n : Nat) (q : WordLane)
    (h0 : ¬ enabled n) (h1 : ¬ enabled (n+1)) :
    fold message (n+2) q =
      StaggerTerminal75.step (n+1) (message (n+1))
        (StaggerTerminal75.step n (message n) (fold message n q)) := by
  change step (n+1) (message (n+1)) (step n (message n) (fold message n q)) = _
  simp only [step, if_neg h0, if_neg h1]

private theorem old_lastTwo (message : Nat → UInt256) (n : Nat) (q : WordLane) :
    StaggerTerminal75.fold message (n+2) q =
      StaggerTerminal75.step (n+1) (message (n+1))
        (StaggerTerminal75.step n (message n) (StaggerTerminal75.fold message n q)) := by rfl

theorem fold_eq_terminal (message : Nat → UInt256) (words : Nat → UInt32)
    (l r : CryptoLane) (hm : StaggerAlgorithm.MessageReady message words 77) :
    fold message 77 (packCrypto l (rightFold words 3 r)) =
      StaggerTerminal75.fold message 77 (packCrypto l (rightFold words 3 r)) := by
  have ha := fold_crypto message words 75 (by decide) l r (fun i hi => hm i (by omega))
  have hb := StaggerTerminal75.fold_prefix message 75 (by decide)
    (packCrypto l (rightFold words 3 r))
  have hc := StaggerAlgorithm.fold_crypto message words 75 (by decide) l r
    (fun i hi => hm i (by omega))
  have h75 := ha.trans (hb.trans hc).symm
  have ht := congrArg (fun q : WordLane => StaggerTerminal75.step 76 (message 76)
    (StaggerTerminal75.step 75 (message 75) q)) h75
  exact (fold_lastTwo message 75 _ (by decide) (by decide)).trans
    (ht.trans (old_lastTwo message 75 _).symm)

theorem final_shape (message : Nat → UInt256) (words : Nat → UInt32)
    (l r : CryptoLane) (hm : StaggerAlgorithm.MessageReady message words 77) :
    ∃ d e : UInt256,
      fold message 77 (packCrypto l (rightFold words 3 r)) =
        {packCrypto (leftFold words 77 l) (rightFold words 80 r) with d:=d,e:=e} ∧
      UInt256.land d pairWord =
        (packCrypto (leftFold words 77 l) (rightFold words 80 r)).d ∧
      UInt256.land e pairWord =
        (packCrypto (leftFold words 77 l) (rightFold words 80 r)).e := by
  obtain ⟨d,e,ho,hd,he⟩ := StaggerTerminal75.final_shape message words l r hm
  have h := (fold_eq_terminal message words l r hm).trans ho
  exact ⟨d,e,h,hd,he⟩

theorem fold_early (message : Nat → UInt256) (n : Nat) (hn : n≤45) (q : WordLane) :
    fold message n q = StaggerTerminal75.fold message n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : ¬ enabled n := by unfold enabled; omega
    rw [fold, step, if_neg he, ih (by omega)]
    rfl

theorem fold_three (message : Nat → UInt256) (q : WordLane) :
    fold message 3 q = StaggerTerminal75.fold message 3 q :=
  fold_early message 3 (by decide) q

theorem fold_near (message : Nat → UInt256) (n : Nat) (hn : 3≤n) (q z : WordLane)
    (h : StaggerPrologueNear.LaneNear q z) (hb : q.b=z.b) (hc : q.c=z.c) :
    fold message n q = fold message n z := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
    have hh := StaggerPrologueNear.fold_three message q z h hb hc
    exact (fold_three message q).trans (hh.trans (fold_three message z).symm)
  | succ k ih => exact congrArg (step (3+k) (message (3+k))) (ih (by omega))

#print axioms fold_crypto
#print axioms fold_eq_terminal
#print axioms final_shape
#print axioms fold_near

#print axioms canonical_formula
#print axioms raw_canonical
#print axioms sum_eq
#print axioms step_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerModeSeven
