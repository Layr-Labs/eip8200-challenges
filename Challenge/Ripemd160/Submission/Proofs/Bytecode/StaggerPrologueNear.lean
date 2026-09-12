import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrologueNear
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound

def Near (x y : UInt256) : Prop := (bits x).setWidth 176 = (bits y).setWidth 176

theorem near_refl (x : UInt256) : Near x x := rfl

theorem near_of_eq {x y : UInt256} (h : x=y) : Near x y := congrArg (fun z : UInt256 => (bits z).setWidth 176) h

theorem near_add {x x' y y' : UInt256} (hx : Near x x') (hy : Near y y') :
    Near (UInt256.add x y) (UInt256.add x' y') := by
  unfold Near at *
  rw [bits_add, bits_add, BitVec.setWidth_add _ _ (by decide),
    BitVec.setWidth_add _ _ (by decide), hx,hy]

theorem near_xor {x x' y y' : UInt256} (hx : Near x x') (hy : Near y y') :
    Near (UInt256.xor x y) (UInt256.xor x' y') := by
  unfold Near at *
  simp only [bits_xor,BitVec.setWidth_xor,hx,hy]

theorem near_and {x x' y y' : UInt256} (hx : Near x x') (hy : Near y y') :
    Near (UInt256.land x y) (UInt256.land x' y') := by
  unfold Near at *
  simp only [bits_land,BitVec.setWidth_and,hx,hy]

theorem near_or {x x' y y' : UInt256} (hx : Near x x') (hy : Near y y') :
    Near (UInt256.lor x y) (UInt256.lor x' y') := by
  unfold Near at *
  simp only [bits_lor,BitVec.setWidth_or,hx,hy]

theorem mask_eq {x y : UInt256} (h : Near x y) :
    UInt256.land x pairWord = UInt256.land y pairWord := by
  have hl := congrArg (fun z : BitVec 176 => z.extractLsb' 0 32) h
  have hh := congrArg (fun z : BitVec 176 => z.extractLsb' 144 32) h
  rw [BitVec.extractLsb'_setWidth_of_le (by decide),
    BitVec.extractLsb'_setWidth_of_le (by decide)] at hl hh
  apply bits_injective
  simp only [bits_land,pairWord,bits_word,←normalize_eq_and,normalize,low,high,hl,hh]

theorem rotate_eq (r s : Nat) (hc : ¬ usesCompact r s) {x y : UInt256}
    (h : Near x y) : wordRotate x r s = wordRotate y r s := by
  unfold wordRotate
  rw [if_neg hc,if_neg hc,mask_eq h]

def LaneNear (q z : WordLane) : Prop :=
  Near q.a z.a ∧ Near q.b z.b ∧ Near q.c z.c ∧ Near q.d z.d ∧ Near q.e z.e

theorem t_eq (r s : Nat) (hc : ¬ usesCompact r s) (message k : UInt256)
    (q z : WordLane) (h : LaneNear q z) :
    StaggerWord.t 0 r s message k q = StaggerWord.t 0 r s message k z := by
  have hr : Near (StaggerWord.raw 0 (StaggerWord.selector 0) q.b q.c q.d)
      (StaggerWord.raw 0 (StaggerWord.selector 0) z.b z.c z.d) :=
    near_xor (near_xor (near_xor h.2.1 h.2.2.1) (near_refl _))
      (near_or h.2.2.2.1 (near_and h.2.2.1 (near_refl _)))
  have hs : Near (StaggerWord.sum 0 q.a q.b q.c q.d message k)
      (StaggerWord.sum 0 z.a z.b z.c z.d message k) :=
    near_add (near_add (near_add h.1 hr) (near_refl _)) (near_refl _)
  unfold StaggerWord.t
  rw [rotate_eq r s hc hs]
  exact mask_eq (near_add (near_refl _) h.2.2.2.2)

theorem step_near (r s : Nat) (hc : ¬ usesCompact r s) (message k : UInt256)
    (q z : WordLane) (h : LaneNear q z) (hb : q.b=z.b) (hc' : q.c=z.c) :
    LaneNear (StaggerWord.step 0 r s message k q) (StaggerWord.step 0 r s message k z) ∧
    (StaggerWord.step 0 r s message k q).b=(StaggerWord.step 0 r s message k z).b ∧
    (StaggerWord.step 0 r s message k q).c=(StaggerWord.step 0 r s message k z).c ∧
    (StaggerWord.step 0 r s message k q).d=(StaggerWord.step 0 r s message k z).d := by
  have ht := t_eq r s hc message k q z h
  have hd : UInt256.land (wordShift q.c 28) pairWord = UInt256.land (wordShift z.c 28) pairWord := by rw [hc']
  exact ⟨⟨h.2.2.2.2, near_of_eq ht, near_of_eq hb, near_of_eq hd,h.2.2.2.1⟩,ht,hb,hd⟩

theorem lane_ext (q z : WordLane) (ha : q.a=z.a) (hb : q.b=z.b) (hc : q.c=z.c)
    (hd : q.d=z.d) (he : q.e=z.e) : q=z := by
  cases q; cases z
  cases ha; cases hb; cases hc; cases hd; cases he
  rfl

theorem three_steps (m0 m1 m2 k0 k1 k2 : UInt256) (q z : WordLane)
    (h : LaneNear q z) (hb : q.b=z.b) (hc : q.c=z.c) :
    StaggerWord.step 0 15 15 m2 k2 (StaggerWord.step 0 14 13 m1 k1 (StaggerWord.step 0 11 11 m0 k0 q)) =
    StaggerWord.step 0 15 15 m2 k2 (StaggerWord.step 0 14 13 m1 k1 (StaggerWord.step 0 11 11 m0 k0 z)) := by
  have h0 := step_near 11 11 (by decide) m0 k0 q z h hb hc
  have h1 := step_near 14 13 (by decide) m1 k1 _ _ h0.1 h0.2.1 h0.2.2.1
  have h2 := step_near 15 15 (by decide) m2 k2 _ _ h1.1 h1.2.1 h1.2.2.1
  exact lane_ext _ _ h0.2.2.2 h2.2.1 h2.2.2.1 h2.2.2.2 h1.2.2.2

theorem fold_three (message : Nat → UInt256) (q z : WordLane)
    (h : LaneNear q z) (hb : q.b=z.b) (hc : q.c=z.c) :
    StaggerTerminal75.fold message 3 q = StaggerTerminal75.fold message 3 z := by
  rw [StaggerTerminal75.fold_prefix message 3 (by decide),
    StaggerTerminal75.fold_prefix message 3 (by decide)]
  exact three_steps (message 0) (message 1) (message 2) _ _ _ q z h hb hc

theorem fold_eq (message : Nat → UInt256) (n : Nat) (hn : 3≤n) (q z : WordLane)
    (h : LaneNear q z) (hb : q.b=z.b) (hc : q.c=z.c) :
    StaggerTerminal75.fold message n q = StaggerTerminal75.fold message n z := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => exact fold_three message q z h hb hc
  | succ k ih => exact congrArg (StaggerTerminal75.step (3+k) (message (3+k))) (ih (by omega))

#print axioms mask_eq
#print axioms three_steps
#print axioms fold_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrologueNear
