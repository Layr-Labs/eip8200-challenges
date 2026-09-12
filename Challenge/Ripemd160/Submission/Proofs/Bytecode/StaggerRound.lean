import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerBoolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordMessage
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
open Paired80Core Paired80Boolean Paired80RoundSemantic Paired80Product
open Paired80GroupTwoHoist Paired80CryptoBridge

def rawSum (mode : Nat) (a b c d message k : BitVec 256) : BitVec 256 :=
  normalize (((a + StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode) b c d) + message) +
    StaggerBoolean.key mode pairMask k)

theorem rawSum_canonical (mode : Nat) (hm : mode < 9)
    (a : BitVec 256) (bl br cl cr dl dr : BitVec 32) (message k : BitVec 256) :
    rawSum mode a (pack bl br) (pack cl cr) (pack dl dr) message k =
      normalize (((a + StaggerBoolean.canonical mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr)) + message) + k) := by
  have hb := StaggerBoolean.raw_add_key mode hm pairMask (StaggerBoolean.selector mode)
    (pack bl br) (pack cl cr) (pack dl dr) k (StaggerBoolean.selector_supported mode)
    (pack_supported _ _) (pack_supported _ _) (pack_supported _ _)
  unfold rawSum
  congr 1
  calc
    ((a + StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr)) + message) + StaggerBoolean.key mode pairMask k =
      (a + message) + (StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr) + StaggerBoolean.key mode pairMask k) := by ac_rfl
    _ = (a + message) + (StaggerBoolean.canonical mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr) + k) := by rw [hb]
    _ = _ := by ac_rfl
#print axioms rawSum_canonical

theorem rawSum_pack (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (message : BitVec 256)
    (hmsg : Paired80Message.Eq112 message (pack wl wr)) :
    rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr) message (pack kl kr) =
      pack (scalarSum (StaggerBoolean.leftGroup mode) al bl cl dl wl kl)
        (scalarSum (StaggerBoolean.rightGroup mode) ar br cr dr wr kr) := by
  rw [rawSum_canonical mode hm, Paired80Message.normalize_add_message _ _ _ _ hmsg,
    StaggerBoolean.canonical_pack mode hm]
  exact normalize_four_adds _ _ _ _ _ _ _ _
#print axioms rawSum_pack

def t (mode r s : Nat) (message k : BitVec 256) (q : Lane 256) : BitVec 256 :=
  normalize (rawRotate (rawSum mode q.a q.b q.c q.d message k) r s + q.e)

def step (mode r s : Nat) (message k : BitVec 256) (q : Lane 256) : Lane 256 :=
  ⟨q.e, t mode r s message k q, q.b, normalize ((q.c * factor) >>> 22), q.d⟩

theorem t_pack (mode r s : Nat) (hm : mode < 9)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (wl wr kl kr : BitVec 32) (l q : Lane 32) (message : BitVec 256)
    (hmsg : Paired80Message.Eq112 message (pack wl wr)) :
    t mode r s message (pack kl kr) (packLane l q) =
      pack (scalarT (StaggerBoolean.leftGroup mode) r l.a l.b l.c l.d l.e wl kl)
        (scalarT (StaggerBoolean.rightGroup mode) s q.a q.b q.c q.d q.e wr kr) := by
  unfold t packLane
  rw [rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ message hmsg]
  rw [Paired80Carry.normalize_add_pack _ _ _ (rawRotate_gap _ _ r s hr0 hr hs0 hs)]
  rw [low_rawRotate _ _ r s hr0 hr hs0 hs, high_rawRotate _ _ r s hr0 hr hs0 hs]
  rfl
#print axioms t_pack

theorem step_pack (mode r s : Nat) (hm : mode < 9)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (wl wr kl kr : BitVec 32) (l q : Lane 32) (message : BitVec 256)
    (hmsg : Paired80Message.Eq112 message (pack wl wr)) :
    step mode r s message (pack kl kr) (packLane l q) =
      packLane (scalarStep (StaggerBoolean.leftGroup mode) r wl kl l)
        (scalarStep (StaggerBoolean.rightGroup mode) s wr kr q) := by
  unfold step
  rw [t_pack mode r s hm hr0 hr hs0 hs wl wr kl kr l q message hmsg]
  simp only [packLane, scalarStep]
  rw [show 22 = 32 - 10 from rfl,
    Paired80Rotate.normalize_rotate_product _ _ 10 (by decide) (by decide)]

#print axioms step_pack

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
