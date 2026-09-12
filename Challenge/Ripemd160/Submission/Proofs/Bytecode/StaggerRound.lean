import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerBoolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactInput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
open Paired144Core Paired144Boolean
open PairedLaneRoundSemantic (scalarSum)

def rawSum (mode : Nat) (a b c d message k : BitVec 256) : BitVec 256 :=
  (((a + StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode) b c d) + message) +
    StaggerBoolean.key mode pairMask k)

theorem rawSum_canonical (mode : Nat) (hm : mode < 9)
    (a : BitVec 256) (bl br cl cr dl dr : BitVec 32) (message k : BitVec 256) :
    rawSum mode a (pack bl br) (pack cl cr) (pack dl dr) message k =
      (((a + StaggerBoolean.canonical mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr)) + message) + k) := by
  have hb := StaggerBoolean.raw_add_key mode hm pairMask (StaggerBoolean.selector mode)
    (pack bl br) (pack cl cr) (pack dl dr) k (StaggerBoolean.selector_supported mode)
    (StaggerBoolean.pack_supported _ _) (StaggerBoolean.pack_supported _ _) (StaggerBoolean.pack_supported _ _)
  unfold rawSum
  calc
    ((a + StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr)) + message) + StaggerBoolean.key mode pairMask k =
      (a + message) + (StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr) + StaggerBoolean.key mode pairMask k) := by ac_rfl
    _ = (a + message) + (StaggerBoolean.canonical mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr) + k) := by rw [hb]
    _ = _ := by ac_rfl

theorem rawSum_pack (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (message : BitVec 256)
    (hmsg : message = pack wl wr) :
    rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr) message (pack kl kr) =
      (((pack al ar + pack (f (StaggerBoolean.leftGroup mode) (BitVec.allOnes 32) bl cl dl)
        (f (StaggerBoolean.rightGroup mode) (BitVec.allOnes 32) br cr dr)) + pack wl wr) + pack kl kr) := by
  rw [rawSum_canonical mode hm, hmsg, StaggerBoolean.canonical_pack mode hm]

theorem rawSum_inputs (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (message : BitVec 256)
    (hmsg : message = pack wl wr) :
    let x := rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr) message (pack kl kr)
    let a := scalarSum (StaggerBoolean.leftGroup mode) al bl cl dl wl kl
    let b := scalarSum (StaggerBoolean.rightGroup mode) ar br cr dr wr kr
    Paired144CompactInput.compact x = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72) ∧
      normalize x = pack a b := by
  dsimp only
  rw [rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ message hmsg]
  constructor
  · exact Paired144CompactInput.compact_four_adds _ _ _ _ _ _ _ _
  · exact Paired144CompactInput.normalize_four_adds _ _ _ _ _ _ _ _

#print axioms rawSum_canonical
#print axioms rawSum_pack
#print axioms rawSum_inputs
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
