import Challenge.Ripemd160.Submission.Local20261028.GeneralMessageLayout
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdSubmission20261101.OrdinaryCertificate
open EvmSemantics RipemdTableOrder20261027
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.GeneralMessageLayout
abbrev Symbol := Sum Nat Nat
def plan : List (Nat × Nat) := [(594, 146), (684, 266), (108, 258), (252, 142), (324, 232), (18, 266), (666, 180), (216, 172), (756, 134), (198, 142), (360, 258), (90, 224), (792, 138), (648, 142), (738, 262), (630, 176), (828, 236), (612, 180), (720, 262), (846, 146), (72, 258), (558, 134), (864, 236), (54, 168), (900, 138), (414, 258), (540, 228), (936, 134), (522, 224), (504, 228), (396, 266), (486, 168), (972, 236), (468, 262), (450, 168), (1008, 180)]
def source (a j : Nat) : Symbol :=
  if a=134 ∧ 9 ≤ j ∧ j<14 then .inr j else .inl (fan (a+j))
def paint (m : Nat → Symbol) (w : Nat × Nat) (a : Nat) : Symbol :=
  if w.1 ≤ a ∧ a < w.1+32 then source w.2 (a-w.1) else m a
def layout : Nat → Symbol := plan.foldl paint (fun a => .inl (fan a))
theorem low_sources : ∀ slot : Fin 61, slot.val ≠ 51 → ∀ j : Fin 4,
    layout (addresses[slot.val]!+28+j.val) =
      .inl (initial (wordAddress Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout.slots[slot.val]!+j.val)) := by
  decide +kernel
theorem high_sources : ∀ i : Fin 77, ∀ j : Fin 4,
    layout (addresses[Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout.pairIndices[i.val]!]!+10+j.val) =
      .inl (initial (wordAddress Crypto.Ripemd160.rP[i.val+3]!+j.val)) := by
  decide +kernel
theorem barrier_sources : ∀ i : Fin 77,
    14 ≤ barriers[i.val]! ∧ barriers[i.val]! ≤ 26 ∧
    layout (addresses[Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout.pairIndices[i.val]!]!+barriers[i.val]!) = .inl 0 := by
  decide +kernel
theorem clear_sources : ∀ a ∈ clearAddresses, layout a = .inl 0 := by decide +kernel
theorem biased_sources : ∀ j : Fin 5, layout (945+j.val) = .inr (9+j.val) := by decide +kernel
theorem unchanged_sources : ∀ a : Fin 1120, a.val < 945 ∨ 950 ≤ a.val →
    layout a.val = .inl (result selected a.val) := by decide +kernel
#print axioms low_sources
#print axioms high_sources
#print axioms barrier_sources
#print axioms clear_sources
#print axioms biased_sources
#print axioms unchanged_sources
end RipemdSubmission20261101.OrdinaryCertificate
