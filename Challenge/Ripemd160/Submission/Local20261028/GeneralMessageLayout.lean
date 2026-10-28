import Challenge.Ripemd160.Submission.Local20261028.GeneralCertificate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.GeneralMessageLayout
open EvmSemantics
open RipemdTableOrder20261027
def addresses : Array Nat := #[0, 414, 90, 316, 108, 432, 468, 32, 202, 608, 604, 604, 234, 270, 728, 594, 66, 746, 142, 842, 324, 342, 10, 378, 36, 54, 504, 94, 76, 522, 540, 558, 576, 146, 594, 180, 666, 630, 62, 702, 14, 756, 774, 838, 320, 820, 138, 810, 828, 846, 882, 918, 134, 954, 864, 990, 612, 684, 18, 472, 58]
def barriers : Array Nat := #[26, 22, 18, 14, 26, 22, 18, 14, 26, 22, 18, 14, 26, 18, 14, 14, 14, 26, 22, 22, 18, 18, 14, 14, 26, 26, 22, 22, 18, 18, 18, 26, 14, 14, 18, 26, 22, 14, 26, 22, 18, 14, 26, 14, 22, 14, 14, 14, 22, 22, 14, 14, 26, 26, 26, 14, 22, 14, 14, 14, 18, 22, 18, 18, 26, 26, 22, 14, 14, 14, 18, 16, 18, 22, 14, 14, 14]
def wordAddress (k : Nat) : Nat := if k < 8 then 252+4*k else 162+4*(k-8)
theorem low_sources : ∀ slot : Fin 61, ∀ j : Fin 4,
    result selected (addresses[slot.val]!+28+j.val) =
      initial (wordAddress StaggerTableLayout.slots[slot.val]!+j.val) := by decide +kernel
theorem high_sources : ∀ i : Fin 77, ∀ j : Fin 4,
    result selected (addresses[StaggerTableLayout.pairIndices[i.val]!]!+10+j.val) =
      initial (wordAddress Crypto.Ripemd160.rP[i.val+3]!+j.val) := by decide +kernel
theorem barrier_sources : ∀ i : Fin 77,
    14 ≤ barriers[i.val]! ∧ barriers[i.val]! ≤ 26 ∧
      result selected (addresses[StaggerTableLayout.pairIndices[i.val]!]!+barriers[i.val]!) = 0 := by
  decide +kernel
#print axioms low_sources
#print axioms high_sources
#print axioms barrier_sources
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.GeneralMessageLayout
