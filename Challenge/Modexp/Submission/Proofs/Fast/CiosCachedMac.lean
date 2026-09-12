import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_l2Mac (pc : Nat) (w : Fin 33) (x tl ts : UInt256)
    (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 91 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hk : k+1 < n)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 2112 + 32 * (n - 2 - k))
    (hts : ts.toNat = 2112 + 32 * (n - 1 - k))
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    runInstructions (l2Program w x tl ts) (l2At pc s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At (pc+(w.val+35)) s mid bi mu c0 pb n i (k+1) hd ent pdst ret rest) := by
  have h := CiosCachedL2.run_step w s (UInt256.ofNat pc) mid bi mu c0 n k x tl ts hx htl hts
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hk hpush
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, l2At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
