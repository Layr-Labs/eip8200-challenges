import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_l1Mac (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions l1Program (l1At pc s mem bi pa pb n i j pdst ret rest) =
      some (l1At (pc+37) s mem bi pa pb n i (j+1) pdst ret rest) := by
  have h := CiosCachedL1.run_step s (UInt256.ofNat pc) mem bi pa n j
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa + 32*n - 32))
    (UInt256.ofNat (pb-32)) (isFour n) pdst ret rest hcap hact hn32 hj hpa hpaFit
  simpa only [CiosCachedL1.program_matches, CiosCachedL1.state, l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

theorem run_l2Mac (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k+1 < n) :
    runInstructions l2Program (l2At pc s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At (pc+40) s mid bi mu c0 pa pb n i (k+1) pdst ret rest) := by
  have h := CiosCachedL2.run_step s (UInt256.ofNat pc) mid bi mu c0 n k
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa + 32*n - 32))
    (UInt256.ofNat (pb-32)) (isFour n) pdst ret rest hcap hact hn32 hk
  simpa only [CiosCachedL2.program_matches, CiosCachedL2.state, l2At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
