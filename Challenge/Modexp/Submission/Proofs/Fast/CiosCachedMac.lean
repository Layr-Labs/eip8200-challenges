import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_l1Mac (pc : Nat) (t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n) (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions (l1Program t) (l1At pc s mem bi pa pb n i j pdst ret rest) =
      some (l1At (pc+38) s mem bi pa pb n i (j+1) pdst ret rest) := by
  have h := CiosCachedL1.run_step s (UInt256.ofNat pc) mem bi pa n j t ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa + 32*n - 32))
    (UInt256.ofNat (pb-32)) (isFour n) pdst ret rest hcap hact hn32 hj hpa hpaFit
  simpa only [CiosCachedL1.state, l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

theorem run_l1Last (t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hpos : 0 < n) (ht : t.toNat = 8256)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions (l1LastProgram t) (l1At 4872 s mem bi pa pb n i (n-1) pdst ret rest) =
      some (midState s (l1Step mem bi pa n n).memory (l1Step mem bi pa n n).carry bi
        pa pb n i pdst ret rest) := by
  have h := CiosCachedL1.run_last s (UInt256.ofNat 4872) mem bi pa n t ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa + 32*n - 32))
    (UInt256.ofNat (pb-32)) (isFour n) pdst ret rest hcap hact hn32 hpos hpa hpaFit
  have hpc : UInt256.ofNat 4872 + UInt256.ofNat 37 = UInt256.ofNat 4909 := by decide
  simpa only [CiosCachedL1.state, CiosCachedL1.doneState, l1At, midState, hpc] using h

theorem run_l2Mac (pc : Nat) (x tl ts : UInt256) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k+1 < n)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 8256 + 32 * (n - 2 - k))
    (hts : ts.toNat = 8256 + 32 * (n - 1 - k)) :
    runInstructions (l2Program x tl ts) (l2At pc s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At (pc+38) s mid bi mu c0 pa pb n i (k+1) pdst ret rest) := by
  have h := CiosCachedL2.run_step s (UInt256.ofNat pc) mid bi mu c0 n k x tl ts hx htl hts
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa + 32*n - 32))
    (UInt256.ofNat (pb-32)) (isFour n) pdst ret rest hcap hact hn32 hk
  simpa only [CiosCachedL2.state, l2At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
