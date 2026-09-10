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

theorem run_l1Mac (pc : Nat) (off t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n) (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions (l1Program off t) (l1At pc s mem bi pa pb n i j pdst ret rest) =
      some (l1At (pc+38) s mem bi pa pb n i (j+1) pdst ret rest) := by
  have h := CiosCachedL1.run_step s (UInt256.ofNat pc) mem bi pa n j off t hoff ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) (modulusAddress n) (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hj hpa hpaFit
  simpa only [List.cons_append, List.nil_append, CiosCachedL1.state, l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

theorem run_l1First (pc : Nat) (off t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hpos : 0 < n) (hoff : off.toNat = 32 * (n - 1))
    (ht : t.toNat = 8256 + 32 * (n - 1))
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions (l1FirstProgram off t) (l1At pc s mem bi pa pb n i 0 pdst ret rest) =
      some (l1At (pc+35) s mem bi pa pb n i 1 pdst ret rest) := by
  have h := CiosCachedL1.run_first s (UInt256.ofNat pc) mem bi pa n off t hoff ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) (modulusAddress n) (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hpos hpa hpaFit
  simpa only [List.cons_append, List.nil_append, CiosCachedL1.state, l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

theorem run_l1Last (t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hpos : 0 < n) (ht : t.toNat = 8256)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions (l1LastProgram t) (l1At 4814 s mem bi pa pb n i (n-1) pdst ret rest) =
      some (midState s (l1Step mem bi pa n n).memory (l1Step mem bi pa n n).carry bi
        pa pb n i pdst ret rest) := by
  have h := CiosCachedL1.run_last s (UInt256.ofNat 4814) mem bi pa n t ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) (modulusAddress n) (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hpos hpa hpaFit
  have hpc : UInt256.ofNat 4814 + UInt256.ofNat 35 = UInt256.ofNat 4849 := by decide
  simpa only [List.cons_append, List.nil_append, CiosCachedL1.state, CiosCachedL1.doneState, l1At, midState, hpc] using h

theorem run_l2Mac (pc : Nat) (w : Fin 33) (x tl ts : UInt256)
    (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k+1 < n)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 8256 + 32 * (n - 2 - k))
    (hts : ts.toNat = 8256 + 32 * (n - 1 - k))
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    runInstructions (l2Program w x tl ts) (l2At pc s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At (pc+(w.val+35)) s mid bi mu c0 pa pb n i (k+1) pdst ret rest) := by
  have h := CiosCachedL2.run_step w s (UInt256.ofNat pc) mid bi mu c0 n k x tl ts hx htl hts
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) (modulusAddress n) (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hk hpush
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, l2At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
