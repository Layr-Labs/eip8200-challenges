import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2First
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Second
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Third
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Fourth
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Fifth
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Sixth
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Select

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid

/-- Exact 2-MAC remainder schedule after the peeled L2 limb. -/
def gasSteps_pairExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 3 = n) :
    Challenge.EvmProof.GasSteps
      (l2At 4905 s mid bi mu c0 pa pb n i k pdst ret rest)
      (tailState s (l2Step mid mu c0 n (k + 2)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 2)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 2)))
        (l2Step mid mu c0 n (k + 2)).carry mu bi pa pb n i pdst ret rest) :=
  (gasSteps_first s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_second s mid bi mu c0 pa pb n i (k + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_selectExit s mid bi mu c0 pa pb n i (k + 2) pdst ret rest
      hcap hrun hcode hfork hnp hn32 (by omega)).trans <|
  gasSteps_join s mid bi mu c0 pa pb n i (k + 2) pdst ret rest hcap hrun hcode hfork hnp

/-- Exact 6-MAC remainder schedule after the peeled L2 limb. -/
def gasSteps_sixExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 7 = n) :
    Challenge.EvmProof.GasSteps
      (l2At 4905 s mid bi mu c0 pa pb n i k pdst ret rest)
      (tailState s (l2Step mid mu c0 n (k + 6)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 6)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 6)))
        (l2Step mid mu c0 n (k + 6)).carry mu bi pa pb n i pdst ret rest) :=
  (gasSteps_first s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_second s mid bi mu c0 pa pb n i (k + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_selectContinue s mid bi mu c0 pa pb n i (k + 2) pdst ret rest
      hcap hrun hcode hfork hnp hn32 (by omega)).trans <|
  (gasSteps_third s mid bi mu c0 pa pb n i (k + 2) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_fourth s mid bi mu c0 pa pb n i (k + 3) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_fifth s mid bi mu c0 pa pb n i (k + 4) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  (gasSteps_sixth s mid bi mu c0 pa pb n i (k + 5) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega)).trans <|
  gasSteps_join s mid bi mu c0 pa pb n i (k + 6) pdst ret rest hcap hrun hcode hfork hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
