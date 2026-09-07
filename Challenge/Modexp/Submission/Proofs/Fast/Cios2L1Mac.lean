import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1First
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Second
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Third
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1FourthBody
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Fifth
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Sixth
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Seventh
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Eighth
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1FourthExit

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- Exact 4-MAC schedule, retaining the cached decrement slot. -/
def gasSteps_l1FourExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 4 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4171 s mem bi pa pb n i j pdst ret rest)
      (midState s (l1Step mem bi pa n (j + 4)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (j + 4)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (j + 4)))
        (l1Step mem bi pa n (j + 4)).carry bi pa pb n i pdst ret rest) :=
  (gasSteps_l1FirstMac s mem bi pa pb n i j pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1SecondMac s mem bi pa pb n i (j + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1ThirdMac s mem bi pa pb n i (j + 2) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1FourthMac s mem bi pa pb n i (j + 3) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_selectExit s mem bi pa pb n i (j + 4) pdst ret rest
      hcap hrun hcode hfork hnp hn32 (by omega) hpa hpaFit).trans <|
  gasSteps_join s mem bi pa pb n i (j + 4) pdst ret rest hcap hrun hcode hfork hnp

/-- Exact 8-MAC schedule, retaining the cached decrement slot. -/
def gasSteps_l1EightExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 8 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4171 s mem bi pa pb n i j pdst ret rest)
      (midState s (l1Step mem bi pa n (j + 8)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (j + 8)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (j + 8)))
        (l1Step mem bi pa n (j + 8)).carry bi pa pb n i pdst ret rest) :=
  (gasSteps_l1FirstMac s mem bi pa pb n i j pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1SecondMac s mem bi pa pb n i (j + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1ThirdMac s mem bi pa pb n i (j + 2) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1FourthMac s mem bi pa pb n i (j + 3) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_selectContinue s mem bi pa pb n i (j + 4) pdst ret rest
      hcap hrun hcode hfork hnp hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1FifthMac s mem bi pa pb n i (j + 4) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1SixthMac s mem bi pa pb n i (j + 5) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1SeventhMac s mem bi pa pb n i (j + 6) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1EighthMac s mem bi pa pb n i (j + 7) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit).trans <|
  gasSteps_join s mem bi pa pb n i (j + 8) pdst ret rest hcap hrun hcode hfork hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
