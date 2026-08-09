import Challenge.Sha256.Submission.Proofs.Bytecode.ArithmeticGas
import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGasBase
import Challenge.Sha256.Submission.Proofs.Bytecode.PairCompositionTest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Sha256.Submission.Proofs.Bytecode

theorem pairIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj : j + 2 ≤ 64) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (PairCompositionTest.gasStepsPair s msgOff returnDest rest j hj hcap
      hcode hfork hrun hnp).cost + MachineState.memCost
        (Compression.pairAt s msgOff returnDest rest j).activeWords.toNat =
      868 + MachineState.memCost
        (Compression.afterPair s msgOff returnDest rest j).activeWords.toNat := by
  have hj64 : j < 64 := by omega
  have hj1 : j + 1 < 64 := by omega
  have hcond := blockCost_potential_of_static Compression.pairConditionPath 23
    (Compression.run_pairCondition s msgOff returnDest rest j hj64 (by omega)
      hrun)
    (by simpa [Compression.pairAt, State.fork] using hfork)
    (by simp [Compression.pairConditionPath, CopyFree]) (by rfl)
  have hsetup10 := blockCost_potential_of_static
    Compression.pairFirstSetupPath 111
    (PairSegmentTest.runFirstSetup s msgOff returnDest rest j hj64 (by omega)
      hcode hrun)
    (by simpa [Compression.afterPairCondition, Compression.pairAt, State.fork]
      using hfork)
    (by simp [Compression.pairFirstSetupPath, CopyFree]) (by rfl)
  have ht10 := ArithmeticGas.gasSteps_bigSigma1_cost_potential
    (Compression.firstPairInputsLoaded s msgOff returnDest rest j)
    (Compression.hValue s 4) (Compression.hValue s 5)
    (Compression.hValue s 6)
    (Compression.hValue s 7 + Compression.kValue s j)
    (Compression.wValue s j) (UInt256.ofNat 717)
    ([Compression.kValue s j, Compression.wValue s j,
      Compression.hValue s 0, Compression.hValue s 4,
      Compression.hValue s 5, Compression.hValue s 6,
      Compression.hValue s 7, Compression.hValue s 1,
      Compression.hValue s 2, Compression.hValue s 3,
      Compression.pairWPtr j, Compression.pairKPtr j,
      msgOff, returnDest] ++ rest)
    (by simp; omega) hcode
    (by simpa [Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt, State.fork]
      using hfork)
    (by simpa [Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt] using hrun)
    (by simpa [Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt] using hnp)
    (by decide)
  have hsetup20 := blockCost_potential_of_static
    Compression.pairFirstT2SetupPath 37
    (PairSegmentTest.runFirstT2Setup s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t1Returned, State.fork] using hfork)
    (by simp [Compression.pairFirstT2SetupPath, CopyFree]) (by rfl)
  have ht20 := ArithmeticGas.gasSteps_bigSigma0_cost_potential
    (Compression.afterPairT10 s msgOff returnDest rest j)
    (Compression.hValue s 0) (Compression.hValue s 1)
    (Compression.hValue s 2) (UInt256.ofNat 737)
    ([Compression.t10 s j, Compression.hValue s 0,
      Compression.hValue s 4, Compression.hValue s 5,
      Compression.hValue s 6, Compression.hValue s 7,
      Compression.hValue s 1, Compression.hValue s 2,
      Compression.hValue s 3, Compression.pairWPtr j,
      Compression.pairKPtr j, msgOff, returnDest] ++ rest)
    (by simp; omega) hcode
    (by simpa [Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t1Returned, State.fork] using hfork)
    (by simpa [Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t1Returned] using hrun)
    (by simpa [Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t1Returned] using hnp)
    (by decide)
  have hsetup11 := blockCost_potential_of_static
    Compression.pairSecondT1SetupPath 106
    (PairSegmentTest.runSecondT1Setup s msgOff returnDest rest j hj1
      (by omega) hcode hrun)
    (by simpa [Compression.afterPairT20, Compression.afterPairT10,
      Compression.firstPairInputsLoaded, Compression.afterPairCondition,
      Compression.pairAt, BigSigma.t2Returned, BigSigma.t1Returned,
      State.fork] using hfork)
    (by simp [Compression.pairSecondT1SetupPath, CopyFree]) (by rfl)
  have ht11 := ArithmeticGas.gasSteps_bigSigma1_cost_potential
    (Compression.secondPairInputsLoaded s msgOff returnDest rest j)
    (Compression.pairE1 s j) (Compression.hValue s 4)
    (Compression.hValue s 5)
    (Compression.hValue s 6 + Compression.kValue s (j + 1))
    (Compression.wValue s (j + 1)) (UInt256.ofNat 805)
    ([Compression.kValue s (j + 1), Compression.wValue s (j + 1),
      Compression.pairA1 s j, Compression.pairE1 s j,
      Compression.hValue s 0, Compression.hValue s 4,
      Compression.hValue s 5, Compression.hValue s 6,
      Compression.hValue s 7, Compression.hValue s 1,
      Compression.hValue s 2, Compression.hValue s 3,
      Compression.pairWPtr j, Compression.pairKPtr j,
      msgOff, returnDest] ++ rest)
    (by simp; omega) hcode
    (by simpa [Compression.secondPairInputsLoaded, Compression.afterPairT20,
      Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t2Returned, BigSigma.t1Returned, State.fork] using hfork)
    (by simpa [Compression.secondPairInputsLoaded, Compression.afterPairT20,
      Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t2Returned, BigSigma.t1Returned] using hrun)
    (by simpa [Compression.secondPairInputsLoaded, Compression.afterPairT20,
      Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t2Returned, BigSigma.t1Returned] using hnp)
    (by decide)
  have hsetup21 := blockCost_potential_of_static
    Compression.pairSecondT2SetupPath 37
    (PairSegmentTest.runSecondT2Setup s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.afterPairT11, Compression.secondPairInputsLoaded,
      Compression.afterPairT20, Compression.afterPairT10,
      Compression.firstPairInputsLoaded, Compression.afterPairCondition,
      Compression.pairAt, BigSigma.t2Returned, BigSigma.t1Returned,
      State.fork] using hfork)
    (by simp [Compression.pairSecondT2SetupPath, CopyFree]) (by rfl)
  have ht21 := ArithmeticGas.gasSteps_bigSigma0_cost_potential
    (Compression.afterPairT11 s msgOff returnDest rest j)
    (Compression.pairA1 s j) (Compression.hValue s 0)
    (Compression.hValue s 1) (UInt256.ofNat 825)
    ([Compression.t11 s j, Compression.pairA1 s j,
      Compression.pairE1 s j, Compression.hValue s 0,
      Compression.hValue s 4, Compression.hValue s 5,
      Compression.hValue s 6, Compression.hValue s 7,
      Compression.hValue s 1, Compression.hValue s 2,
      Compression.hValue s 3, Compression.pairWPtr j,
      Compression.pairKPtr j, msgOff, returnDest] ++ rest)
    (by simp; omega) hcode
    (by simpa [Compression.afterPairT11, Compression.secondPairInputsLoaded,
      Compression.afterPairT20, Compression.afterPairT10,
      Compression.firstPairInputsLoaded, Compression.afterPairCondition,
      Compression.pairAt, BigSigma.t2Returned, BigSigma.t1Returned,
      State.fork] using hfork)
    (by simpa [Compression.afterPairT11, Compression.secondPairInputsLoaded,
      Compression.afterPairT20, Compression.afterPairT10,
      Compression.firstPairInputsLoaded, Compression.afterPairCondition,
      Compression.pairAt, BigSigma.t2Returned,
      BigSigma.t1Returned] using hrun)
    (by simpa [Compression.afterPairT11, Compression.secondPairInputsLoaded,
      Compression.afterPairT20, Compression.afterPairT10,
      Compression.firstPairInputsLoaded, Compression.afterPairCondition,
      Compression.pairAt, BigSigma.t2Returned,
      BigSigma.t1Returned] using hnp)
    (by decide)
  have hcommit := blockCost_potential_of_static Compression.pairCommitPath 158
    (PairSegmentTest.runCommit s msgOff returnDest rest j (by omega)
      (by omega) hcode hrun)
    (by simpa [Compression.afterPairT21, Compression.afterPairT11,
      Compression.secondPairInputsLoaded, Compression.afterPairT20,
      Compression.afterPairT10, Compression.firstPairInputsLoaded,
      Compression.afterPairCondition, Compression.pairAt,
      BigSigma.t2Returned, BigSigma.t1Returned, State.fork] using hfork)
    (by simp [Compression.pairCommitPath, CopyFree]) (by rfl)
  simp only [BigSigma.gasSteps_bigSigma0, BigSigma.gasSteps_bigSigma1,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost] at ht10 ht20 ht11 ht21
  change (_ + (_ + (_ + (_ + (_ + (_ + (_ + (_ + (_ + _))))))))) +
      MachineState.memCost
        (Compression.pairAt s msgOff returnDest rest j).activeWords.toNat =
    868 + MachineState.memCost
      (Compression.afterPair s msgOff returnDest rest j).activeWords.toNat
  omega

theorem roundLoop_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_roundLoop s msgOff returnDest rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.roundLoopState s msgOff returnDest rest 0).activeWords.toNat =
      32 * 868 + MachineState.memCost
        (Compression.roundLoopState s msgOff returnDest rest 64).activeWords.toNat := by
  unfold Compression.gasSteps_roundLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add 32 868
  intro n hn
  let q := PairCompositionTest.pairLoopState s msgOff returnDest rest n
  have qcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have h := pairIteration_cost_potential q msgOff returnDest rest (2 * n)
    (by omega) hcap qcode qfork qrun qnp
  dsimp only [q] at h
  have h' :
      (PairCompositionTest.gasStepsPair
        (PairCompositionTest.pairLoopState s msgOff returnDest rest n)
        msgOff returnDest rest (2 * n) (by omega) hcap qcode qfork qrun qnp).cost +
          MachineState.memCost
            (PairCompositionTest.pairLoopState s msgOff returnDest rest n).activeWords.toNat =
        868 + MachineState.memCost
          (PairCompositionTest.pairLoopState s msgOff returnDest rest (n + 1)).activeWords.toNat := by
    simpa [Compression.pairAt, PairCompositionTest.pairLoopState] using h
  simpa only [Challenge.EvmProof.GasSteps.cast_cost] using h'

end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas
