import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGasBase
import Challenge.Sha256.Submission.Proofs.Bytecode.ArithmeticGas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler


theorem t1_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_t1 s msgOff returnDest rest j hj hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.roundAt s msgOff returnDest rest j).activeWords.toNat =
      260 + MachineState.memCost
        (Compression.afterT1 s msgOff returnDest rest j).activeWords.toNat := by
  have hcond := blockCost_potential_of_static Compression.conditionPath 26
    (Compression.run_condition s msgOff returnDest rest j hj (by omega) hrun)
    (by simpa [Compression.roundAt, State.fork] using hfork)
    (by simp [Compression.conditionPath, CopyFree]) (by rfl)
  have hsetupW := blockCost_potential_of_static Compression.setupWPath 27
    (Compression.run_setupW s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Compression.afterCondition, State.fork] using hfork)
    (by simp [Compression.setupWPath, CopyFree]) (by rfl)
  have hsetupK := blockCost_potential_of_static Compression.setupKPath 24
    (Compression.run_setupK s msgOff returnDest rest j hj (by omega) hrun)
    (by simpa [Compression.gotW, Compression.loadedE,
      Accessors.loadReturned, State.fork] using hfork)
    (by simp [Compression.setupKPath, CopyFree]) (by rfl)
  have hsetupH6 := blockCost_potential_of_static Compression.setupH6Path 17
    (Compression.run_setupH6 s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Compression.gotK, Compression.gotW, Compression.loadedE,
      Accessors.kAtReturned, Accessors.loadReturned, State.fork] using hfork)
    (by simp [Compression.setupH6Path, CopyFree]) (by rfl)
  have hsetupH5 := blockCost_potential_of_static Compression.setupH5Path 12
    (Compression.run_setupH5 s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.loadReturned, Accessors.kAtReturned,
      State.fork] using hfork)
    (by simp [Compression.setupH5Path, CopyFree]) (by rfl)
  have hsetupCh := blockCost_potential_of_static Compression.setupChPath 15
    (Compression.run_setupCh s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupChPath, CopyFree]) (by rfl)
  have hch := ArithmeticGas.gasSteps_ch_cost_potential
    (Compression.gotH5 s msgOff returnDest rest j) (Compression.hValue s 4)
    (Compression.hValue s 5) (Compression.hValue s 6) 0 (UInt256.ofNat 703)
    ([Compression.kValue s j, Compression.wValue s j,
      UInt256.ofNat 0xffffffff, Compression.hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupB1 := blockCost_potential_of_static
    Compression.setupBigSigma1Path 18
    (Compression.run_setupBigSigma1 s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupBigSigma1Path, CopyFree]) (by rfl)
  have hb1 := ArithmeticGas.gasSteps_bigSigma1_cost_potential
    (Compression.gotCh s msgOff returnDest rest j) (Compression.hValue s 4)
    (Compression.chPlusK s j) (Compression.wValue s j)
    ([Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp)
  have hfinish := blockCost_potential_of_static Compression.finishT1Path 5
    (Compression.run_finishT1 s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Compression.gotFusedT1, BigSigma.t1Returned,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.finishT1Path, CopyFree]) (by rfl)
  have hawCh :
      (Compression.callCh s msgOff returnDest rest j).activeWords =
        (Compression.gotH5 s msgOff returnDest rest j).activeWords := by rfl
  have hawB1 :
      (Compression.callBigSigma1 s msgOff returnDest rest j).activeWords =
        (Compression.gotCh s msgOff returnDest rest j).activeWords := by rfl
  simp only [Compression.gasSteps_t1, Compression.gasSteps_condition,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [hawCh] at hsetupCh
  rw [hawB1] at hsetupB1
  change _ = 44 + MachineState.memCost
    (Compression.gotCh s msgOff returnDest rest j).activeWords.toNat at hch
  change _ = 72 + MachineState.memCost
    (Compression.gotFusedT1 s msgOff returnDest rest j).activeWords.toNat at hb1
  omega


end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas
