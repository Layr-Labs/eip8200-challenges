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


/- Superseded standalone Maj composition. -/
/-
theorem t2_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_t2 s msgOff returnDest rest j hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.afterT1 s msgOff returnDest rest j).activeWords.toNat =
      165 + MachineState.memCost
        (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat := by
  have hsetupH2 := blockCost_potential_of_static Compression.setupT2H2Path 20
    (Compression.run_setupT2H2 s msgOff returnDest rest j (by omega)
      hrun)
    (by simpa [Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupT2H2Path, CopyFree]) (by rfl)
  have hsetupH1 := blockCost_potential_of_static Compression.setupT2H1Path 6
    (Compression.run_setupT2H1 s msgOff returnDest rest j (by omega)
      hrun)
    (by simpa [Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupT2H1Path, CopyFree]) (by rfl)
  have hsetupMaj := blockCost_potential_of_static Compression.setupMajPath 14
    (Compression.run_setupMaj s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupMajPath, CopyFree]) (by rfl)
  have hmaj := ArithmeticGas.gasSteps_maj_cost_potential
    (Compression.gotT2H1 s msgOff returnDest rest j)
    (Compression.hValue s 0) (Compression.hValue s 1)
    (Compression.hValue s 2) 0 (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, Compression.hValue s 0, Compression.t1 s j,
      Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupB0 := blockCost_potential_of_static
    Compression.setupBigSigma0Path 15
    (Compression.run_setupBigSigma0 s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupBigSigma0Path, CopyFree]) (by rfl)
  have hb0 := ArithmeticGas.gasSteps_bigSigma0_cost_potential
    (Compression.gotMaj s msgOff returnDest rest j) (Compression.hValue s 0)
    (Word.evmMaj (Compression.hValue s 0) (Compression.hValue s 1)
      (Compression.hValue s 2))
    ([Compression.hValue s 0, Compression.t1 s j, Compression.hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hnp)
  have hawMaj :
      (Compression.callMaj s msgOff returnDest rest j).activeWords =
        (Compression.gotT2H1 s msgOff returnDest rest j).activeWords := by rfl
  have hawB0 :
      (Compression.callBigSigma0 s msgOff returnDest rest j).activeWords =
        (Compression.gotMaj s msgOff returnDest rest j).activeWords := by rfl
  simp only [Compression.gasSteps_t2,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, id_eq]
  rw [hawMaj] at hsetupMaj
  rw [hawB0] at hsetupB0
  change _ = 50 + MachineState.memCost
    (Compression.gotMaj s msgOff returnDest rest j).activeWords.toNat at hmaj
  change _ = 60 + MachineState.memCost
    (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat at hb0
  omega
-/

theorem t2_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_t2 s msgOff returnDest rest j hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.afterT1 s msgOff returnDest rest j).activeWords.toNat =
      135 + MachineState.memCost
        (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat := by
  have hsetupT2 := blockCost_potential_of_static Compression.setupT2Path 36
    (Compression.run_setupT2 s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.afterT1, Compression.gotIntegratedT1,
      BigSigma.t1Returned, Compression.loadedT1Inputs, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.kAtReturned,
      Accessors.loadReturned, State.fork] using hfork)
    (by simp [Compression.setupT2Path, CopyFree]) (by rfl)
  have hb0 := ArithmeticGas.gasSteps_bigSigma0_cost_potential
    (Compression.loadedT2Inputs s msgOff returnDest rest j)
    (Compression.hValue s 0) (Compression.hValue s 1) (Compression.hValue s 2)
    ([Compression.hValue s 0, Compression.t1 s j, Compression.hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.loadedT2Inputs, Compression.afterT1,
      Compression.gotIntegratedT1, BigSigma.t1Returned,
      Compression.loadedT1Inputs, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.kAtReturned, Accessors.loadReturned]
      using hcode)
    (by simpa [Compression.loadedT2Inputs, Compression.afterT1,
      Compression.gotIntegratedT1, BigSigma.t1Returned,
      Compression.loadedT1Inputs, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.kAtReturned, Accessors.loadReturned,
      State.fork] using hfork)
    (by simpa [Compression.loadedT2Inputs, Compression.afterT1,
      Compression.gotIntegratedT1, BigSigma.t1Returned,
      Compression.loadedT1Inputs, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.kAtReturned, Accessors.loadReturned]
      using hrun)
    (by simpa [Compression.loadedT2Inputs, Compression.afterT1,
      Compression.gotIntegratedT1, BigSigma.t1Returned,
      Compression.loadedT1Inputs, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.kAtReturned, Accessors.loadReturned]
      using hnp)
  have haw :
      (Compression.callIntegratedT2 s msgOff returnDest rest j).activeWords =
        (Compression.loadedT2Inputs s msgOff returnDest rest j).activeWords := by
    rfl
  simp only [Compression.gasSteps_t2,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, id_eq]
  rw [haw] at hsetupT2
  change _ = 99 + MachineState.memCost
    (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat at hb0
  omega


end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas
