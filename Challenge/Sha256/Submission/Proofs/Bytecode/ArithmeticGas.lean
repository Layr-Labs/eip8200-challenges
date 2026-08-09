import Challenge.EvmProof.Meter
import Challenge.Sha256.Submission.Proofs.Bytecode.BigSigma

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ArithmeticGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem instrCostWithoutMemory_eq_static (instruction : Instr) (s : State)
    (hfork : s.fork = .Osaka) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      Challenge.EvmProof.Meter.instrStaticCost .Osaka instruction := by
  cases instruction with
  | push width value => simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | CompBit op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Keccak op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Dup op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Swap op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | DupN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | SwapN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Exchange op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Log op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | System op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]

private theorem block_cost_potential
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  apply Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    path hresult hfork
  intro located hmem q hq
  exact instrCostWithoutMemory_eq_static located.instruction q hq
    (hfree located hmem)

private theorem block_cost_of_activeWords_eq
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hwords : t.activeWords = s.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path := by
  have hpotential := block_cost_potential path hresult hfork hfree
  rw [hwords] at hpotential
  omega

/- Standalone Ch/Maj helpers are dead in the integrated kernel. -/
/-
private theorem ch_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.chPath = 44 := by
  rfl

theorem gasSteps_ch_cost_potential (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ch s x y z output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      44 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmCh x y z) returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_ch s x y z output returnDest rest hcap hcode
    hrun hvalid
  have hmeter := block_cost_potential Functions.chPath hresult hfork
    (by simp [Functions.chPath, CopyFree])
  rw [ch_static] at hmeter
  unfold Functions.gasSteps_ch
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.ternaryEntry] using hmeter
-/

/-
private theorem maj_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.majPath = 50 := by
  rfl

theorem gasSteps_maj_cost_potential (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Functions.gasSteps_maj s x y z output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      50 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmMaj x y z) returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_maj s x y z output returnDest rest hcap hcode
    hrun hvalid
  have hmeter := block_cost_potential Functions.majPath hresult hfork
    (by simp [Functions.majPath, CopyFree])
  rw [maj_static] at hmeter
  unfold Functions.gasSteps_maj
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.ternaryEntry] using hmeter
-/

/-
private theorem ssig0_setup_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0SetupPath = 32 := by
  rfl

private theorem ssig0_middle_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0MiddlePath = 23 := by
  rfl

private theorem ssig0_finish_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0FinishPath = 25 := by
  rfl

theorem gasSteps_ssig0_cost_potential (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ssig0 s x output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      176 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmSmallSigma0 x) returnDest rest).activeWords.toNat := by
  have setupResult := Functions.run_ssig0Setup s x output returnDest rest
    (by omega) hcode hrun
  have setupCost := block_cost_of_activeWords_eq Functions.ssig0SetupPath
    setupResult hfork (by simp [Functions.ssig0SetupPath, CopyFree]) (by rfl)
  rw [ssig0_setup_static] at setupCost
  have firstCost := gasSteps_rotr_cost s x 18 0 (UInt256.ofNat 48)
    (UInt256.shiftRight x (UInt256.ofNat 3) :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have middleResult := Functions.run_ssig0Middle s x output returnDest rest
    (by omega) hcode hrun
  have middleCost := block_cost_of_activeWords_eq Functions.ssig0MiddlePath
    middleResult hfork (by simp [Functions.ssig0MiddlePath, CopyFree]) (by rfl)
  rw [ssig0_middle_static] at middleCost
  have secondCost := gasSteps_rotr_cost s x 7 0 (UInt256.ofNat 60)
    (Word.evmRotr32 x 18 :: UInt256.shiftRight x (UInt256.ofNat 3) ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have finishResult := Functions.run_ssig0Finish s x output returnDest rest
    (by omega) hcode hrun hvalid
  have finishCost := block_cost_of_activeWords_eq Functions.ssig0FinishPath
    finishResult hfork (by simp [Functions.ssig0FinishPath, CopyFree]) (by rfl)
  rw [ssig0_finish_static] at finishCost
  unfold Functions.gasSteps_ssig0
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [Functions.unaryReturned] at ⊢
  omega

private theorem ssig1_setup_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1SetupPath = 32 := by
  rfl

private theorem ssig1_middle_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1MiddlePath = 23 := by
  rfl

private theorem ssig1_finish_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1FinishPath = 25 := by
  rfl

theorem gasSteps_ssig1_cost_potential (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ssig1 s x output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      176 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmSmallSigma1 x) returnDest rest).activeWords.toNat := by
  have setupResult := Functions.run_ssig1Setup s x output returnDest rest
    (by omega) hcode hrun
  have setupCost := block_cost_of_activeWords_eq Functions.ssig1SetupPath
    setupResult hfork (by simp [Functions.ssig1SetupPath, CopyFree]) (by rfl)
  rw [ssig1_setup_static] at setupCost
  have firstCost := gasSteps_rotr_cost s x 19 0 (UInt256.ofNat 89)
    (UInt256.shiftRight x (UInt256.ofNat 10) :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have middleResult := Functions.run_ssig1Middle s x output returnDest rest
    (by omega) hcode hrun
  have middleCost := block_cost_of_activeWords_eq Functions.ssig1MiddlePath
    middleResult hfork (by simp [Functions.ssig1MiddlePath, CopyFree]) (by rfl)
  rw [ssig1_middle_static] at middleCost
  have secondCost := gasSteps_rotr_cost s x 17 0 (UInt256.ofNat 101)
    (Word.evmRotr32 x 19 :: UInt256.shiftRight x (UInt256.ofNat 10) ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have finishResult := Functions.run_ssig1Finish s x output returnDest rest
    (by omega) hcode hrun hvalid
  have finishCost := block_cost_of_activeWords_eq Functions.ssig1FinishPath
    finishResult hfork (by simp [Functions.ssig1FinishPath, CopyFree]) (by rfl)
  rw [ssig1_finish_static] at finishCost
  unfold Functions.gasSteps_ssig1
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [Functions.unaryReturned] at ⊢
  omega
-/

private theorem ssig0_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0Path = 57 := by
  rfl

theorem gasSteps_ssig0_cost_potential (s : State) (x returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ssig0 s x returnDest rest (by omega) hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      57 + MachineState.memCost
        (Functions.unaryReturned s (Word.rawFusedSmallSigma0 x) returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_ssig0 s x returnDest rest (by omega) hcode
    hrun hvalid
  have hmeter := block_cost_potential Functions.ssig0Path hresult hfork
    (by simp [Functions.ssig0Path, CopyFree])
  rw [ssig0_static] at hmeter
  unfold Functions.gasSteps_ssig0
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.smallSigmaEntry] using hmeter

private theorem ssig1_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1Path = 57 := by
  rfl

theorem gasSteps_ssig1_cost_potential (s : State) (x returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ssig1 s x returnDest rest (by omega) hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      57 + MachineState.memCost
        (Functions.unaryReturned s (Word.rawFusedSmallSigma1 x) returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_ssig1 s x returnDest rest (by omega) hcode
    hrun hvalid
  have hmeter := block_cost_potential Functions.ssig1Path hresult hfork
    (by simp [Functions.ssig1Path, CopyFree])
  rw [ssig1_static] at hmeter
  unfold Functions.gasSteps_ssig1
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.smallSigmaEntry] using hmeter

private theorem bigSigma0_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma0Path = 99 := by
  rfl

theorem gasSteps_bigSigma0_cost_potential (s : State)
    (x y z : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (BigSigma.gasSteps_bigSigma0 s x y z rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      99 + MachineState.memCost
        (BigSigma.t2Returned s x y z rest).activeWords.toNat := by
  have hresult := BigSigma.run_bigSigma0 s x y z rest hcap hcode hrun
  have hmeter := block_cost_potential BigSigma.bigSigma0Path hresult hfork
    (by simp [BigSigma.bigSigma0Path, CopyFree])
  rw [bigSigma0_static] at hmeter
  unfold BigSigma.gasSteps_bigSigma0
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [BigSigma.t2Entry] using hmeter

private theorem bigSigma1_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma1Path = 108 := by
  rfl

theorem gasSteps_bigSigma1_cost_potential (s : State)
    (x y z addend1 addend2 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (BigSigma.gasSteps_bigSigma1 s x y z addend1 addend2 rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      108 + MachineState.memCost
        (BigSigma.t1Returned s x y z addend1 addend2 rest).activeWords.toNat := by
  have hresult := BigSigma.run_bigSigma1 s x y z addend1 addend2 rest hcap hcode hrun
  have hmeter := block_cost_potential BigSigma.bigSigma1Path hresult hfork
    (by simp [BigSigma.bigSigma1Path, CopyFree])
  rw [bigSigma1_static] at hmeter
  unfold BigSigma.gasSteps_bigSigma1
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [BigSigma.t1Entry] using hmeter

end Challenge.Sha256.Submission.Proofs.Bytecode.ArithmeticGas
