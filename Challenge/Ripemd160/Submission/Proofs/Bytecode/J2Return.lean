import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2ReturnSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Payload

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Return
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open J2Sites J2Moves RecognitionSelectorRaw RecognitionSelectorResult

def source (s : State) : UInt256 :=
  selected (UInt256.ofNat s.executionEnv.code.size) s.executionEnv.calldata.size

def beforeCopy (s : State) (rho : List UInt256) : State :=
  atState s 4945 (12 :: source s :: 20 :: rho)

def afterCopy (s : State) (rho : List UInt256) : State :=
  sized (beforeCopy s rho) (source s) rho

def output (s : State) (rho : List UInt256) : State :=
  RecognitionSelectorRaw.returned (afterCopy s rho) (UInt256.ofNat 4947) rho

private theorem pc_3606 : Artifact.submissionArtifact.instructionPC 3599 = 4945 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private theorem pc_3607 : Artifact.submissionArtifact.instructionPC 3600 = 4946 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private theorem beforeCopy_pc (s : State) (rho : List UInt256) :
    (beforeCopy s rho).pc.toNat = 4945 := by
  change (UInt256.ofNat 4945).toNat = 4945; decide

private theorem copied_pc (s : State) (rho : List UInt256) :
    (copied (beforeCopy s rho) (source s) rho).pc.toNat = 4946 := by
  change (UInt256.ofNat 4945).succ.toNat = 4946; decide

private theorem copy_decoded (s : State) (e : Env s) (rho : List UInt256) :
    (beforeCopy s rho).decodedOp = some .CODECOPY := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3599 .CODECOPY
    (by rfl) (by decide) trivial
  exact Artifact.submissionArtifact.state_decodedOp_of (beforeCopy s rho) 3599
    e.code ((beforeCopy_pc s rho).trans pc_3606.symm) .CODECOPY none hd
    (by change Operation.CODECOPY.availableInFork s.fork = true; rw [e.fork]; rfl)

private theorem size_decoded (s : State) (e : Env s) (rho : List UInt256) :
    (copied (beforeCopy s rho) (source s) rho).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3600 .MSIZE
    (by rfl) (by decide) trivial
  exact Artifact.submissionArtifact.state_decodedOp_of
    (copied (beforeCopy s rho) (source s) rho) 3600 e.code
    ((copied_pc s rho).trans pc_3607.symm) .MSIZE none hd
    (by change Operation.MSIZE.availableInFork s.fork = true; rw [e.fork]; rfl)

def gasSteps (s : State) (e : Env s) (rho : List UInt256)
    (hcap : rho.length ≤ 990) (hmem : s.memory = ByteArray.empty)
    (hactive : s.activeWords = 0) :
    GasSteps (atState s 4928 rho) (output s rho) := by
  have hp : StackRoundTrace.runInstrSeq J2ReturnSites.selector.template
      (atState s 4928 rho) = some (beforeCopy s rho) := by
    have h := run_prefix s (UInt256.ofNat 4928) rho (by omega) e.run
    simpa only [J2ReturnSites.selector.end_pc, beforeCopy, atState, source] using h
  have gp := J2ReturnSites.selector.lift s (beforeCopy s rho) e rho hp
  have gc : GasSteps (beforeCopy s rho) (afterCopy s rho) :=
    gasSteps_copy_size (beforeCopy s rho) (source s) rho rfl hcap hmem hactive
      e.run e.np (copy_decoded s e rho) (size_decoded s e rho)
  have ea : Env (afterCopy s rho) := ⟨e.code, e.fork, e.run, e.np⟩
  have hf : StackRoundTrace.runInstrSeq J2ReturnSites.returned.template
      (atState (afterCopy s rho) 4947 (32 :: rho)) = some (output s rho) :=
    run_finish (afterCopy s rho) (UInt256.ofNat 4947) rho (by omega) e.run
  have hpc : (UInt256.ofNat 4945).succ.succ = UInt256.ofNat 4947 := by decide
  have gf : GasSteps (afterCopy s rho) (output s rho) := by
    simpa only [afterCopy, beforeCopy, sized, copied, atState, hpc] using
      J2ReturnSites.returned.lift (afterCopy s rho) (output s rho) ea (32 :: rho) hf
  exact gp.trans (gc.trans gf)

theorem output_halt (s : State) (rho : List UInt256) : (output s rho).halt = .Returned := rfl

theorem output_callStack (s : State) (rho : List UInt256) :
    (output s rho).callStack = s.callStack := rfl

theorem output_spec (s : State) (e : Env s) (rho : List UInt256)
    (hn : RecognitionAccumulator.Allowed s.executionEnv.calldata.size)
    (hz : J2Accumulator.resultAcc s.executionEnv.calldata s.executionEnv.calldata.size = 0) :
    (output s rho).hReturn = spec s.executionEnv.calldata := by
  apply returned_spec (beforeCopy s rho) (source s) (UInt256.ofNat 4947) rho
    s.executionEnv.calldata.size hn rfl
      ((RecognitionAccumulator.resultAcc_zero_iff _ _ hn rfl).mpr
        ((J2Accumulator.resultAcc_zero_iff _ _ hn rfl).mp hz))
  change MachineState.readPadded s.executionEnv.code (source s).toNat 20 = _
  have hsz : s.executionEnv.code.size = 5247 :=
    (congrArg ByteArray.size e.code).trans referenceBytecode_size
  have hsrc : (source s).toNat = (selected (UInt256.ofNat 5247) s.executionEnv.calldata.size).toNat := by
    rw [source, hsz]
  have hread : ∀ (c : ByteArray) (st : Nat),
      c = submissionBytecode →
      st = (selected (UInt256.ofNat 5247) s.executionEnv.calldata.size).toNat →
      MachineState.readPadded c st 20 =
        MachineState.readPadded RecognitionDigest.payload (280 - 20 * ((14357627 / s.executionEnv.calldata.size) % 16)) 20 := by
    intro c st hc hst
    subst hc hst
    exact J2Payload.read_selected _ hn
  exact hread s.executionEnv.code (source s).toNat e.code hsrc

#print axioms gasSteps
#print axioms output_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Return
