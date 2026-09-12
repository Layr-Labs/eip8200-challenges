import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPayload

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionReturn
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open RecognitionSites RecognitionSelectorRaw RecognitionSelectorResult

def source (s : State) : UInt256 := selected (UInt256.ofNat 4819) s.executionEnv.calldata.size

def beforeCopy (s : State) (rho : List UInt256) : State :=
  atState s 4814 (12 :: source s :: 20 :: rho)

def afterCopy (s : State) (rho : List UInt256) : State :=
  sized (beforeCopy s rho) (source s) rho

def output (s : State) (rho : List UInt256) : State :=
  RecognitionSelectorRaw.returned (afterCopy s rho) (UInt256.ofNat 4816) rho

private theorem copy_decoded (s : State) (e : Env s) (rho : List UInt256) :
    (beforeCopy s rho).decodedOp = some .CODECOPY := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3917 .CODECOPY
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of (beforeCopy s rho) 3917
    e.code ?_ .CODECOPY none hd (by change Operation.CODECOPY.availableInFork s.fork = true; rw [e.fork]; rfl)
  change (UInt256.ofNat 4814).toNat = Artifact.submissionArtifact.instructionPC 3917
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem size_decoded (s : State) (e : Env s) (rho : List UInt256) :
    (copied (beforeCopy s rho) (source s) rho).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3918 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of
    (copied (beforeCopy s rho) (source s) rho) 3918 e.code ?_ .MSIZE none hd (by change Operation.MSIZE.availableInFork s.fork = true; rw [e.fork]; rfl)
  change (UInt256.ofNat 4815).toNat = Artifact.submissionArtifact.instructionPC 3918
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def gasSteps (s : State) (e : Env s) (rho : List UInt256)
    (hcap : rho.length ≤ 990) (hmem : s.memory = ByteArray.empty)
    (hactive : s.activeWords = 0) :
    GasSteps (atState s 4793 rho) (output s rho) := by
  have hp : StackRoundTrace.runInstrSeq RecognitionSites.selector.template
      (atState s 4793 rho) = some (beforeCopy s rho) := by
    have h := run_prefix s (UInt256.ofNat 4793) (UInt256.ofNat 4819) rho (by omega) e.run
    simpa only [RecognitionSites.selector.end_pc, beforeCopy, atState, source] using h
  have gp := RecognitionSites.selector.lift s (beforeCopy s rho) e rho hp
  have gc : GasSteps (beforeCopy s rho) (afterCopy s rho) :=
    gasSteps_copy_size (beforeCopy s rho) (source s) rho rfl hcap hmem hactive
      e.run e.np (copy_decoded s e rho) (size_decoded s e rho)
  have ea : Env (afterCopy s rho) := ⟨e.code, e.fork, e.run, e.np⟩
  have hf : StackRoundTrace.runInstrSeq RecognitionSites.returned.template
      (atState (afterCopy s rho) 4816 (32 :: rho)) = some (output s rho) :=
    run_finish (afterCopy s rho) (UInt256.ofNat 4816) rho (by omega) e.run
  have hpc : (UInt256.ofNat 4814).succ.succ = UInt256.ofNat 4816 := by decide
  have gf : GasSteps (afterCopy s rho) (output s rho) := by
    simpa only [afterCopy, beforeCopy, sized, copied, atState, hpc] using
      RecognitionSites.returned.lift (afterCopy s rho) (output s rho) ea (32 :: rho) hf
  exact gp.trans (gc.trans gf)

theorem output_halt (s : State) (rho : List UInt256) : (output s rho).halt = .Returned := rfl

theorem output_callStack (s : State) (rho : List UInt256) :
    (output s rho).callStack = s.callStack := rfl

theorem output_spec (s : State) (e : Env s) (rho : List UInt256)
    (hn : RecognitionAccumulator.Allowed s.executionEnv.calldata.size)
    (hz : RecognitionAccumulator.resultAcc s.executionEnv.calldata s.executionEnv.calldata.size = 0) :
    (output s rho).hReturn = spec s.executionEnv.calldata := by
  apply returned_spec (beforeCopy s rho) (source s) (UInt256.ofNat 4816) rho
    s.executionEnv.calldata.size hn rfl hz
  change MachineState.readPadded s.executionEnv.code (source s).toNat 20 = _
  rw [e.code]
  exact RecognitionPayload.read_selected _ hn

#print axioms gasSteps
#print axioms output_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionReturn
