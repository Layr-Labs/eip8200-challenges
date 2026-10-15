import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdAlignedBlock
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

/-- The loop-head marker is separate from the endian body, so callers may
enter at 461 without pretending the body itself begins there. -/
def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 179).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 179 join_slice
    (by change 179 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide)) (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 461 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 179) = UInt256.ofNat 461
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_join (s : State) (stack : List UInt256) (hstack : stack.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 461, stack := stack}
      {s with pc := UInt256.ofNat 462, stack := stack} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 461, stack := stack} _
    hcode hfork hrun hnp join_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · simp [joinTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    decide

/-- The shared path enters the same one-instruction marker at PC 497,
then starts its lower-half/table body at 498. -/
theorem sharedJoin_slice :
    (Artifact.submissionArtifact.instructions.drop 206).take joinTemplate.length = joinTemplate := by rfl

def sharedJoinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 206 sharedJoin_slice
    (by change 206 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide)) (by decide)

theorem sharedJoin_pc : sharedJoinSite.startPC = LoopCompletionControl.sharedTailPC := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 206) = UInt256.ofNat 497
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_sharedJoin (s : State) (stack : List UInt256) (hstack : stack.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := LoopCompletionControl.sharedTailPC, stack := stack}
      {s with pc := UInt256.ofNat 498, stack := stack} := by
  apply PadLift.gasSteps_of_raw sharedJoinSite
    {s with pc := LoopCompletionControl.sharedTailPC, stack := stack} _
    hcode hfork hrun hnp sharedJoin_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · simp [joinTemplate, LoopCompletionControl.sharedTailPC, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    decide

/-- Enter the ordinary message block through its loop-head JUMPDEST.
The endian body starts at 462; unlike the shared lower-half entry at 497,
this entry reads and reverses both message halves. -/
def gasSteps_normal (s : State) (ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat)
    (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 32 = UInt256.ofNat (p + 32))
    (hq0 : off = UInt256.ofNat p)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 461, stack := PersistentMaskEndian.stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho}
      {s with pc := UInt256.ofNat 824, stack := PersistentMaskEndian.stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho, memory := PoolReference.dataMemory s.memory p, activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  have gj := gasSteps_join s
    (PersistentMaskEndian.stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho)
    (by simp only [PersistentMaskEndian.stk, Pair13Endian.stk, List.length_cons]; omega)
    hrun hcode hfork hnp
  have gn := ColdOrdinarySites.gasSteps_normal s ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    hstack hrun hp hbound hq1 hq0 hcode hfork hnp
  exact gj.trans gn

#print axioms gasSteps_join
#print axioms gasSteps_sharedJoin
#print axioms gasSteps_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdAlignedBlock
