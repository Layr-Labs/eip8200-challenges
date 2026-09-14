import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighRoute
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentFrame

def template : List Instr :=
  [.op (.Swap ⟨11,by decide⟩), .push 1 64, .op .ADD, .op (.Swap ⟨11,by decide⟩),
   .push 2 4705, .op .JUMP]

theorem slice : (Artifact.submissionArtifact.instructions.drop 3721).take template.length=template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3721 slice
    (by change 3721+template.length≤Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count];decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions:=template) (by decide)) (by decide)

theorem pc : site.startPC=UInt256.ofNat 4816 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3721)=UInt256.ofNat 4816
  rw [ArtifactByteLength.instructionPC_eq_byteLength];decide

theorem valid (s : State) (hcode : s.executionEnv.code=Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 4705=true := by
  have hp : Artifact.submissionArtifact.instructionPC 3659=4705 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength];decide
  have h:=Artifact.submissionArtifact.isValidJumpDest_index 3659 (by rfl)
  rw [hp] at h
  rw [hcode]
  exact h

def gasSteps (s : State) (h : Compression.HashState) (off lim : UInt256) (rho : List UInt256)
    (hs : rho.length≤900) (hr : s.halt=.Running)
    (hc : s.executionEnv.code=Artifact.submissionArtifact.code) (hf : s.fork=.Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr=false) :
    GasSteps {s with pc:=UInt256.ofNat 4816, stack:=frame h off lim rho}
      {s with pc:=UInt256.ofNat 4705, stack:=frame h off (lim+UInt256.ofNat 64) rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc:=UInt256.ofNat 4816, stack:=frame h off lim rho} _ hc hf hr hnp pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hcap (n : Nat) (hn : n≤20) : rho.length+n<1024 := by omega
    have hv:=valid s hc
    simp (discharger:=omega) [template,frame,runInstrSeq,DataStepper.runInstr,hr,
      List.exchange,List.getElem?_cons_zero,Nat.add_assoc,hcap,UInt256.succ,Word.word_toNat_ofNat,
      Word.literal_eq_ofNat,hv,Word.word_add_comm]
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighRoute
