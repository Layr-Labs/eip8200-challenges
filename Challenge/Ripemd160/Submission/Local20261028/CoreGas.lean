import Challenge.Ripemd160.Submission.Local20261028.CandidateArtifact
import Challenge.Ripemd160.Submission.Local20261028.ModFoldLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
private def plainDecidable (operation : Operation) : Decidable (plainOp operation) := by
  cases operation <;> dsimp only [plainOp] <;> infer_instance
private def instructionWellFormedDecidable (instruction : Instr) :
    Decidable (DataStepper.WellFormed .Osaka instruction) :=
  match instruction with
  | .push width value => inferInstanceAs (Decidable
      (value.toNat < 256 ^ width.val ∧
        (Operation.Push ⟨width⟩).availableInFork .Osaka = true))
  | .op operation =>
    letI := plainDecidable operation
    inferInstanceAs (Decidable (Decode.opcodeOf (PcEncoding.opByte operation) = some operation ∧
      plainOp operation ∧ operation.availableInFork .Osaka = true))
def wellFormedCheck (i : Instr) : Bool := @decide (DataStepper.WellFormed .Osaka i) (instructionWellFormedDecidable i)
theorem wellFormed_of_check (code : List Instr) (h : code.all wellFormedCheck = true) :
    ∀ i ∈ code, DataStepper.WellFormed .Osaka i := by
  intro i hi
  letI := instructionWellFormedDecidable i
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
theorem actual_slice :
    (CandidateArtifact.artifact.instructions.drop 349).take CoreBody.template.length = CoreBody.template := by
  rfl
def site : GenericRoundSite CandidateArtifact.artifact .Osaka CoreBody.template :=
  StackSiteBuilder.ofSlice CoreBody.template 349 actual_slice
    (by change 349 + CoreBody.template.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count, CandidateArtifact.count2]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem site_pc : site.startPC = UInt256.ofNat 824 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 349) = UInt256.ofNat 824
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def gasSteps (s : State) (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      {s with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result s.memory h) off limit rho} := by
  apply ModFoldLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h off limit rho}
    {s with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result s.memory h) off limit rho}
    hc hf hr hnp site_pc.symm
  · apply ModFoldLift.advancesAll_sound
    decide +kernel
  · exact CoreBody.run s h off limit rho hs hr ha
#print axioms site
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreGas
