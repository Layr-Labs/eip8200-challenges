import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open StaggerPersistentPackRaw (template)

def suffix (h : WordLane) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [h.b, h.c, h.d, h.a, off, limit] ++ rho

def input (_memory : ByteArray) (h q : WordLane) (off limit : UInt256) :
    StaggerPersistentPackRaw.Input :=
  ⟨q.d, UInt256.ofNat 1352829926, q.c, q.b, q.e, q.a,
    factorWord, lowerWord, compactMaskWord,
    coefficientWord 0 2, coefficientWord 0 3,
    coefficientWord 3 0, h.e, h.b, h.c, h.d, h.a, off, limit⟩

def entry (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 1129, stack := stack s.memory h.e [.d, .k, .c, .b, .e, .a, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500] q h (UInt256.ofNat 1352829926) (suffix h off limit rho)}

theorem input_eq (memory : ByteArray) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    StaggerPersistentPackRaw.inputStack (input memory h q off limit) rho =
      stack memory h.e [.d, .k, .c, .b, .e, .a, .factor, .lower, .cache 140,
        .cache 190, .cache 310, .cache 350, .cache 500]
        q h (UInt256.ofNat 1352829926) (suffix h off limit rho) := by
  simp [StaggerPersistentPackRaw.inputStack, input, stack, StaggerCoreCommon.word, suffix]

theorem output_eq (memory : ByteArray) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    StaggerPersistentPackRaw.outputStack (input memory h q off limit) rho =
      stack memory h.e [.pair, .upper, .e, .b, .a, .d, .c, .factor, .lower,
        .cache 140, .cache 190, .cache 310, .cache 350, .cache 500]
        (StaggerCoreModel.pair h q) h (StaggerAlgorithm.physicalKey 0)
        (suffix h off limit rho) := by
  have hm : UInt256.lor lowerWord (UInt256.shiftLeft lowerWord (UInt256.ofNat 144)) =
      Paired144WordRound.pairWord := by decide
  have hu : UInt256.shiftLeft lowerWord (UInt256.ofNat 144) = upperWord := by decide
  simp [StaggerPersistentPackRaw.outputStack, input, stack, StaggerCoreCommon.word,
    StaggerCoreModel.pair, StaggerCoreModel.pairWord, suffix, hm, hu, StaggerCoreCommon.lor_comm]
  decide

#print axioms input_eq
#print axioms output_eq

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 679).take template.length = template := by rfl

def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 679 actual_slice
    (by change 679 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 1129 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 679) = UInt256.ofNat 1129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s h q off limit rho)
      (StaggerCore.atRound s h.e 0 (StaggerCoreModel.pair h q) h (suffix h off limit rho)) := by
  have raw := StaggerPersistentPackRaw.run_actual s (UInt256.ofNat 1129)
    (input s.memory h q off limit) rho hs hr
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 1129) template = UInt256.ofNat 1168 := by decide
  rw [hend] at raw
  have g := DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 1129, stack := StaggerPersistentPackRaw.inputStack (input s.memory h q off limit) rho}
    {s with pc := UInt256.ofNat 1168, stack := StaggerPersistentPackRaw.outputStack (input s.memory h q off limit) rho}
    hcode hfork hr hnp site_pc.symm advances raw
  rw [input_eq, output_eq] at g
  exact g

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackBridge
