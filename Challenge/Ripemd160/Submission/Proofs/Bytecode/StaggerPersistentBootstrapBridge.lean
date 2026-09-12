import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreBody
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired80WordRound Paired80WordRotate Paired80WordBoolean StaggerCoreCommon
open StaggerPersistentBootstrapRaw (template)
open PersistentStaggerFunctional (initial)

theorem initial_eq (h : Compression.HashState) :
    initial h = (⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
      Word.ofUInt32 h.h3, Word.ofUInt32 h.h4⟩ : WordLane) := by
  simp only [StaggerRepresentation.word_ofUInt32]
  rfl

def input (h : Compression.HashState) (off limit : UInt256) :
    StaggerPersistentBootstrapRaw.Input :=
  ⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
    Word.ofUInt32 h.h3, Word.ofUInt32 h.h4, off, limit⟩

def entry (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 927, stack := StaggerPersistentFrame.frame h off limit rho}

theorem input_eq (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) :
    StaggerPersistentBootstrapRaw.inputStack (input h off limit) rho =
      StaggerPersistentFrame.frame h off limit rho := rfl

theorem output_eq (memory : ByteArray) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) :
    StaggerPersistentBootstrapRaw.outputStack memory (input h off limit) rho =
      stack memory (Word.ofUInt32 h.h4)
        [.k, .a, .b, .c, .d, .e, .factor, .lower, .cache 140,
          .cache 190, .cache 310, .cache 350, .cache 500]
        (initial h) (initial h) (UInt256.ofNat 1352829926)
        (StaggerPersistentFrame.coreRest h off limit rho) := by
  have hf : factorWord = UInt256.ofNat 4294967297 := by decide
  have hm : lowerWord = UInt256.ofNat 4294967295 := by decide
  simp [StaggerPersistentBootstrapRaw.outputStack, input, stack, StaggerCoreCommon.word,
    initial_eq, StaggerPersistentFrame.coreRest, hf, hm]

#print axioms initial_eq
#print axioms output_eq

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 599).take template.length = template := by rfl

def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 599 actual_slice
    (by change 599 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 927 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 599) = UInt256.ofNat 927
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 900) (hr : s.halt = .Running)
    (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s h off limit rho)
      (StaggerPersistentCoreRight.initialState s (Word.ofUInt32 h.h4) (initial h)
        (StaggerPersistentFrame.coreRest h off limit rho)) := by
  have raw := StaggerPersistentBootstrapRaw.run_actual s (UInt256.ofNat 927)
    (input h off limit) rho hs hr ha
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 927) template = UInt256.ofNat 964 := by decide
  rw [hend] at raw
  have g := DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 927, stack := StaggerPersistentBootstrapRaw.inputStack (input h off limit) rho}
    {s with pc := UInt256.ofNat 964, stack := StaggerPersistentBootstrapRaw.outputStack s.memory (input h off limit) rho}
    hcode hfork hr hnp site_pc.symm advances raw
  rw [input_eq, output_eq] at g
  exact g

def gasSteps_body (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 894) (hr : s.halt = .Running)
    (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s h off limit rho)
      (StaggerCore.suffixState s (Word.ofUInt32 h.h4)
        (StaggerCoreModel.paired s.memory (initial h))
        (StaggerPersistentFrame.coreRest h off limit rho)) := by
  have gb := gasSteps s h off limit rho (by omega) hr ha hcode hfork hnp
  have gc := StaggerPersistentCoreBody.gasSteps s (initial h) off limit rho hs hr ha hcode hfork hnp
  have he : (initial h).e = Word.ofUInt32 h.h4 := by rw [initial_eq]
  have hsuf : StaggerPersistentPackBridge.suffix (initial h) off limit rho =
      StaggerPersistentFrame.coreRest h off limit rho := by
    rw [initial_eq]
    rfl
  rw [he, hsuf] at gc
  exact gb.trans gc

#print axioms gasSteps
#print axioms gasSteps_body
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapBridge
