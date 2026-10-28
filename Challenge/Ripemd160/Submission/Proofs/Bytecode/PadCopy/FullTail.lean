import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullPrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PersistentStaggerTailBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentLoopSites
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Tail and block exit of the full pad-only copy

The pad-only copy ends with its own copy of the scheduled tail (final
cross-line combination) and its own `SWAP13 JUMP` block exit.  Both are
byte-identical to the generic ones at 4526 and 4581, so they reuse the
generic raw execution lemmas at the relocated sites.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullTail
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof Paired144WordRound
open StackRoundTrace StackRoundTemplate PersistentStaggerFunctional

/-- Program counter of the copied block exit. -/
def exitPC : Nat := 10262

abbrev template := ScheduledTailRaw.template
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 6993).take template.length = template := by rfl

def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 6993 actual_slice
    (by change 6993 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 10207 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6993) = UInt256.ofNat 10207
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_site (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : StaggerPersistentTailRaw.Input) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10207, stack := StaggerPersistentTailRaw.entryStack (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
      {s with pc := UInt256.ofNat exitPC, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 10207, stack := StaggerPersistentTailRaw.entryStack (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
    {s with pc := UInt256.ofNat exitPC, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho}
    hcode hfork hrun hnp site_pc.symm HoistedInherited.StaggerPersistentTailSite.advances
  have hraw := HoistedInherited.ScheduledTailBridge.run_current s (UInt256.ofNat 10207) h {q with off := off, limit := limit} rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 10207) template = UInt256.ofNat exitPC := by decide
  rw [hend] at hraw
  exact hraw

open HoistedInherited.PersistentStaggerTailBridge (tailInput combine_eq initial_eq) in
theorem suffix_eq (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) :
    PadCopy.FullPrefix.suffixState s (initial h).e q
      (HoistedInherited.StaggerPersistentPackBridge.suffix (initial h) off limit rho) =
    {s with pc := UInt256.ofNat 10207, stack := StaggerPersistentTailRaw.entryStack (StaggerPersistentFrame.bind h
        (tailInput s.memory h (HoistedInherited.StaggerCoreLeft79.epilogueRaw s.memory q) q off limit)) rho} := by
  rw [initial_eq]
  rfl

open HoistedInherited.PersistentStaggerTailBridge (tailInput combine_eq) in
/-- The copied tail leaves the old hash's `h2` above the combined frame. -/
def gasSteps (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 980)
    (hr : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (PadCopy.FullPrefix.suffixState s (initial h).e q
      (HoistedInherited.StaggerPersistentPackBridge.suffix (initial h) off limit rho))
      {s with
        pc := UInt256.ofNat exitPC
        stack := Word.ofUInt32 h.h2 ::
          StaggerPersistentFrame.frame (combine h (StaggerCoreModel.epilogue s.memory q) q) off limit rho} := by
  rw [suffix_eq]
  have g := gasSteps_site s off limit h
    (tailInput s.memory h (HoistedInherited.StaggerCoreLeft79.epilogueRaw s.memory q) q off limit)
    rho hs hr hcode hfork hnp
  rw [combine_eq] at g
  exact g

/-! ## Copied block exit -/

def dispatchCode : List Instr := StaggerPersistentLoopRaw.dispatchTemplate

theorem dispatch_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 7043).take dispatchCode.length = dispatchCode := by rfl

def dispatchSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 7043 dispatch_slice
    (by change 7043 + dispatchCode.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide))
    (by decide)

theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat exitPC := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 7043) = UInt256.ofNat 10262
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Copied block exit: jump to the continuation in slot 12 with the frame unchanged. -/
def gasSteps_dispatch (s : State) (h : Compression.HashState) (off cont junk : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat exitPC, stack := junk :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := cont, stack := StaggerPersistentFrame.frame h off junk rho} := by
  apply ExitLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat exitPC, stack := junk :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · exact StaggerPersistentLoopRaw.run_dispatch s (UInt256.ofNat exitPC) h off cont junk rho (by omega) hrun hvalid

#print axioms gasSteps
#print axioms gasSteps_dispatch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullTail
