import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailBinding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift

set_option warningAsError true
set_option maxRecDepth 30000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailSite

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Paired144WordRound

abbrev template := PersistentTailRaw.template

def rawInput (q : WordLane) (off limit : UInt256) : PersistentTailRaw.Input :=
  {a := q.a, b := q.b, c := q.c, d := q.d, e := q.e,
   factor := factorWord, pair := pairWord, upper := upperWord, lower := lowerWord,
   k0 := 28, k1 := 20282409598929303941081901039615, k2 := 127,
   k3 := 20282409608374036906834076368900, k4 := 15,
   k5 := 20282409608374036906851256238088,
   h0 := 0, h1 := 0, h2 := 0, h3 := 0, h4 := 0, off := off, limit := limit}

def entryStack (h : Compression.HashState) (q : WordLane) (off limit : UInt256)
    (rho : List UInt256) : List UInt256 :=
  Table144CoreCommon.stack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower]
    q 0 (PersistentFrame.frame h off limit rho)

theorem entry_eq (h : Compression.HashState) (q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    entryStack h q off limit rho =
      PersistentTailRaw.stack0 (PersistentFrame.bind h (rawInput q off limit)) rho := by
  simp only [entryStack, Table144CoreCommon.stack, Table144CoreCommon.word,
    Table144CoreCommon.lowerWord_literal, Table144Raw.cache, PersistentFrame.frame,
    PersistentTailRaw.stack0, PersistentFrame.bind, rawInput, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]

theorem combine_eq (h : Compression.HashState) (q : WordLane) (off limit : UInt256) :
    PersistentFrame.combine h (rawInput q off limit) = PersistentTailBinding.combine h q := rfl

theorem core_entry (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) :
    Table144Core.atRound s 80 q (PersistentFrame.frame h off limit rho) =
      {s with pc := UInt256.ofNat 4620, stack := entryStack h q off limit rho} := by rfl

theorem run_template (s : State) (pc off limit : UInt256) (h : Compression.HashState)
    (q : WordLane) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := entryStack h q off limit rho} =
      some {s with pc := pcAfter pc template, stack := PersistentFrame.frame (PersistentTailBinding.combine h q) off limit rho} := by
  rw [entry_eq]
  have hraw := PersistentFrame.run_tail s pc h (rawInput q off limit) rho hstack hrun
  rw [combine_eq] at hraw
  exact hraw

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3896).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3896 actual_slice
    (by change 3896 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 4620 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3896) = UInt256.ofNat 4620
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound template (by decide)

def gasSteps_prefix (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : WordLane) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4620, stack := entryStack h q off limit rho}
      {s with pc := UInt256.ofNat 4700, stack := PersistentFrame.frame (PersistentTailBinding.combine h q) off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4620, stack := entryStack h q off limit rho}
    {s with pc := UInt256.ofNat 4700, stack := PersistentFrame.frame (PersistentTailBinding.combine h q) off limit rho}
    hcode hfork hrun hnp site_pc.symm advances
  have hraw := run_template s (UInt256.ofNat 4620) off limit h q rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 4620) template = UInt256.ofNat 4700 := by decide
  rw [hend] at hraw
  exact hraw

def jumpTemplate : List Instr := PadJump.template 490

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3971).take jumpTemplate.length = jumpTemplate := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpTemplate :=
  StackSiteBuilder.ofSlice jumpTemplate 3971 jump_slice
    (by change 3971 + jumpTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := jumpTemplate) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4700 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3971) = UInt256.ofNat 4700
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem jump_advances : ∀ instruction ∈ jumpTemplate.dropLast, PadLift.Advances instruction :=
  PadLift.advancesAll_sound _ (by decide)

theorem valid_driver (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 490).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 296 = 490 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 296 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 490 = true
  rw [hcode]
  exact h

def gasSteps_jump (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1022)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4700, stack := rho}
      {s with pc := UInt256.ofNat 490, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4700, stack := rho} _
    hcode hfork hrun hnp jump_pc.symm jump_advances
  exact PadJump.run_template s (UInt256.ofNat 4700) rho 490 hstack hrun (valid_driver s hcode)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : WordLane) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (Table144Core.atRound s 80 q (PersistentFrame.frame h off limit rho))
      {s with pc := UInt256.ofNat 490, stack := PersistentFrame.frame (PersistentTailBinding.combine h q) off limit rho} := by
  rw [core_entry]
  exact (gasSteps_prefix s off limit h q rho hstack hrun hcode hfork hnp).trans
    (gasSteps_jump s (PersistentFrame.frame (PersistentTailBinding.combine h q) off limit rho)
      (by simp only [PersistentFrame.frame, List.length_append, List.length_cons, List.length_nil]; omega)
      hrun hcode hfork hnp)

#print axioms entry_eq
#print axioms core_entry
#print axioms run_template
#print axioms actual_slice
#print axioms jump_slice
#print axioms gasSteps

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailSite
