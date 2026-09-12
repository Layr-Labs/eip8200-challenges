import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace
def packedHash (h : Compression.HashState) : UInt256 := (UInt256.lor (ofUInt32 h.h4) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h3) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h2) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h1) (UInt256.shiftLeft (ofUInt32 h.h0) (UInt256.ofNat 32))) (UInt256.ofNat 32))) (UInt256.ofNat 32))) (UInt256.ofNat 32)))
def template : List Instr := [
   .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .SHL, .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .SHL, .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .SHL, .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .SHL, .op .OR ]
def join (a b : UInt256) : UInt256 := UInt256.lor (UInt256.shiftLeft a (UInt256.ofNat 32)) b

private theorem join_reverse (a b : UInt256) :
    join a b = UInt256.lor b (UInt256.shiftLeft a (UInt256.ofNat 32)) :=
  Word.lor_comm _ _

theorem run_raw (s : State) (pc a b c d e : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 1012) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := [a,b,c,d,e] ++ rho} =
      some {s with pc := pcAfter pc template, stack := join (join (join (join a b) c) d) e :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 11) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, join,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

theorem run_template (s : State) (pc off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 1010) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with pc := pcAfter pc template, stack := packedHash h :: off :: limit :: rho} := by
  have hs : (off :: limit :: rho).length ≤ 1012 := by simpa using hstack
  simpa only [StaggerPersistentFrame.frame, packedHash, join_reverse, List.cons_append, List.nil_append] using
    run_raw s pc (ofUInt32 h.h0) (ofUInt32 h.h1) (ofUInt32 h.h2)
      (ofUInt32 h.h3) (ofUInt32 h.h4) (off :: limit :: rho) hs hrun

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3833).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3833 actual_slice
    (by change 3833 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4609 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3833) = UInt256.ofNat 4609
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound template (by decide)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 1010) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4609, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4625, stack := packedHash h :: off :: limit :: rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4609, stack := StaggerPersistentFrame.frame h off limit rho}
    {s with pc := UInt256.ofNat 4625, stack := packedHash h :: off :: limit :: rho}
    hcode hfork hrun hnp site_pc.symm advances
  have hraw := run_template s (UInt256.ofNat 4609) off limit h rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 4609) template = UInt256.ofNat 4625 := by decide
  rw [hend] at hraw
  exact hraw

#print axioms run_raw
#print axioms run_template
#print axioms actual_slice
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
