import Challenge.Ripemd160.Submission.Proofs.Bytecode.MemoryPackedOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace
@[simp] private theorem rawZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
def packedHash (h : Compression.HashState) : UInt256 := (UInt256.lor (ofUInt32 h.h4) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h3) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h2) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h1) (UInt256.shiftLeft (ofUInt32 h.h0) (UInt256.ofNat 32))) (UInt256.ofNat 32))) (UInt256.ofNat 32))) (UInt256.ofNat 32)))
/-- Five descending stores pack the chaining words into bytes 28 through 47. -/
def prefixTemplate : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]
def bodyTemplate : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 16), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 12), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 8), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 4), .op .MSTORE,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 16), .op .MLOAD]
def template : List Instr := prefixTemplate ++ bodyTemplate

def stored (s : State) (address : Nat) (word : UInt32) : State :=
  {s with memory := MemoryPackedOutput.store s.memory address word
          activeWords := s.activeWordsAfterUInt256 address 32}

def prepared (s : State) (h : Compression.HashState) : State :=
  let t := stored (stored (stored (stored (stored s 16 h.h4) 12 h.h3) 8 h.h2) 4 h.h1) 0 h.h0
  {t with activeWords := t.activeWordsAfterUInt256 16 32}

theorem run_template (s : State) (pc off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {prepared s h with pc := pcAfter pc template, stack := packedHash h :: off :: limit :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hread := MemoryPackedOutput.readWord_eq s.memory h
  have hpack : PackedOutputMath.pack5 h.h0 h.h1 h.h2 h.h3 h.h4 = packedHash h := by
    simp only [PackedOutputMath.pack5, PackedOutputMath.append32, packedHash, Word.lor_comm]
  simp only [MemoryPackedOutput.memory, MemoryPackedOutput.store, hpack] at hread
  simp (discharger := omega) [template, prefixTemplate, bodyTemplate,
    StaggerPersistentFrame.frame, prepared, stored, MemoryPackedOutput.store,
    runInstrSeq, DataStepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.ofUInt32_toNat, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hread,
    State.activeWordsAfterUInt256]
  all_goals repeat first | apply And.intro | rfl

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3568).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3568 actual_slice
    (by change 3568 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4653 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3568) = UInt256.ofNat 4653
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound template (by decide)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4653, stack := StaggerPersistentFrame.frame h off limit rho}
      {prepared s h with pc := UInt256.ofNat 4676, stack := packedHash h :: off :: limit :: rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4653, stack := StaggerPersistentFrame.frame h off limit rho}
    {prepared s h with pc := UInt256.ofNat 4676, stack := packedHash h :: off :: limit :: rho}
    hcode hfork hrun hnp site_pc.symm advances
  have hraw := run_template s (UInt256.ofNat 4653) off limit h rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 4653) template = UInt256.ofNat 4676 := by decide
  rw [hend] at hraw
  exact hraw

#print axioms run_template
#print axioms actual_slice
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
