import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Round
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Site
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairedAllInlineCoreTrace Strip78Round CachedCoreCommon
def actualTemplate : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 112),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨10, by decide⟩),
    .op .SHR ]


theorem run_actual (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq actualTemplate {s with pc := pc, stack := inline78Entry q (cache s.memory ++ rho)} =
      some {s with pc := pcAfter pc actualTemplate, stack := stripOutput q (stripT (inline78Frame s.memory q) (PairedHelperBooleanTrace.inline4Boolean q)) (cache s.memory ++ rho)} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedHelperBooleanTrace.active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [actualTemplate, inline78Entry, stripOutput, cache,
    stripT, PairedHelperBooleanTrace.scaledRotation, PairedHelperBooleanTrace.inlineSum,
    inline78Frame, TerminalRound.modifiedC10,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat]
  constructor
  · rfl
  constructor
  · rfl
  · change stripT (inline78Frame s.memory q) (PairedSynthCoreTrace.fourRaw q) =
      stripT (inline78Frame s.memory q) (PairedHelperBooleanTrace.inline4Boolean q)
    rw [PairedSynthCoreTrace.fourRaw_eq_inline4Boolean]

theorem template_slice :
    (Artifact.submissionArtifact.instructions.drop 3846).take actualTemplate.length = actualTemplate := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka actualTemplate :=
  StackSiteBuilder.ofSlice actualTemplate 3846 template_slice
    (by
      change 3846 + actualTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := actualTemplate) (by decide))
    (by decide)

theorem site_startPC : site.startPC = UInt256.ofNat 4523 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3846) = UInt256.ofNat 4523
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem actualTemplate_pc : pcAfter (UInt256.ofNat 4523) actualTemplate = UInt256.ofNat 4568 := by decide

def gasSteps (s : State) (f : PairedHelperBooleanTrace.CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4523, stack := inline78Entry f.frame (cache s.memory ++ rho)}
      {s with pc := UInt256.ofNat 4568, stack := inline79Entry (dirtyFrame s.memory f) (cache s.memory ++ rho)} := by
  have hraw := run_actual s (UInt256.ofNat 4523) f.frame rho hstack hrun hactive
  rw [actualTemplate_pc, output_dirtyFrame] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp
    site_startPC.symm
    (by apply PairedHelperBooleanTrace.coreAdvancesAll_sound; decide)
    hraw

#print axioms run_actual
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Site
