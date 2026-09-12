import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore28
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 504),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 486),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 468),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 450),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 432),
    .op .MSTORE,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 414),
    .op .MSTORE,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 396),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 378),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 342),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 324),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 306),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 270),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 234),
    .op .MSTORE ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, x.v9, x.v10, x.v11, x.v12, x.v13 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13 ] ++ rho
def outputMemory (memory : ByteArray) (x : Input) : ByteArray :=
  (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory 504 x.v0) 486 x.v9) 468 x.v1) 450 x.v10) 432 x.v10) 414 x.v12) 396 x.v12) 378 x.v6) 360 x.v6) 342 x.v2) 324 x.v2) 306 x.v4) 288 x.v3) 270 x.v4) 252 x.v5) 234 x.v5)
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 17) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, outputStack, outputMemory, PairedScheduleMemory.writeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 565).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 565 actual_slice
    (by change 565 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 866 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 565) = UInt256.ofNat 866
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 866, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 938, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hraw := run_actual s (UInt256.ofNat 866) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 866) template = UInt256.ofNat 938 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore28
