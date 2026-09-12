import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawBootstrap
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .op .JUMPDEST,
    .push ⟨2, by decide⟩ (UInt256.ofNat 500),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 350),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 310),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 190),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 140),
    .op .MLOAD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .push ⟨5, by decide⟩ (UInt256.ofNat 4294967297),
    .push ⟨2, by decide⟩ (UInt256.ofNat 960),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 928),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 896),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 832),
    .op .MLOAD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926) ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [  ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.ofNat 1352829926),
    (MachineState.readWord memory 832),
    (MachineState.readWord memory 864),
    (MachineState.readWord memory 896),
    (MachineState.readWord memory 928),
    (MachineState.readWord memory 960),
    (UInt256.ofNat 4294967297),
    (UInt256.ofNat 4294967295),
    (MachineState.readWord memory 140),
    (MachineState.readWord memory 190),
    (MachineState.readWord memory 310),
    (MachineState.readWord memory 350),
    (MachineState.readWord memory 500) ] ++ rho
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, outputStack,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 608).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 608 actual_slice
    (by change 608 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 940 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 608) = UInt256.ofNat 940
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 940, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 995, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 940) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 940) template = UInt256.ofNat 995 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawBootstrap
