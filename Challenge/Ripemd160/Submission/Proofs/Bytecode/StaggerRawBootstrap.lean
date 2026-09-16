import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
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
    .push ⟨2, by decide⟩ (UInt256.ofNat 528),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 378),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 338),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 218),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 168),
    .op .MLOAD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967323),
    .push ⟨5, by decide⟩ (UInt256.ofNat 4294967325),
    .push ⟨2, by decide⟩ (UInt256.ofNat 988),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 956),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 924),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 892),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 860),
    .op .MLOAD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829954) ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [  ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.ofNat 1352829954),
    (MachineState.readWord memory 832),
    (MachineState.readWord memory 864),
    (MachineState.readWord memory 896),
    (MachineState.readWord memory 928),
    (MachineState.readWord memory 960),
    (UInt256.ofNat 4294967325),
    (UInt256.ofNat 4294967323),
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
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 606).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 606 actual_slice
    (by change 606 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 1048 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 606) = UInt256.ofNat 1048
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
    GasSteps {s with pc := UInt256.ofNat 1048, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 1023, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 1048) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 1048) template = UInt256.ofNat 1023 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawBootstrap
