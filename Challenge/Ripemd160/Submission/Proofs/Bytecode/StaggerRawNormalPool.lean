import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 48),
    .op .MLOAD,
    .op (.Dup ⟨1, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 4),
    .op .MLOAD,
    .op (.Dup ⟨2, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .MLOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 44),
    .op .MLOAD,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 60),
    .op .MLOAD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 56),
    .op .MLOAD,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .MLOAD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 52),
    .op .MLOAD,
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 40),
    .op .MLOAD,
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .MLOAD,
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .MLOAD,
    .op (.Dup ⟨11, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .MLOAD,
    .op (.Dup ⟨12, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 12),
    .op .MLOAD,
    .op (.Dup ⟨13, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MLOAD,
    .op (.Dup ⟨14, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .MLOAD,
    .op (.Dup ⟨15, by decide⟩),
    .op .AND,
    .op (.Swap ⟨14, by decide⟩),
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .op .AND ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land (MachineState.readWord memory 0) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 36)),
    (UInt256.land x.v0 (MachineState.readWord memory 12)),
    (UInt256.land x.v0 (MachineState.readWord memory 32)),
    (UInt256.land x.v0 (MachineState.readWord memory 8)),
    (UInt256.land x.v0 (MachineState.readWord memory 28)),
    (UInt256.land x.v0 (MachineState.readWord memory 40)),
    (UInt256.land x.v0 (MachineState.readWord memory 52)),
    (UInt256.land x.v0 (MachineState.readWord memory 16)),
    (UInt256.land x.v0 (MachineState.readWord memory 56)),
    (UInt256.land x.v0 (MachineState.readWord memory 60)),
    (UInt256.land x.v0 (MachineState.readWord memory 44)),
    (UInt256.land x.v0 (MachineState.readWord memory 20)),
    (UInt256.land x.v0 (MachineState.readWord memory 4)),
    (UInt256.land x.v0 (MachineState.readWord memory 48)),
    (UInt256.land x.v0 (MachineState.readWord memory 24)) ] ++ rho
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 19) : rho.length + n < 1024 := by omega
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
    (Artifact.submissionArtifact.instructions.drop 358).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 358 actual_slice
    (by change 358 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 573 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 358) = UInt256.ofNat 573
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
    GasSteps {s with pc := UInt256.ofNat 573, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 652, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 573) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 573) template = UInt256.ofNat 652 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool
