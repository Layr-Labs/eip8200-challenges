import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired45
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .op (.Swap ⟨2, by decide⟩),
    .op .POP,
    .push ⟨23, by decide⟩ (UInt256.ofNat 141586572954389725278986803886319569511332025164491681),
    .op (.Swap ⟨5, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op .XOR,
    .op .OR,
    .op .XOR,
    .op .XOR,
    .op .NOT,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 486),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .SHR,
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨12, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .AND,
    .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .AND ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, x.v9, x.v10, x.v11, x.v12, x.v13, x.v14 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v1 (UInt256.shiftRight (UInt256.mul x.v8 x.v4) (UInt256.ofNat 28))),
    x.v1,
    x.v2,
    x.v0,
    (UInt256.land x.v1 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v12 (UInt256.land x.v10 (UInt256.lor (UInt256.shiftRight (UInt256.add (UInt256.ofNat 141586572954389725278986803886319569511332025164491681) (UInt256.add (MachineState.readWord memory 486) (UInt256.add (UInt256.lnot (UInt256.xor (UInt256.xor (UInt256.lor (UInt256.xor (UInt256.land x.v0 x.v7) x.v4) (UInt256.xor x.v2 x.v7)) x.v0) x.v7)) x.v6))) (UInt256.ofNat 72)) (UInt256.add (UInt256.ofNat 141586572954389725278986803886319569511332025164491681) (UInt256.add (MachineState.readWord memory 486) (UInt256.add (UInt256.lnot (UInt256.xor (UInt256.xor (UInt256.lor (UInt256.xor (UInt256.land x.v0 x.v7) x.v4) (UInt256.xor x.v2 x.v7)) x.v0) x.v7)) x.v6)))))) (UInt256.ofNat 20)))),
    x.v5,
    (UInt256.ofNat 141586572954389725278986803886319569511332025164491681),
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14 ] ++ rho
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 23) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, outputStack,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 2401).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 2401 actual_slice
    (by change 2401 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 3129 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2401) = UInt256.ofNat 3129
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
    GasSteps {s with pc := UInt256.ofNat 3129, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 3202, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 3129) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 3129) template = UInt256.ofNat 3202 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired45
