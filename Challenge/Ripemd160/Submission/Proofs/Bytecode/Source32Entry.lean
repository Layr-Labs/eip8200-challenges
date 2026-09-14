import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Entry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def guardTemplate : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .CALLDATASIZE,
   .op (.Dup ⟨0, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .EQ,
   .push ⟨2, by decide⟩ (UInt256.ofNat 4919), .op .JUMPI]

def constructorTemplate : List Instr :=
  [.op .JUMPDEST, .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .push ⟨1, by decide⟩ (UInt256.ofNat 56), .op .MSTORE, .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 391), .op .JUMP]

def dispatchTemplate : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 525), .op .JUMPI]

theorem run_guard_miss (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hmiss : s.executionEnv.calldata.size ≠ 32) :
    runInstrSeq guardTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc guardTemplate
        stack := UInt256.ofNat s.executionEnv.calldata.size :: UInt256.ofNat 128 :: rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat s.executionEnv.calldata.size) = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
    norm_num only
    rw [if_neg hmiss.symm]
  simp (discharger := omega) [guardTemplate, runInstrSeq, DataStepper.runInstr, hrun,
    hbase, hcap, heq, List.length_cons, List.getElem?_cons_zero, Nat.add_assoc,
    pcAfter, UInt256.succ, Instr.size, Word.literal_eq_ofNat, UInt256.isTrue]
  rfl

theorem run_guard_hit (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hhit : s.executionEnv.calldata.size = 32)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4919 = true) :
    runInstrSeq guardTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := UInt256.ofNat 4919
        stack := UInt256.ofNat 32 :: UInt256.ofNat 128 :: rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [guardTemplate, runInstrSeq, DataStepper.runInstr, hrun,
    hbase, hcap, hhit, UInt256.eq, hvalid, List.length_cons, List.getElem?_cons_zero,
    Nat.add_assoc, Word.literal_eq_ofNat, UInt256.isTrue]

theorem run_constructor (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 3 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 391 = true) :
    runInstrSeq constructorTemplate
      {s with pc := pc, stack := UInt256.ofNat 32 :: UInt256.ofNat 128 :: rho} =
      some {s with
        pc := UInt256.ofNat 391
        stack := rho
        memory := Source32Memory.source32Memory s.memory} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have h56 : MachineState.activeWordsAfter s.activeWords.toNat 56 32 = s.activeWords.toNat := by
    simp [MachineState.activeWordsAfter, Nat.max_eq_left (by omega : 3 ≤ s.activeWords.toNat), Nat.max_eq_left (by omega : 2 ≤ s.activeWords.toNat)]
  have h32 : MachineState.activeWordsAfter s.activeWords.toNat 32 32 = s.activeWords.toNat := by
    simp [MachineState.activeWordsAfter, Nat.max_eq_left (by omega : 3 ≤ s.activeWords.toNat), Nat.max_eq_left (by omega : 2 ≤ s.activeWords.toNat)]
  simp (discharger := omega) [constructorTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, hbase, hcap, hvalid, State.activeWordsAfterUInt256,
    h56, h32, Source32Memory.source32Memory, Source32Memory.writeWord,
    ← Word.word_eq_ofNat_toNat, List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat]

theorem run_dispatch_miss (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 2 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord s.memory 32 = UInt256.ofNat 0) :
    runInstrSeq dispatchTemplate {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc dispatchTemplate, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have ha : MachineState.activeWordsAfter s.activeWords.toNat 32 32 = s.activeWords.toNat := by
    simp [MachineState.activeWordsAfter, Nat.max_eq_left hactive]
  simp (discharger := omega) [dispatchTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, hbase, hcap, hzero, ha, State.activeWordsAfterUInt256,
    List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat, UInt256.isTrue,
    pcAfter, UInt256.succ, Instr.size, ← Word.word_eq_ofNat_toNat]
  rfl

theorem run_dispatch_hit (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 2 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord s.memory 32 = UInt256.ofNat 128)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 525 = true) :
    runInstrSeq dispatchTemplate {s with pc := pc, stack := rho} =
      some {s with pc := UInt256.ofNat 525, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have ha : MachineState.activeWordsAfter s.activeWords.toNat 32 32 = s.activeWords.toNat := by
    simp [MachineState.activeWordsAfter, Nat.max_eq_left hactive]
  simp (discharger := omega) [dispatchTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, hbase, hcap, hflag, ha, State.activeWordsAfterUInt256, hvalid,
    List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat, UInt256.isTrue, ← Word.word_eq_ofNat_toNat]



theorem guard_slice :
    (Artifact.submissionArtifact.instructions.drop 3691).take guardTemplate.length = guardTemplate := by rfl

def guardSite : GenericRoundSite Artifact.submissionArtifact .Osaka guardTemplate :=
  StackSiteBuilder.ofSlice guardTemplate 3691 guard_slice
    (by change 3691 + guardTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := guardTemplate) (by decide)) (by decide)

theorem guard_pc : guardSite.startPC = UInt256.ofNat 4678 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3691) = UInt256.ofNat 4678
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem constructor_slice :
    (Artifact.submissionArtifact.instructions.drop 3816).take constructorTemplate.length = constructorTemplate := by rfl

def constructorSite : GenericRoundSite Artifact.submissionArtifact .Osaka constructorTemplate :=
  StackSiteBuilder.ofSlice constructorTemplate 3816 constructor_slice
    (by change 3816 + constructorTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := constructorTemplate) (by decide)) (by decide)

theorem constructor_pc : constructorSite.startPC = UInt256.ofNat 4919 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3816) = UInt256.ofNat 4919
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 291).take dispatchTemplate.length = dispatchTemplate := by rfl

def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchTemplate :=
  StackSiteBuilder.ofSlice dispatchTemplate 291 dispatch_slice
    (by change 291 + dispatchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchTemplate) (by decide)) (by decide)

theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 481 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 291) = UInt256.ofNat 481
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_constructor (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 4919 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3816 = 4919 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hv := Artifact.submissionArtifact.isValidJumpDest_index 3816 (by rfl)
  rw [hp] at hv
  rw [hcode]
  exact hv

theorem valid_initial (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 391 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 268 = 391 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hv := Artifact.submissionArtifact.isValidJumpDest_index 268 (by rfl)
  rw [hp] at hv
  rw [hcode]
  exact hv

theorem valid_lower (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 525 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 322 = 525 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hv := Artifact.submissionArtifact.isValidJumpDest_index 322 (by rfl)
  rw [hp] at hv
  rw [hcode]
  exact hv

def gasSteps_guard_miss (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hmiss : s.executionEnv.calldata.size ≠ 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4678, stack := rho}
      {s with pc := UInt256.ofNat 4689, stack := UInt256.ofNat s.executionEnv.calldata.size :: UInt256.ofNat 128 :: rho} := by
  apply PadLift.gasSteps_of_raw guardSite {s with pc := UInt256.ofNat 4678, stack := rho} _
    hcode hfork hrun hnp guard_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have h := run_guard_miss s (UInt256.ofNat 4678) rho hstack hrun hfit hmiss
    have hp : pcAfter (UInt256.ofNat 4678) guardTemplate = UInt256.ofNat 4689 := by decide
    rw [hp] at h
    exact h

def gasSteps_guard_hit (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hhit : s.executionEnv.calldata.size = 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4678, stack := rho}
      {s with pc := UInt256.ofNat 4919, stack := UInt256.ofNat 32 :: UInt256.ofNat 128 :: rho} := by
  apply PadLift.gasSteps_of_raw guardSite {s with pc := UInt256.ofNat 4678, stack := rho} _
    hcode hfork hrun hnp guard_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have h := run_guard_hit s (UInt256.ofNat 4678) rho hstack hrun hhit (valid_constructor s hcode)
    exact h

def gasSteps_constructor (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 3 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4919, stack := UInt256.ofNat 32 :: UInt256.ofNat 128 :: rho}
      {s with pc := UInt256.ofNat 391, stack := rho, memory := Source32Memory.source32Memory s.memory} := by
  apply PadLift.gasSteps_of_raw constructorSite {s with pc := UInt256.ofNat 4919, stack := UInt256.ofNat 32 :: UInt256.ofNat 128 :: rho} _
    hcode hfork hrun hnp constructor_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have h := run_constructor s (UInt256.ofNat 4919) rho hstack hrun hactive (valid_initial s hcode)
    exact h

def gasSteps_dispatch_miss (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 2 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord s.memory 32 = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 481, stack := rho}
      {s with pc := UInt256.ofNat 488, stack := rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 481, stack := rho} _
    hcode hfork hrun hnp dispatch_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have h := run_dispatch_miss s (UInt256.ofNat 481) rho hstack hrun hactive hzero
    have hp : pcAfter (UInt256.ofNat 481) dispatchTemplate = UInt256.ofNat 488 := by decide
    rw [hp] at h
    exact h

def gasSteps_dispatch_hit (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 2 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord s.memory 32 = UInt256.ofNat 128)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 481, stack := rho}
      {s with pc := UInt256.ofNat 525, stack := rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 481, stack := rho} _
    hcode hfork hrun hnp dispatch_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have h := run_dispatch_hit s (UInt256.ofNat 481) rho hstack hrun hactive hflag (valid_lower s hcode)
    exact h
#print axioms gasSteps_guard_miss
#print axioms gasSteps_guard_hit
#print axioms gasSteps_constructor
#print axioms gasSteps_dispatch_miss
#print axioms gasSteps_dispatch_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Entry
