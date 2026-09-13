import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair54
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace SharedCoreCommon
def prefixTemplate : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .push ⟨2, by decide⟩ (UInt256.ofNat 3444),
    .op (.Swap ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 5168),
    .op .JUMP ]
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 2714).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 2714 prefix_slice
    (by change 2714 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 3396 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2714) = UInt256.ofNat 3396
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def suffixTemplate : List Instr :=
  [ .op .JUMPDEST,
    .push ⟨2, by decide⟩ (UInt256.ofNat 320),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 208),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
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
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem suffix_slice :
    (Artifact.submissionArtifact.instructions.drop 2752).take suffixTemplate.length = suffixTemplate := by rfl
def suffixSite : GenericRoundSite Artifact.submissionArtifact .Osaka suffixTemplate :=
  StackSiteBuilder.ofSlice suffixTemplate 2752 suffix_slice
    (by change 2752 + suffixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := suffixTemplate) (by decide))
    (by decide)
theorem suffix_pc : suffixSite.startPC = UInt256.ofNat 3444 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2752) = UInt256.ofNat 3444
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem suffix_advances : ∀ instruction ∈ suffixTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def prefixStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.ofNat 4294967295),
    (UInt256.ofNat 26),
    (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 7) (UInt256.land (UInt256.ofNat 4294967295) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))),
    x.v0,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    x.v6,
    x.v7,
    x.v8,
    (UInt256.ofNat 3444) ] ++ rho
def helperStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.add (UInt256.xor x.v2 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v2) (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 7) (UInt256.land (UInt256.ofNat 4294967295) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.ofNat 26))))) (UInt256.xor (UInt256.land x.v8 x.v2) (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 22)))))) x.v5),
    x.v0,
    x.v2,
    (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 7) (UInt256.land (UInt256.ofNat 4294967295) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.ofNat 26)))),
    x.v4,
    (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 22))),
    x.v6,
    x.v7,
    x.v8,
    (UInt256.ofNat 4294967295) ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v2) (UInt256.ofNat 22))),
    x.v0,
    (UInt256.land x.v7 (UInt256.add x.v0 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 63) (UInt256.land x.v8 (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 320)) (UInt256.add (UInt256.xor x.v2 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v2) (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 7) (UInt256.land (UInt256.ofNat 4294967295) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.ofNat 26))))) (UInt256.xor (UInt256.land x.v8 x.v2) (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 22)))))) x.v5)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 320)) (UInt256.add (UInt256.xor x.v2 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v2) (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 7) (UInt256.land (UInt256.ofNat 4294967295) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.ofNat 26))))) (UInt256.xor (UInt256.land x.v8 x.v2) (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 22)))))) x.v5)))))) (UInt256.ofNat 24)))),
    (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 7) (UInt256.land (UInt256.ofNat 4294967295) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576)) (UInt256.add (UInt256.xor x.v3 (UInt256.land (UInt256.xor (UInt256.lor x.v8 x.v3) x.v2) (UInt256.xor (UInt256.land x.v8 x.v3) x.v0))) x.v1)))))) (UInt256.ofNat 26)))),
    x.v4,
    (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 22))),
    x.v6,
    x.v7,
    x.v8,
    (UInt256.ofNat 4294967295) ] ++ rho
def originalTemplate : List Instr :=
  PairedAllInlineCoreTrace.inline54Block.code ++ PairedAllInlineCoreTrace.inline55Block.code
theorem return_valid (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 3444 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 2752 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 2752 = 3444 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  rw [hp] at h
  rw [hcode]
  exact h
theorem run_prefix (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    runInstrSeq prefixTemplate {s with pc := UInt256.ofNat 3396, stack := inputStack x rho} =
      some {s with pc := UInt256.ofNat 5168, stack := prefixStack s.memory x rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  have hvalid := helper_valid s hcode
  simp (discharger := omega) [prefixTemplate, inputStack, prefixStack, helperStack, outputStack,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, hvalid]
  all_goals repeat first | apply And.intro | rfl
theorem run_helper (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    runInstrSeq helperTemplate {s with pc := UInt256.ofNat 5168, stack := prefixStack s.memory x rho} =
      some {s with pc := UInt256.ofNat 3444, stack := helperStack s.memory x rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  have hvalid := return_valid s hcode
  simp (discharger := omega) [helperTemplate, inputStack, prefixStack, helperStack, outputStack,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, hvalid]
  all_goals repeat first | apply And.intro | rfl
theorem run_suffix (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    runInstrSeq suffixTemplate {s with pc := UInt256.ofNat 3444, stack := helperStack s.memory x rho} =
      some {s with pc := UInt256.ofNat 3482, stack := outputStack s.memory x rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [suffixTemplate, inputStack, prefixStack, helperStack, outputStack,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat]
  all_goals repeat first | apply And.intro | rfl
theorem run_original (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    runInstrSeq originalTemplate {s with pc := UInt256.ofNat 3453, stack := inputStack x rho} =
      some {s with pc := UInt256.ofNat 3558, stack := outputStack s.memory x rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [originalTemplate, inputStack, prefixStack, helperStack, outputStack, PairedAllInlineCoreTrace.inline54Block, PairedAllInlineCoreTrace.inline55Block, PairedAllInlineCoreTrace.inline54Template, PairedAllInlineCoreTrace.inline55Template,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat]
  all_goals repeat first | apply And.intro | rfl
def gasSteps_raw (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 3396, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 3482, stack := outputStack s.memory x rho} := by
  have g0 := gasSteps_terminal_of_raw prefixSite {s with pc := UInt256.ofNat 3396, stack := inputStack x rho} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
    (run_prefix s x rho hstack hrun hactive hcode)
  have g1 := gasSteps_terminal_of_raw helperSite {s with pc := UInt256.ofNat 5168, stack := prefixStack s.memory x rho} _ hcode hfork hrun hnp helper_pc.symm helper_advances
    (run_helper s x rho hstack hrun hactive hcode)
  have g2 := gasSteps_terminal_of_raw suffixSite {s with pc := UInt256.ofNat 3444, stack := helperStack s.memory x rho} _ hcode hfork hrun hnp suffix_pc.symm suffix_advances
    (run_suffix s x rho hstack hrun hactive hcode)
  exact g0.trans (g1.trans g2)

def pairEval (memory : ByteArray) (f : CoreFrame) : CoreFrame :=
  PairedAllInlineCoreTrace.inline55Block.eval memory
    (PairedAllInlineCoreTrace.inline54Block.eval memory f)

def gasSteps_pair (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 3396, stack := coreStack [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] f rho}
      {s with pc := UInt256.ofNat 3482, stack := coreStack [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] (pairEval s.memory f) rho} := by
  let x : Input := ⟨CoreReg.word .d f, CoreReg.word .a f, CoreReg.word .b f, CoreReg.word .c f, CoreReg.word .k f, CoreReg.word .e f, CoreReg.word .factor f, CoreReg.word .pair f, CoreReg.word .upper f⟩
  have hin : inputStack x rho = coreStack [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] f rho := rfl
  have h0 := PairedAllInlineCoreTrace.inline54Block.run s f rho hstack hrun hactive
  have h1 := PairedAllInlineCoreTrace.inline55Block.run s
    (PairedAllInlineCoreTrace.inline54Block.eval s.memory f) rho hstack hrun hactive
  have hold := DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1
  have hraw := run_original s x rho hstack hrun hactive hcode
  rw [hin] at hraw
  have he : outputStack s.memory x rho = coreStack [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] (pairEval s.memory f) rho := by
    exact congrArg State.stack (Option.some.inj (hraw.symm.trans hold))
  have g := gasSteps_raw s x rho hstack hrun hactive hcode hfork hnp
  rw [hin, he] at g
  exact g
#print axioms gasSteps_pair
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair54
