import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound32
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace PairedAllInlineCoreTrace CachedCoreCommon
def actualTemplate : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 1993).take actualTemplate.length = actualTemplate := by rfl
def actualSite : GenericRoundSite Artifact.submissionArtifact .Osaka actualTemplate :=
  StackSiteBuilder.ofSlice actualTemplate 1993 actual_slice
    (by change 1993 + actualTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := actualTemplate) (by decide))
    (by decide)
theorem actual_pc : actualSite.startPC = UInt256.ofNat 2531 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1993) = UInt256.ofNat 2531
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem actual_advances : ∀ instruction ∈ actualTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def originalTemplate : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem original_eq : originalTemplate = PairedAllInlineCoreTrace.inline32Block.code := by rfl
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 22))),
    x.v0,
    x.v2,
    (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 3) (UInt256.land x.v9 (UInt256.land x.v7 (UInt256.add x.v0 (UInt256.add (UInt256.lor (MachineState.readWord memory 288) (MachineState.readWord memory 688)) (UInt256.add (UInt256.xor x.v4 (UInt256.lor (UInt256.lnot x.v3) x.v2)) x.v1)))))) (UInt256.land x.v7 (UInt256.add x.v0 (UInt256.add (UInt256.lor (MachineState.readWord memory 288) (MachineState.readWord memory 688)) (UInt256.add (UInt256.xor x.v4 (UInt256.lor (UInt256.lnot x.v3) x.v2)) x.v1)))))) (UInt256.ofNat 23)))),
    x.v4,
    x.v5,
    x.v6,
    x.v7,
    x.v8,
    x.v9 ] ++ (cache memory ++ rho)
theorem run_original (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq originalTemplate {s with pc := UInt256.ofNat 2412, stack := inputStack s.memory x rho} =
      some {s with pc := UInt256.ofNat 2458, stack := outputStack s.memory x rho} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [originalTemplate, inputStack, outputStack, cache,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.lor_comm]
  all_goals repeat first | apply And.intro | rfl
theorem run_actual (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq actualTemplate {s with pc := UInt256.ofNat 2531, stack := inputStack s.memory x rho} =
      some {s with pc := UInt256.ofNat 2574, stack := outputStack s.memory x rho} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [actualTemplate, inputStack, outputStack, cache,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.lor_comm]
  all_goals repeat first | apply And.intro | rfl
def gasSteps (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 2531, stack := coreStack [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f (cache s.memory ++ rho)}
      {s with pc := UInt256.ofNat 2574, stack := coreStack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] (PairedAllInlineCoreTrace.inline32Block.eval s.memory f) (cache s.memory ++ rho)} := by
  let x : Input := ⟨CoreReg.word .k f, CoreReg.word .a f, CoreReg.word .b f, CoreReg.word .c f, CoreReg.word .d f, CoreReg.word .e f, CoreReg.word .factor f, CoreReg.word .pair f, CoreReg.word .upper f, CoreReg.word .lower f⟩
  have hin : inputStack s.memory x rho = coreStack [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f (cache s.memory ++ rho) := rfl
  have hs : (cache s.memory ++ rho).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  have hold := PairedAllInlineCoreTrace.inline32Block.run s f (cache s.memory ++ rho) hs hrun hactive
  have hraw := run_original s x rho hstack hrun hactive
  rw [original_eq, hin] at hraw
  have he : outputStack s.memory x rho = coreStack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] (PairedAllInlineCoreTrace.inline32Block.eval s.memory f) (cache s.memory ++ rho) :=
    congrArg State.stack (Option.some.inj (hraw.symm.trans hold))
  have g := gasSteps_terminal_of_raw actualSite
    {s with pc := UInt256.ofNat 2531, stack := inputStack s.memory x rho} _
    hcode hfork hrun hnp actual_pc.symm actual_advances (run_actual s x rho hstack hrun hactive)
  rw [hin, he] at g
  exact g
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound32
