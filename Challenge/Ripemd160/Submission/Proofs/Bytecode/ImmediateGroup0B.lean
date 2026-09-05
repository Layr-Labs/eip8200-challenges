import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Immediate wrapper group0 part B (left rounds 6,7,8,9,10)

Rounds 6,7,8,9,10 each start by executing the prior return `JUMPDEST`,
then the same eight-instruction immediate call around helper `0x114`.
In this group `base=0xc0`, `j=0`, `K=0`, `r[k]=k`, `s[k]` pinned.
Each site composes its pushes with the unchanged `RoundTrace.gasSteps_round`.
Generated deterministically; see `benchmark-results/ripemd160/h09/gen_h09_group0.py`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0B

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] private theorem valid114 :
    Decode.isValidJumpDest submissionBytecode 0x114 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 208 (by rfl)

/-- Body wrapper site for left round 6. Call indices 1051--1058, return 1059. -/
def site6 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1051
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x7b5
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 7
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 6
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 6: leading `JUMPDEST` at 1050 then eight-instruction call. -/
def path6 : List Located :=
  ⟨1050, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site6
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1050 :
    Artifact.submissionArtifact.instructionPC 1050 = 0x7a5 := by decide
@[simp] private theorem pc1051 :
    Artifact.submissionArtifact.instructionPC 1051 = 0x7a6 := by decide
@[simp] private theorem pc1052 :
    Artifact.submissionArtifact.instructionPC 1052 = 0x7a9 := by decide
@[simp] private theorem pc1053 :
    Artifact.submissionArtifact.instructionPC 1053 = 0x7aa := by decide
@[simp] private theorem pc1054 :
    Artifact.submissionArtifact.instructionPC 1054 = 0x7ac := by decide
@[simp] private theorem pc1055 :
    Artifact.submissionArtifact.instructionPC 1055 = 0x7ae := by decide
@[simp] private theorem pc1056 :
    Artifact.submissionArtifact.instructionPC 1056 = 0x7af := by decide
@[simp] private theorem pc1057 :
    Artifact.submissionArtifact.instructionPC 1057 = 0x7b1 := by decide
@[simp] private theorem pc1058 :
    Artifact.submissionArtifact.instructionPC 1058 = 0x7b4 := by decide

@[simp] private theorem valid7B5 :
    Decode.isValidJumpDest submissionBytecode 0x7b5 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1059 (by rfl)

/-- Wrapper entry for round 6: prior return PC with outer stack. -/
def entry6 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x7a5
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 6. -/
def roundEntry6 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 6)
    (UInt256.ofNat 7) (UInt256.ofNat 0) (UInt256.ofNat 0x7b5)
    ([messageOffset, outerReturn] ++ rest)

theorem run6 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path6
      (entry6 s messageOffset outerReturn rest) =
        some (roundEntry6 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x7b5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x7b5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 7, UInt256.ofNat 0, UInt256.ofNat 0x7b5,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 6, UInt256.ofNat 7, UInt256.ofNat 0,
      UInt256.ofNat 0x7b5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 6, UInt256.ofNat 7,
      UInt256.ofNat 0, UInt256.ofNat 0x7b5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 6,
      UInt256.ofNat 7, UInt256.ofNat 0, UInt256.ofNat 0x7b5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 6, UInt256.ofNat 7, UInt256.ofNat 0,
      UInt256.ofNat 0x7b5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path6, ImmediateWrapper.wrapperPath, site6, entry6,
      roundEntry6, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1050, pc1051, pc1052, pc1053, pc1054, pc1055, pc1056, pc1057, pc1058,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper6 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry6 s messageOffset outerReturn rest)
      (roundEntry6 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path6
  · simpa [entry6, Artifact.submissionArtifact] using hcode
  · simpa [entry6, State.fork] using hfork
  · exact run6 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry6] using hrun
  · simpa [entry6] using hnp

/-- One full helper call for round 6: nine-instruction setup plus verified round body. -/
def gasSteps_round6 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry6 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 6)
        (UInt256.ofNat 7) (UInt256.ofNat 0) (UInt256.ofNat 0x7b5)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper6 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 6) (UInt256.ofNat 7) (UInt256.ofNat 0)
    (UInt256.ofNat 0x7b5) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid7B5
  have hEq : roundEntry6 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 6)
        (UInt256.ofNat 7) (UInt256.ofNat 0) (UInt256.ofNat 0x7b5)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 6. -/
def wrapperWork6 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path6

theorem wrapperWork6_eq : wrapperWork6 = 28 := by rfl

/-- Body wrapper site for left round 7. Call indices 1060--1067, return 1068. -/
def site7 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1060
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x7c5
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 9
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 7
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 7: leading `JUMPDEST` at 1059 then eight-instruction call. -/
def path7 : List Located :=
  ⟨1059, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site7
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1059 :
    Artifact.submissionArtifact.instructionPC 1059 = 0x7b5 := by decide
@[simp] private theorem pc1060 :
    Artifact.submissionArtifact.instructionPC 1060 = 0x7b6 := by decide
@[simp] private theorem pc1061 :
    Artifact.submissionArtifact.instructionPC 1061 = 0x7b9 := by decide
@[simp] private theorem pc1062 :
    Artifact.submissionArtifact.instructionPC 1062 = 0x7ba := by decide
@[simp] private theorem pc1063 :
    Artifact.submissionArtifact.instructionPC 1063 = 0x7bc := by decide
@[simp] private theorem pc1064 :
    Artifact.submissionArtifact.instructionPC 1064 = 0x7be := by decide
@[simp] private theorem pc1065 :
    Artifact.submissionArtifact.instructionPC 1065 = 0x7bf := by decide
@[simp] private theorem pc1066 :
    Artifact.submissionArtifact.instructionPC 1066 = 0x7c1 := by decide
@[simp] private theorem pc1067 :
    Artifact.submissionArtifact.instructionPC 1067 = 0x7c4 := by decide

@[simp] private theorem valid7C5 :
    Decode.isValidJumpDest submissionBytecode 0x7c5 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1068 (by rfl)

/-- Wrapper entry for round 7: prior return PC with outer stack. -/
def entry7 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x7b5
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 7. -/
def roundEntry7 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 7)
    (UInt256.ofNat 9) (UInt256.ofNat 0) (UInt256.ofNat 0x7c5)
    ([messageOffset, outerReturn] ++ rest)

theorem run7 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path7
      (entry7 s messageOffset outerReturn rest) =
        some (roundEntry7 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x7c5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x7c5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 9, UInt256.ofNat 0, UInt256.ofNat 0x7c5,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 7, UInt256.ofNat 9, UInt256.ofNat 0,
      UInt256.ofNat 0x7c5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 7, UInt256.ofNat 9,
      UInt256.ofNat 0, UInt256.ofNat 0x7c5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 7,
      UInt256.ofNat 9, UInt256.ofNat 0, UInt256.ofNat 0x7c5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 7, UInt256.ofNat 9, UInt256.ofNat 0,
      UInt256.ofNat 0x7c5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path7, ImmediateWrapper.wrapperPath, site7, entry7,
      roundEntry7, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1059, pc1060, pc1061, pc1062, pc1063, pc1064, pc1065, pc1066, pc1067,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper7 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry7 s messageOffset outerReturn rest)
      (roundEntry7 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path7
  · simpa [entry7, Artifact.submissionArtifact] using hcode
  · simpa [entry7, State.fork] using hfork
  · exact run7 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry7] using hrun
  · simpa [entry7] using hnp

/-- One full helper call for round 7: nine-instruction setup plus verified round body. -/
def gasSteps_round7 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry7 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 7)
        (UInt256.ofNat 9) (UInt256.ofNat 0) (UInt256.ofNat 0x7c5)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper7 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 7) (UInt256.ofNat 9) (UInt256.ofNat 0)
    (UInt256.ofNat 0x7c5) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid7C5
  have hEq : roundEntry7 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 7)
        (UInt256.ofNat 9) (UInt256.ofNat 0) (UInt256.ofNat 0x7c5)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 7. -/
def wrapperWork7 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path7

theorem wrapperWork7_eq : wrapperWork7 = 28 := by rfl

/-- Body wrapper site for left round 8. Call indices 1069--1076, return 1077. -/
def site8 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1069
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x7d5
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 11
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 8
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 8: leading `JUMPDEST` at 1068 then eight-instruction call. -/
def path8 : List Located :=
  ⟨1068, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site8
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1068 :
    Artifact.submissionArtifact.instructionPC 1068 = 0x7c5 := by decide
@[simp] private theorem pc1069 :
    Artifact.submissionArtifact.instructionPC 1069 = 0x7c6 := by decide
@[simp] private theorem pc1070 :
    Artifact.submissionArtifact.instructionPC 1070 = 0x7c9 := by decide
@[simp] private theorem pc1071 :
    Artifact.submissionArtifact.instructionPC 1071 = 0x7ca := by decide
@[simp] private theorem pc1072 :
    Artifact.submissionArtifact.instructionPC 1072 = 0x7cc := by decide
@[simp] private theorem pc1073 :
    Artifact.submissionArtifact.instructionPC 1073 = 0x7ce := by decide
@[simp] private theorem pc1074 :
    Artifact.submissionArtifact.instructionPC 1074 = 0x7cf := by decide
@[simp] private theorem pc1075 :
    Artifact.submissionArtifact.instructionPC 1075 = 0x7d1 := by decide
@[simp] private theorem pc1076 :
    Artifact.submissionArtifact.instructionPC 1076 = 0x7d4 := by decide

@[simp] private theorem valid7D5 :
    Decode.isValidJumpDest submissionBytecode 0x7d5 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1077 (by rfl)

/-- Wrapper entry for round 8: prior return PC with outer stack. -/
def entry8 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x7c5
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 8. -/
def roundEntry8 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 8)
    (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x7d5)
    ([messageOffset, outerReturn] ++ rest)

theorem run8 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path8
      (entry8 s messageOffset outerReturn rest) =
        some (roundEntry8 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x7d5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x7d5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 11, UInt256.ofNat 0, UInt256.ofNat 0x7d5,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 8, UInt256.ofNat 11, UInt256.ofNat 0,
      UInt256.ofNat 0x7d5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 8, UInt256.ofNat 11,
      UInt256.ofNat 0, UInt256.ofNat 0x7d5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 8,
      UInt256.ofNat 11, UInt256.ofNat 0, UInt256.ofNat 0x7d5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 8, UInt256.ofNat 11, UInt256.ofNat 0,
      UInt256.ofNat 0x7d5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path8, ImmediateWrapper.wrapperPath, site8, entry8,
      roundEntry8, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1068, pc1069, pc1070, pc1071, pc1072, pc1073, pc1074, pc1075, pc1076,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper8 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry8 s messageOffset outerReturn rest)
      (roundEntry8 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path8
  · simpa [entry8, Artifact.submissionArtifact] using hcode
  · simpa [entry8, State.fork] using hfork
  · exact run8 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry8] using hrun
  · simpa [entry8] using hnp

/-- One full helper call for round 8: nine-instruction setup plus verified round body. -/
def gasSteps_round8 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry8 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 8)
        (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x7d5)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper8 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 8) (UInt256.ofNat 11) (UInt256.ofNat 0)
    (UInt256.ofNat 0x7d5) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid7D5
  have hEq : roundEntry8 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 8)
        (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x7d5)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 8. -/
def wrapperWork8 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path8

theorem wrapperWork8_eq : wrapperWork8 = 28 := by rfl

/-- Body wrapper site for left round 9. Call indices 1078--1085, return 1086. -/
def site9 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1078
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x7e5
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 13
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 9
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 9: leading `JUMPDEST` at 1077 then eight-instruction call. -/
def path9 : List Located :=
  ⟨1077, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site9
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1077 :
    Artifact.submissionArtifact.instructionPC 1077 = 0x7d5 := by decide
@[simp] private theorem pc1078 :
    Artifact.submissionArtifact.instructionPC 1078 = 0x7d6 := by decide
@[simp] private theorem pc1079 :
    Artifact.submissionArtifact.instructionPC 1079 = 0x7d9 := by decide
@[simp] private theorem pc1080 :
    Artifact.submissionArtifact.instructionPC 1080 = 0x7da := by decide
@[simp] private theorem pc1081 :
    Artifact.submissionArtifact.instructionPC 1081 = 0x7dc := by decide
@[simp] private theorem pc1082 :
    Artifact.submissionArtifact.instructionPC 1082 = 0x7de := by decide
@[simp] private theorem pc1083 :
    Artifact.submissionArtifact.instructionPC 1083 = 0x7df := by decide
@[simp] private theorem pc1084 :
    Artifact.submissionArtifact.instructionPC 1084 = 0x7e1 := by decide
@[simp] private theorem pc1085 :
    Artifact.submissionArtifact.instructionPC 1085 = 0x7e4 := by decide

@[simp] private theorem valid7E5 :
    Decode.isValidJumpDest submissionBytecode 0x7e5 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1086 (by rfl)

/-- Wrapper entry for round 9: prior return PC with outer stack. -/
def entry9 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x7d5
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 9. -/
def roundEntry9 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 9)
    (UInt256.ofNat 13) (UInt256.ofNat 0) (UInt256.ofNat 0x7e5)
    ([messageOffset, outerReturn] ++ rest)

theorem run9 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path9
      (entry9 s messageOffset outerReturn rest) =
        some (roundEntry9 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x7e5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x7e5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 13, UInt256.ofNat 0, UInt256.ofNat 0x7e5,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 9, UInt256.ofNat 13, UInt256.ofNat 0,
      UInt256.ofNat 0x7e5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 9, UInt256.ofNat 13,
      UInt256.ofNat 0, UInt256.ofNat 0x7e5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 9,
      UInt256.ofNat 13, UInt256.ofNat 0, UInt256.ofNat 0x7e5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 9, UInt256.ofNat 13, UInt256.ofNat 0,
      UInt256.ofNat 0x7e5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path9, ImmediateWrapper.wrapperPath, site9, entry9,
      roundEntry9, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1077, pc1078, pc1079, pc1080, pc1081, pc1082, pc1083, pc1084, pc1085,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper9 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry9 s messageOffset outerReturn rest)
      (roundEntry9 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path9
  · simpa [entry9, Artifact.submissionArtifact] using hcode
  · simpa [entry9, State.fork] using hfork
  · exact run9 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry9] using hrun
  · simpa [entry9] using hnp

/-- One full helper call for round 9: nine-instruction setup plus verified round body. -/
def gasSteps_round9 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry9 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 9)
        (UInt256.ofNat 13) (UInt256.ofNat 0) (UInt256.ofNat 0x7e5)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper9 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 9) (UInt256.ofNat 13) (UInt256.ofNat 0)
    (UInt256.ofNat 0x7e5) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid7E5
  have hEq : roundEntry9 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 9)
        (UInt256.ofNat 13) (UInt256.ofNat 0) (UInt256.ofNat 0x7e5)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 9. -/
def wrapperWork9 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path9

theorem wrapperWork9_eq : wrapperWork9 = 28 := by rfl

/-- Body wrapper site for left round 10. Call indices 1087--1094, return 1095. -/
def site10 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1087
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x7f5
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 14
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 10
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 10: leading `JUMPDEST` at 1086 then eight-instruction call. -/
def path10 : List Located :=
  ⟨1086, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site10
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1086 :
    Artifact.submissionArtifact.instructionPC 1086 = 0x7e5 := by decide
@[simp] private theorem pc1087 :
    Artifact.submissionArtifact.instructionPC 1087 = 0x7e6 := by decide
@[simp] private theorem pc1088 :
    Artifact.submissionArtifact.instructionPC 1088 = 0x7e9 := by decide
@[simp] private theorem pc1089 :
    Artifact.submissionArtifact.instructionPC 1089 = 0x7ea := by decide
@[simp] private theorem pc1090 :
    Artifact.submissionArtifact.instructionPC 1090 = 0x7ec := by decide
@[simp] private theorem pc1091 :
    Artifact.submissionArtifact.instructionPC 1091 = 0x7ee := by decide
@[simp] private theorem pc1092 :
    Artifact.submissionArtifact.instructionPC 1092 = 0x7ef := by decide
@[simp] private theorem pc1093 :
    Artifact.submissionArtifact.instructionPC 1093 = 0x7f1 := by decide
@[simp] private theorem pc1094 :
    Artifact.submissionArtifact.instructionPC 1094 = 0x7f4 := by decide

@[simp] private theorem valid7F5 :
    Decode.isValidJumpDest submissionBytecode 0x7f5 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1095 (by rfl)

/-- Wrapper entry for round 10: prior return PC with outer stack. -/
def entry10 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x7e5
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 10. -/
def roundEntry10 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 10)
    (UInt256.ofNat 14) (UInt256.ofNat 0) (UInt256.ofNat 0x7f5)
    ([messageOffset, outerReturn] ++ rest)

theorem run10 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path10
      (entry10 s messageOffset outerReturn rest) =
        some (roundEntry10 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x7f5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x7f5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 14, UInt256.ofNat 0, UInt256.ofNat 0x7f5,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 10, UInt256.ofNat 14, UInt256.ofNat 0,
      UInt256.ofNat 0x7f5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 10, UInt256.ofNat 14,
      UInt256.ofNat 0, UInt256.ofNat 0x7f5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 10,
      UInt256.ofNat 14, UInt256.ofNat 0, UInt256.ofNat 0x7f5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 10, UInt256.ofNat 14, UInt256.ofNat 0,
      UInt256.ofNat 0x7f5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path10, ImmediateWrapper.wrapperPath, site10, entry10,
      roundEntry10, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1086, pc1087, pc1088, pc1089, pc1090, pc1091, pc1092, pc1093, pc1094,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper10 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry10 s messageOffset outerReturn rest)
      (roundEntry10 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path10
  · simpa [entry10, Artifact.submissionArtifact] using hcode
  · simpa [entry10, State.fork] using hfork
  · exact run10 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry10] using hrun
  · simpa [entry10] using hnp

/-- One full helper call for round 10: nine-instruction setup plus verified round body. -/
def gasSteps_round10 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry10 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 10)
        (UInt256.ofNat 14) (UInt256.ofNat 0) (UInt256.ofNat 0x7f5)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper10 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 10) (UInt256.ofNat 14) (UInt256.ofNat 0)
    (UInt256.ofNat 0x7f5) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid7F5
  have hEq : roundEntry10 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 10)
        (UInt256.ofNat 14) (UInt256.ofNat 0) (UInt256.ofNat 0x7f5)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 10. -/
def wrapperWork10 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path10

theorem wrapperWork10_eq : wrapperWork10 = 28 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0B
