import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Immediate wrapper group0 part C (left rounds 11,12,13,14,15)

Rounds 11,12,13,14,15 each start by executing the prior return `JUMPDEST`,
then the same eight-instruction immediate call around helper `0x114`.
In this group `base=0xc0`, `j=0`, `K=0`, `r[k]=k`, `s[k]` pinned.
Each site composes its pushes with the unchanged `RoundTrace.gasSteps_round`.
Generated deterministically; see `benchmark-results/ripemd160/h09/gen_h09_group0.py`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0C

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

/-- Body wrapper site for left round 11. Call indices 1096--1103, return 1104. -/
def site11 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1096
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x805
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 15
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 11
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 11: leading `JUMPDEST` at 1095 then eight-instruction call. -/
def path11 : List Located :=
  ⟨1095, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site11
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1095 :
    Artifact.submissionArtifact.instructionPC 1095 = 0x7f5 := by decide
@[simp] private theorem pc1096 :
    Artifact.submissionArtifact.instructionPC 1096 = 0x7f6 := by decide
@[simp] private theorem pc1097 :
    Artifact.submissionArtifact.instructionPC 1097 = 0x7f9 := by decide
@[simp] private theorem pc1098 :
    Artifact.submissionArtifact.instructionPC 1098 = 0x7fa := by decide
@[simp] private theorem pc1099 :
    Artifact.submissionArtifact.instructionPC 1099 = 0x7fc := by decide
@[simp] private theorem pc1100 :
    Artifact.submissionArtifact.instructionPC 1100 = 0x7fe := by decide
@[simp] private theorem pc1101 :
    Artifact.submissionArtifact.instructionPC 1101 = 0x7ff := by decide
@[simp] private theorem pc1102 :
    Artifact.submissionArtifact.instructionPC 1102 = 0x801 := by decide
@[simp] private theorem pc1103 :
    Artifact.submissionArtifact.instructionPC 1103 = 0x804 := by decide

@[simp] private theorem valid805 :
    Decode.isValidJumpDest submissionBytecode 0x805 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1104 (by rfl)

/-- Wrapper entry for round 11: prior return PC with outer stack. -/
def entry11 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x7f5
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 11. -/
def roundEntry11 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 11)
    (UInt256.ofNat 15) (UInt256.ofNat 0) (UInt256.ofNat 0x805)
    ([messageOffset, outerReturn] ++ rest)

theorem run11 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path11
      (entry11 s messageOffset outerReturn rest) =
        some (roundEntry11 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x805, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x805, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 15, UInt256.ofNat 0, UInt256.ofNat 0x805,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 11, UInt256.ofNat 15, UInt256.ofNat 0,
      UInt256.ofNat 0x805, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 11, UInt256.ofNat 15,
      UInt256.ofNat 0, UInt256.ofNat 0x805, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 11,
      UInt256.ofNat 15, UInt256.ofNat 0, UInt256.ofNat 0x805, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 11, UInt256.ofNat 15, UInt256.ofNat 0,
      UInt256.ofNat 0x805, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path11, ImmediateWrapper.wrapperPath, site11, entry11,
      roundEntry11, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1095, pc1096, pc1097, pc1098, pc1099, pc1100, pc1101, pc1102, pc1103,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper11 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry11 s messageOffset outerReturn rest)
      (roundEntry11 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path11
  · simpa [entry11, Artifact.submissionArtifact] using hcode
  · simpa [entry11, State.fork] using hfork
  · exact run11 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry11] using hrun
  · simpa [entry11] using hnp

/-- One full helper call for round 11: nine-instruction setup plus verified round body. -/
def gasSteps_round11 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry11 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 11)
        (UInt256.ofNat 15) (UInt256.ofNat 0) (UInt256.ofNat 0x805)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper11 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 11) (UInt256.ofNat 15) (UInt256.ofNat 0)
    (UInt256.ofNat 0x805) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid805
  have hEq : roundEntry11 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 11)
        (UInt256.ofNat 15) (UInt256.ofNat 0) (UInt256.ofNat 0x805)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 11. -/
def wrapperWork11 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path11

theorem wrapperWork11_eq : wrapperWork11 = 28 := by rfl

/-- Body wrapper site for left round 12. Call indices 1105--1112, return 1113. -/
def site12 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1105
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x815
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 6
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 12
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 12: leading `JUMPDEST` at 1104 then eight-instruction call. -/
def path12 : List Located :=
  ⟨1104, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site12
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1104 :
    Artifact.submissionArtifact.instructionPC 1104 = 0x805 := by decide
@[simp] private theorem pc1105 :
    Artifact.submissionArtifact.instructionPC 1105 = 0x806 := by decide
@[simp] private theorem pc1106 :
    Artifact.submissionArtifact.instructionPC 1106 = 0x809 := by decide
@[simp] private theorem pc1107 :
    Artifact.submissionArtifact.instructionPC 1107 = 0x80a := by decide
@[simp] private theorem pc1108 :
    Artifact.submissionArtifact.instructionPC 1108 = 0x80c := by decide
@[simp] private theorem pc1109 :
    Artifact.submissionArtifact.instructionPC 1109 = 0x80e := by decide
@[simp] private theorem pc1110 :
    Artifact.submissionArtifact.instructionPC 1110 = 0x80f := by decide
@[simp] private theorem pc1111 :
    Artifact.submissionArtifact.instructionPC 1111 = 0x811 := by decide
@[simp] private theorem pc1112 :
    Artifact.submissionArtifact.instructionPC 1112 = 0x814 := by decide

@[simp] private theorem valid815 :
    Decode.isValidJumpDest submissionBytecode 0x815 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1113 (by rfl)

/-- Wrapper entry for round 12: prior return PC with outer stack. -/
def entry12 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x805
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 12. -/
def roundEntry12 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 12)
    (UInt256.ofNat 6) (UInt256.ofNat 0) (UInt256.ofNat 0x815)
    ([messageOffset, outerReturn] ++ rest)

theorem run12 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path12
      (entry12 s messageOffset outerReturn rest) =
        some (roundEntry12 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x815, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x815, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 6, UInt256.ofNat 0, UInt256.ofNat 0x815,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 12, UInt256.ofNat 6, UInt256.ofNat 0,
      UInt256.ofNat 0x815, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 12, UInt256.ofNat 6,
      UInt256.ofNat 0, UInt256.ofNat 0x815, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 12,
      UInt256.ofNat 6, UInt256.ofNat 0, UInt256.ofNat 0x815, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 12, UInt256.ofNat 6, UInt256.ofNat 0,
      UInt256.ofNat 0x815, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path12, ImmediateWrapper.wrapperPath, site12, entry12,
      roundEntry12, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1104, pc1105, pc1106, pc1107, pc1108, pc1109, pc1110, pc1111, pc1112,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper12 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry12 s messageOffset outerReturn rest)
      (roundEntry12 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path12
  · simpa [entry12, Artifact.submissionArtifact] using hcode
  · simpa [entry12, State.fork] using hfork
  · exact run12 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry12] using hrun
  · simpa [entry12] using hnp

/-- One full helper call for round 12: nine-instruction setup plus verified round body. -/
def gasSteps_round12 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry12 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 12)
        (UInt256.ofNat 6) (UInt256.ofNat 0) (UInt256.ofNat 0x815)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper12 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 12) (UInt256.ofNat 6) (UInt256.ofNat 0)
    (UInt256.ofNat 0x815) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid815
  have hEq : roundEntry12 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 12)
        (UInt256.ofNat 6) (UInt256.ofNat 0) (UInt256.ofNat 0x815)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 12. -/
def wrapperWork12 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path12

theorem wrapperWork12_eq : wrapperWork12 = 28 := by rfl

/-- Body wrapper site for left round 13. Call indices 1114--1121, return 1122. -/
def site13 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1114
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x825
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 7
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 13
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 13: leading `JUMPDEST` at 1113 then eight-instruction call. -/
def path13 : List Located :=
  ⟨1113, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site13
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1113 :
    Artifact.submissionArtifact.instructionPC 1113 = 0x815 := by decide
@[simp] private theorem pc1114 :
    Artifact.submissionArtifact.instructionPC 1114 = 0x816 := by decide
@[simp] private theorem pc1115 :
    Artifact.submissionArtifact.instructionPC 1115 = 0x819 := by decide
@[simp] private theorem pc1116 :
    Artifact.submissionArtifact.instructionPC 1116 = 0x81a := by decide
@[simp] private theorem pc1117 :
    Artifact.submissionArtifact.instructionPC 1117 = 0x81c := by decide
@[simp] private theorem pc1118 :
    Artifact.submissionArtifact.instructionPC 1118 = 0x81e := by decide
@[simp] private theorem pc1119 :
    Artifact.submissionArtifact.instructionPC 1119 = 0x81f := by decide
@[simp] private theorem pc1120 :
    Artifact.submissionArtifact.instructionPC 1120 = 0x821 := by decide
@[simp] private theorem pc1121 :
    Artifact.submissionArtifact.instructionPC 1121 = 0x824 := by decide

@[simp] private theorem valid825 :
    Decode.isValidJumpDest submissionBytecode 0x825 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1122 (by rfl)

/-- Wrapper entry for round 13: prior return PC with outer stack. -/
def entry13 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x815
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 13. -/
def roundEntry13 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 13)
    (UInt256.ofNat 7) (UInt256.ofNat 0) (UInt256.ofNat 0x825)
    ([messageOffset, outerReturn] ++ rest)

theorem run13 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path13
      (entry13 s messageOffset outerReturn rest) =
        some (roundEntry13 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x825, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x825, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 7, UInt256.ofNat 0, UInt256.ofNat 0x825,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 13, UInt256.ofNat 7, UInt256.ofNat 0,
      UInt256.ofNat 0x825, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 13, UInt256.ofNat 7,
      UInt256.ofNat 0, UInt256.ofNat 0x825, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 13,
      UInt256.ofNat 7, UInt256.ofNat 0, UInt256.ofNat 0x825, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 13, UInt256.ofNat 7, UInt256.ofNat 0,
      UInt256.ofNat 0x825, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path13, ImmediateWrapper.wrapperPath, site13, entry13,
      roundEntry13, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1113, pc1114, pc1115, pc1116, pc1117, pc1118, pc1119, pc1120, pc1121,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper13 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry13 s messageOffset outerReturn rest)
      (roundEntry13 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path13
  · simpa [entry13, Artifact.submissionArtifact] using hcode
  · simpa [entry13, State.fork] using hfork
  · exact run13 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry13] using hrun
  · simpa [entry13] using hnp

/-- One full helper call for round 13: nine-instruction setup plus verified round body. -/
def gasSteps_round13 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry13 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 13)
        (UInt256.ofNat 7) (UInt256.ofNat 0) (UInt256.ofNat 0x825)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper13 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 13) (UInt256.ofNat 7) (UInt256.ofNat 0)
    (UInt256.ofNat 0x825) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid825
  have hEq : roundEntry13 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 13)
        (UInt256.ofNat 7) (UInt256.ofNat 0) (UInt256.ofNat 0x825)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 13. -/
def wrapperWork13 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path13

theorem wrapperWork13_eq : wrapperWork13 = 28 := by rfl

/-- Body wrapper site for left round 14. Call indices 1123--1130, return 1131. -/
def site14 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1123
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x835
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 9
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 14
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 14: leading `JUMPDEST` at 1122 then eight-instruction call. -/
def path14 : List Located :=
  ⟨1122, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site14
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1122 :
    Artifact.submissionArtifact.instructionPC 1122 = 0x825 := by decide
@[simp] private theorem pc1123 :
    Artifact.submissionArtifact.instructionPC 1123 = 0x826 := by decide
@[simp] private theorem pc1124 :
    Artifact.submissionArtifact.instructionPC 1124 = 0x829 := by decide
@[simp] private theorem pc1125 :
    Artifact.submissionArtifact.instructionPC 1125 = 0x82a := by decide
@[simp] private theorem pc1126 :
    Artifact.submissionArtifact.instructionPC 1126 = 0x82c := by decide
@[simp] private theorem pc1127 :
    Artifact.submissionArtifact.instructionPC 1127 = 0x82e := by decide
@[simp] private theorem pc1128 :
    Artifact.submissionArtifact.instructionPC 1128 = 0x82f := by decide
@[simp] private theorem pc1129 :
    Artifact.submissionArtifact.instructionPC 1129 = 0x831 := by decide
@[simp] private theorem pc1130 :
    Artifact.submissionArtifact.instructionPC 1130 = 0x834 := by decide

@[simp] private theorem valid835 :
    Decode.isValidJumpDest submissionBytecode 0x835 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1131 (by rfl)

/-- Wrapper entry for round 14: prior return PC with outer stack. -/
def entry14 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x825
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 14. -/
def roundEntry14 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 14)
    (UInt256.ofNat 9) (UInt256.ofNat 0) (UInt256.ofNat 0x835)
    ([messageOffset, outerReturn] ++ rest)

theorem run14 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path14
      (entry14 s messageOffset outerReturn rest) =
        some (roundEntry14 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x835, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x835, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 9, UInt256.ofNat 0, UInt256.ofNat 0x835,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 14, UInt256.ofNat 9, UInt256.ofNat 0,
      UInt256.ofNat 0x835, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 14, UInt256.ofNat 9,
      UInt256.ofNat 0, UInt256.ofNat 0x835, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 14,
      UInt256.ofNat 9, UInt256.ofNat 0, UInt256.ofNat 0x835, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 14, UInt256.ofNat 9, UInt256.ofNat 0,
      UInt256.ofNat 0x835, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path14, ImmediateWrapper.wrapperPath, site14, entry14,
      roundEntry14, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1122, pc1123, pc1124, pc1125, pc1126, pc1127, pc1128, pc1129, pc1130,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper14 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry14 s messageOffset outerReturn rest)
      (roundEntry14 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path14
  · simpa [entry14, Artifact.submissionArtifact] using hcode
  · simpa [entry14, State.fork] using hfork
  · exact run14 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry14] using hrun
  · simpa [entry14] using hnp

/-- One full helper call for round 14: nine-instruction setup plus verified round body. -/
def gasSteps_round14 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry14 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 14)
        (UInt256.ofNat 9) (UInt256.ofNat 0) (UInt256.ofNat 0x835)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper14 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 14) (UInt256.ofNat 9) (UInt256.ofNat 0)
    (UInt256.ofNat 0x835) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid835
  have hEq : roundEntry14 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 14)
        (UInt256.ofNat 9) (UInt256.ofNat 0) (UInt256.ofNat 0x835)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 14. -/
def wrapperWork14 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path14

theorem wrapperWork14_eq : wrapperWork14 = 28 := by rfl

/-- Body wrapper site for left round 15. Call indices 1132--1139, return 1140. -/
def site15 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1132
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x845
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 8
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 15
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 15: leading `JUMPDEST` at 1131 then eight-instruction call. -/
def path15 : List Located :=
  ⟨1131, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site15
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1131 :
    Artifact.submissionArtifact.instructionPC 1131 = 0x835 := by decide
@[simp] private theorem pc1132 :
    Artifact.submissionArtifact.instructionPC 1132 = 0x836 := by decide
@[simp] private theorem pc1133 :
    Artifact.submissionArtifact.instructionPC 1133 = 0x839 := by decide
@[simp] private theorem pc1134 :
    Artifact.submissionArtifact.instructionPC 1134 = 0x83a := by decide
@[simp] private theorem pc1135 :
    Artifact.submissionArtifact.instructionPC 1135 = 0x83c := by decide
@[simp] private theorem pc1136 :
    Artifact.submissionArtifact.instructionPC 1136 = 0x83e := by decide
@[simp] private theorem pc1137 :
    Artifact.submissionArtifact.instructionPC 1137 = 0x83f := by decide
@[simp] private theorem pc1138 :
    Artifact.submissionArtifact.instructionPC 1138 = 0x841 := by decide
@[simp] private theorem pc1139 :
    Artifact.submissionArtifact.instructionPC 1139 = 0x844 := by decide

@[simp] private theorem valid845 :
    Decode.isValidJumpDest submissionBytecode 0x845 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1140 (by rfl)

/-- Wrapper entry for round 15: prior return PC with outer stack. -/
def entry15 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x835
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 15. -/
def roundEntry15 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 15)
    (UInt256.ofNat 8) (UInt256.ofNat 0) (UInt256.ofNat 0x845)
    ([messageOffset, outerReturn] ++ rest)

theorem run15 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path15
      (entry15 s messageOffset outerReturn rest) =
        some (roundEntry15 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x845, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x845, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 8, UInt256.ofNat 0, UInt256.ofNat 0x845,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 15, UInt256.ofNat 8, UInt256.ofNat 0,
      UInt256.ofNat 0x845, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 15, UInt256.ofNat 8,
      UInt256.ofNat 0, UInt256.ofNat 0x845, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 15,
      UInt256.ofNat 8, UInt256.ofNat 0, UInt256.ofNat 0x845, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 15, UInt256.ofNat 8, UInt256.ofNat 0,
      UInt256.ofNat 0x845, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path15, ImmediateWrapper.wrapperPath, site15, entry15,
      roundEntry15, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1131, pc1132, pc1133, pc1134, pc1135, pc1136, pc1137, pc1138, pc1139,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper15 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry15 s messageOffset outerReturn rest)
      (roundEntry15 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path15
  · simpa [entry15, Artifact.submissionArtifact] using hcode
  · simpa [entry15, State.fork] using hfork
  · exact run15 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry15] using hrun
  · simpa [entry15] using hnp

/-- One full helper call for round 15: nine-instruction setup plus verified round body. -/
def gasSteps_round15 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry15 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 15)
        (UInt256.ofNat 8) (UInt256.ofNat 0) (UInt256.ofNat 0x845)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper15 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 15) (UInt256.ofNat 8) (UInt256.ofNat 0)
    (UInt256.ofNat 0x845) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid845
  have hEq : roundEntry15 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 15)
        (UInt256.ofNat 8) (UInt256.ofNat 0) (UInt256.ofNat 0x845)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 15. -/
def wrapperWork15 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path15

theorem wrapperWork15_eq : wrapperWork15 = 28 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0C
