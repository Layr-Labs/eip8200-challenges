import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Immediate wrapper group0 part A (left rounds 1,2,3,4,5)

Rounds 1,2,3,4,5 each start by executing the prior return `JUMPDEST`,
then the same eight-instruction immediate call around helper `0x114`.
In this group `base=0xc0`, `j=0`, `K=0`, `r[k]=k`, `s[k]` pinned.
Each site composes its pushes with the unchanged `RoundTrace.gasSteps_round`.
Generated deterministically; see `benchmark-results/ripemd160/h09/gen_h09_group0.py`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0A

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

/-- Body wrapper site for left round 1. Call indices 1006--1013, return 1014. -/
def site1 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1006
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x765
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 14
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 1
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 1: leading `JUMPDEST` at 1005 then eight-instruction call. -/
def path1 : List Located :=
  ⟨1005, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site1
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1005 :
    Artifact.submissionArtifact.instructionPC 1005 = 0x755 := by decide
@[simp] private theorem pc1006 :
    Artifact.submissionArtifact.instructionPC 1006 = 0x756 := by decide
@[simp] private theorem pc1007 :
    Artifact.submissionArtifact.instructionPC 1007 = 0x759 := by decide
@[simp] private theorem pc1008 :
    Artifact.submissionArtifact.instructionPC 1008 = 0x75a := by decide
@[simp] private theorem pc1009 :
    Artifact.submissionArtifact.instructionPC 1009 = 0x75c := by decide
@[simp] private theorem pc1010 :
    Artifact.submissionArtifact.instructionPC 1010 = 0x75e := by decide
@[simp] private theorem pc1011 :
    Artifact.submissionArtifact.instructionPC 1011 = 0x75f := by decide
@[simp] private theorem pc1012 :
    Artifact.submissionArtifact.instructionPC 1012 = 0x761 := by decide
@[simp] private theorem pc1013 :
    Artifact.submissionArtifact.instructionPC 1013 = 0x764 := by decide

@[simp] private theorem valid765 :
    Decode.isValidJumpDest submissionBytecode 0x765 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1014 (by rfl)

/-- Wrapper entry for round 1: prior return PC with outer stack. -/
def entry1 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x755
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 1. -/
def roundEntry1 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 1)
    (UInt256.ofNat 14) (UInt256.ofNat 0) (UInt256.ofNat 0x765)
    ([messageOffset, outerReturn] ++ rest)

theorem run1 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path1
      (entry1 s messageOffset outerReturn rest) =
        some (roundEntry1 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x765, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x765, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 14, UInt256.ofNat 0, UInt256.ofNat 0x765,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 1, UInt256.ofNat 14, UInt256.ofNat 0,
      UInt256.ofNat 0x765, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 1, UInt256.ofNat 14,
      UInt256.ofNat 0, UInt256.ofNat 0x765, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 1,
      UInt256.ofNat 14, UInt256.ofNat 0, UInt256.ofNat 0x765, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 1, UInt256.ofNat 14, UInt256.ofNat 0,
      UInt256.ofNat 0x765, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path1, ImmediateWrapper.wrapperPath, site1, entry1,
      roundEntry1, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1005, pc1006, pc1007, pc1008, pc1009, pc1010, pc1011, pc1012, pc1013,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper1 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry1 s messageOffset outerReturn rest)
      (roundEntry1 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path1
  · simpa [entry1, Artifact.submissionArtifact] using hcode
  · simpa [entry1, State.fork] using hfork
  · exact run1 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry1] using hrun
  · simpa [entry1] using hnp

/-- One full helper call for round 1: nine-instruction setup plus verified round body. -/
def gasSteps_round1 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry1 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 1)
        (UInt256.ofNat 14) (UInt256.ofNat 0) (UInt256.ofNat 0x765)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper1 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 1) (UInt256.ofNat 14) (UInt256.ofNat 0)
    (UInt256.ofNat 0x765) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid765
  have hEq : roundEntry1 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 1)
        (UInt256.ofNat 14) (UInt256.ofNat 0) (UInt256.ofNat 0x765)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 1. -/
def wrapperWork1 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path1

theorem wrapperWork1_eq : wrapperWork1 = 28 := by rfl

/-- Body wrapper site for left round 2. Call indices 1015--1022, return 1023. -/
def site2 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1015
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x775
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 15
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 2
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 2: leading `JUMPDEST` at 1014 then eight-instruction call. -/
def path2 : List Located :=
  ⟨1014, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site2
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1014 :
    Artifact.submissionArtifact.instructionPC 1014 = 0x765 := by decide
@[simp] private theorem pc1015 :
    Artifact.submissionArtifact.instructionPC 1015 = 0x766 := by decide
@[simp] private theorem pc1016 :
    Artifact.submissionArtifact.instructionPC 1016 = 0x769 := by decide
@[simp] private theorem pc1017 :
    Artifact.submissionArtifact.instructionPC 1017 = 0x76a := by decide
@[simp] private theorem pc1018 :
    Artifact.submissionArtifact.instructionPC 1018 = 0x76c := by decide
@[simp] private theorem pc1019 :
    Artifact.submissionArtifact.instructionPC 1019 = 0x76e := by decide
@[simp] private theorem pc1020 :
    Artifact.submissionArtifact.instructionPC 1020 = 0x76f := by decide
@[simp] private theorem pc1021 :
    Artifact.submissionArtifact.instructionPC 1021 = 0x771 := by decide
@[simp] private theorem pc1022 :
    Artifact.submissionArtifact.instructionPC 1022 = 0x774 := by decide

@[simp] private theorem valid775 :
    Decode.isValidJumpDest submissionBytecode 0x775 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1023 (by rfl)

/-- Wrapper entry for round 2: prior return PC with outer stack. -/
def entry2 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x765
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 2. -/
def roundEntry2 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 2)
    (UInt256.ofNat 15) (UInt256.ofNat 0) (UInt256.ofNat 0x775)
    ([messageOffset, outerReturn] ++ rest)

theorem run2 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path2
      (entry2 s messageOffset outerReturn rest) =
        some (roundEntry2 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x775, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x775, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 15, UInt256.ofNat 0, UInt256.ofNat 0x775,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 2, UInt256.ofNat 15, UInt256.ofNat 0,
      UInt256.ofNat 0x775, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 2, UInt256.ofNat 15,
      UInt256.ofNat 0, UInt256.ofNat 0x775, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 2,
      UInt256.ofNat 15, UInt256.ofNat 0, UInt256.ofNat 0x775, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 2, UInt256.ofNat 15, UInt256.ofNat 0,
      UInt256.ofNat 0x775, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path2, ImmediateWrapper.wrapperPath, site2, entry2,
      roundEntry2, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1014, pc1015, pc1016, pc1017, pc1018, pc1019, pc1020, pc1021, pc1022,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper2 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry2 s messageOffset outerReturn rest)
      (roundEntry2 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path2
  · simpa [entry2, Artifact.submissionArtifact] using hcode
  · simpa [entry2, State.fork] using hfork
  · exact run2 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry2] using hrun
  · simpa [entry2] using hnp

/-- One full helper call for round 2: nine-instruction setup plus verified round body. -/
def gasSteps_round2 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry2 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 2)
        (UInt256.ofNat 15) (UInt256.ofNat 0) (UInt256.ofNat 0x775)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper2 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 2) (UInt256.ofNat 15) (UInt256.ofNat 0)
    (UInt256.ofNat 0x775) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid775
  have hEq : roundEntry2 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 2)
        (UInt256.ofNat 15) (UInt256.ofNat 0) (UInt256.ofNat 0x775)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 2. -/
def wrapperWork2 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path2

theorem wrapperWork2_eq : wrapperWork2 = 28 := by rfl

/-- Body wrapper site for left round 3. Call indices 1024--1031, return 1032. -/
def site3 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1024
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x785
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 12
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 3
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 3: leading `JUMPDEST` at 1023 then eight-instruction call. -/
def path3 : List Located :=
  ⟨1023, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site3
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1023 :
    Artifact.submissionArtifact.instructionPC 1023 = 0x775 := by decide
@[simp] private theorem pc1024 :
    Artifact.submissionArtifact.instructionPC 1024 = 0x776 := by decide
@[simp] private theorem pc1025 :
    Artifact.submissionArtifact.instructionPC 1025 = 0x779 := by decide
@[simp] private theorem pc1026 :
    Artifact.submissionArtifact.instructionPC 1026 = 0x77a := by decide
@[simp] private theorem pc1027 :
    Artifact.submissionArtifact.instructionPC 1027 = 0x77c := by decide
@[simp] private theorem pc1028 :
    Artifact.submissionArtifact.instructionPC 1028 = 0x77e := by decide
@[simp] private theorem pc1029 :
    Artifact.submissionArtifact.instructionPC 1029 = 0x77f := by decide
@[simp] private theorem pc1030 :
    Artifact.submissionArtifact.instructionPC 1030 = 0x781 := by decide
@[simp] private theorem pc1031 :
    Artifact.submissionArtifact.instructionPC 1031 = 0x784 := by decide

@[simp] private theorem valid785 :
    Decode.isValidJumpDest submissionBytecode 0x785 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1032 (by rfl)

/-- Wrapper entry for round 3: prior return PC with outer stack. -/
def entry3 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x775
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 3. -/
def roundEntry3 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 3)
    (UInt256.ofNat 12) (UInt256.ofNat 0) (UInt256.ofNat 0x785)
    ([messageOffset, outerReturn] ++ rest)

theorem run3 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path3
      (entry3 s messageOffset outerReturn rest) =
        some (roundEntry3 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x785, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x785, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 12, UInt256.ofNat 0, UInt256.ofNat 0x785,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 3, UInt256.ofNat 12, UInt256.ofNat 0,
      UInt256.ofNat 0x785, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 3, UInt256.ofNat 12,
      UInt256.ofNat 0, UInt256.ofNat 0x785, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 3,
      UInt256.ofNat 12, UInt256.ofNat 0, UInt256.ofNat 0x785, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 3, UInt256.ofNat 12, UInt256.ofNat 0,
      UInt256.ofNat 0x785, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path3, ImmediateWrapper.wrapperPath, site3, entry3,
      roundEntry3, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1023, pc1024, pc1025, pc1026, pc1027, pc1028, pc1029, pc1030, pc1031,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper3 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry3 s messageOffset outerReturn rest)
      (roundEntry3 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path3
  · simpa [entry3, Artifact.submissionArtifact] using hcode
  · simpa [entry3, State.fork] using hfork
  · exact run3 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry3] using hrun
  · simpa [entry3] using hnp

/-- One full helper call for round 3: nine-instruction setup plus verified round body. -/
def gasSteps_round3 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry3 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 3)
        (UInt256.ofNat 12) (UInt256.ofNat 0) (UInt256.ofNat 0x785)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper3 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 3) (UInt256.ofNat 12) (UInt256.ofNat 0)
    (UInt256.ofNat 0x785) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid785
  have hEq : roundEntry3 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 3)
        (UInt256.ofNat 12) (UInt256.ofNat 0) (UInt256.ofNat 0x785)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 3. -/
def wrapperWork3 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path3

theorem wrapperWork3_eq : wrapperWork3 = 28 := by rfl

/-- Body wrapper site for left round 4. Call indices 1033--1040, return 1041. -/
def site4 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1033
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x795
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 5
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 4
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 4: leading `JUMPDEST` at 1032 then eight-instruction call. -/
def path4 : List Located :=
  ⟨1032, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site4
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1032 :
    Artifact.submissionArtifact.instructionPC 1032 = 0x785 := by decide
@[simp] private theorem pc1033 :
    Artifact.submissionArtifact.instructionPC 1033 = 0x786 := by decide
@[simp] private theorem pc1034 :
    Artifact.submissionArtifact.instructionPC 1034 = 0x789 := by decide
@[simp] private theorem pc1035 :
    Artifact.submissionArtifact.instructionPC 1035 = 0x78a := by decide
@[simp] private theorem pc1036 :
    Artifact.submissionArtifact.instructionPC 1036 = 0x78c := by decide
@[simp] private theorem pc1037 :
    Artifact.submissionArtifact.instructionPC 1037 = 0x78e := by decide
@[simp] private theorem pc1038 :
    Artifact.submissionArtifact.instructionPC 1038 = 0x78f := by decide
@[simp] private theorem pc1039 :
    Artifact.submissionArtifact.instructionPC 1039 = 0x791 := by decide
@[simp] private theorem pc1040 :
    Artifact.submissionArtifact.instructionPC 1040 = 0x794 := by decide

@[simp] private theorem valid795 :
    Decode.isValidJumpDest submissionBytecode 0x795 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1041 (by rfl)

/-- Wrapper entry for round 4: prior return PC with outer stack. -/
def entry4 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x785
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 4. -/
def roundEntry4 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 4)
    (UInt256.ofNat 5) (UInt256.ofNat 0) (UInt256.ofNat 0x795)
    ([messageOffset, outerReturn] ++ rest)

theorem run4 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path4
      (entry4 s messageOffset outerReturn rest) =
        some (roundEntry4 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x795, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x795, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 5, UInt256.ofNat 0, UInt256.ofNat 0x795,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 4, UInt256.ofNat 5, UInt256.ofNat 0,
      UInt256.ofNat 0x795, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 4, UInt256.ofNat 5,
      UInt256.ofNat 0, UInt256.ofNat 0x795, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 4,
      UInt256.ofNat 5, UInt256.ofNat 0, UInt256.ofNat 0x795, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 4, UInt256.ofNat 5, UInt256.ofNat 0,
      UInt256.ofNat 0x795, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path4, ImmediateWrapper.wrapperPath, site4, entry4,
      roundEntry4, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1032, pc1033, pc1034, pc1035, pc1036, pc1037, pc1038, pc1039, pc1040,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper4 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry4 s messageOffset outerReturn rest)
      (roundEntry4 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path4
  · simpa [entry4, Artifact.submissionArtifact] using hcode
  · simpa [entry4, State.fork] using hfork
  · exact run4 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry4] using hrun
  · simpa [entry4] using hnp

/-- One full helper call for round 4: nine-instruction setup plus verified round body. -/
def gasSteps_round4 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry4 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 4)
        (UInt256.ofNat 5) (UInt256.ofNat 0) (UInt256.ofNat 0x795)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper4 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 4) (UInt256.ofNat 5) (UInt256.ofNat 0)
    (UInt256.ofNat 0x795) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid795
  have hEq : roundEntry4 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 4)
        (UInt256.ofNat 5) (UInt256.ofNat 0) (UInt256.ofNat 0x795)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 4. -/
def wrapperWork4 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path4

theorem wrapperWork4_eq : wrapperWork4 = 28 := by rfl

/-- Body wrapper site for left round 5. Call indices 1042--1049, return 1050. -/
def site5 : ImmediateWrapper.WrapperSite :=
  { startIndex := 1042
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x7a5
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 8
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 5
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Nine-instruction body path for round 5: leading `JUMPDEST` at 1041 then eight-instruction call. -/
def path5 : List Located :=
  ⟨1041, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩ ::
    ImmediateWrapper.wrapperPath site5
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (wfOp (by decide) trivial rfl)

@[simp] private theorem pc1041 :
    Artifact.submissionArtifact.instructionPC 1041 = 0x795 := by decide
@[simp] private theorem pc1042 :
    Artifact.submissionArtifact.instructionPC 1042 = 0x796 := by decide
@[simp] private theorem pc1043 :
    Artifact.submissionArtifact.instructionPC 1043 = 0x799 := by decide
@[simp] private theorem pc1044 :
    Artifact.submissionArtifact.instructionPC 1044 = 0x79a := by decide
@[simp] private theorem pc1045 :
    Artifact.submissionArtifact.instructionPC 1045 = 0x79c := by decide
@[simp] private theorem pc1046 :
    Artifact.submissionArtifact.instructionPC 1046 = 0x79e := by decide
@[simp] private theorem pc1047 :
    Artifact.submissionArtifact.instructionPC 1047 = 0x79f := by decide
@[simp] private theorem pc1048 :
    Artifact.submissionArtifact.instructionPC 1048 = 0x7a1 := by decide
@[simp] private theorem pc1049 :
    Artifact.submissionArtifact.instructionPC 1049 = 0x7a4 := by decide

@[simp] private theorem valid7A5 :
    Decode.isValidJumpDest submissionBytecode 0x7a5 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1050 (by rfl)

/-- Wrapper entry for round 5: prior return PC with outer stack. -/
def entry5 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x795
           stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the nine-instruction setup for round 5. -/
def roundEntry5 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 5)
    (UInt256.ofNat 8) (UInt256.ofNat 0) (UInt256.ofNat 0x7a5)
    ([messageOffset, outerReturn] ++ rest)

theorem run5 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path5
      (entry5 s messageOffset outerReturn rest) =
        some (roundEntry5 s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x7a5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x7a5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 8, UInt256.ofNat 0, UInt256.ofNat 0x7a5,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 5, UInt256.ofNat 8, UInt256.ofNat 0,
      UInt256.ofNat 0x7a5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 5, UInt256.ofNat 8,
      UInt256.ofNat 0, UInt256.ofNat 0x7a5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 5,
      UInt256.ofNat 8, UInt256.ofNat 0, UInt256.ofNat 0x7a5, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 5, UInt256.ofNat 8, UInt256.ofNat 0,
      UInt256.ofNat 0x7a5, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [path5, ImmediateWrapper.wrapperPath, site5, entry5,
      roundEntry5, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc1041, pc1042, pc1043, pc1044, pc1045, pc1046, pc1047, pc1048, pc1049,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper5 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry5 s messageOffset outerReturn rest)
      (roundEntry5 s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path5
  · simpa [entry5, Artifact.submissionArtifact] using hcode
  · simpa [entry5, State.fork] using hfork
  · exact run5 s messageOffset outerReturn rest hstack hcode hrun
  · simpa [entry5] using hrun
  · simpa [entry5] using hnp

/-- One full helper call for round 5: nine-instruction setup plus verified round body. -/
def gasSteps_round5 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry5 s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 5)
        (UInt256.ofNat 8) (UInt256.ofNat 0) (UInt256.ofNat 0x7a5)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper5 s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 5) (UInt256.ofNat 8) (UInt256.ofNat 0)
    (UInt256.ofNat 0x7a5) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid7A5
  have hEq : roundEntry5 s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 5)
        (UInt256.ofNat 8) (UInt256.ofNat 0) (UInt256.ofNat 0x7a5)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-- Static non-memory work of the nine-instruction setup for round 5. -/
def wrapperWork5 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost path5

theorem wrapperWork5_eq : wrapperWork5 = 28 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0A
