import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionRightLoopTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# H09 final right-round wrapper

This module isolates the final `PUSH0` and immediate right-round call.  The
round-state equality is an explicit interface for the immediate model proof.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLastRound

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def lastRoundSite : ImmediateWrapper.WrapperSite :=
  { startIndex := 2429
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x324
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 11
    wiW := ⟨1, by decide⟩
    wordIndex := UInt256.ofNat 11
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨2, by decide⟩
    base := UInt256.ofNat 352 }

structure LastRoundCertificate : Prop where
  h0 : Artifact.submissionArtifact.instructions[2429]? =
    some (.push ⟨2, by decide⟩ (UInt256.ofNat 0x324))
  h1 : Artifact.submissionArtifact.instructions[2430]? =
    some (.push ⟨0, by decide⟩ (UInt256.ofNat 0))
  h2 : Artifact.submissionArtifact.instructions[2431]? =
    some (.push ⟨1, by decide⟩ (UInt256.ofNat 11))
  h3 : Artifact.submissionArtifact.instructions[2432]? =
    some (.push ⟨1, by decide⟩ (UInt256.ofNat 11))
  h4 : Artifact.submissionArtifact.instructions[2433]? =
    some (.push ⟨0, by decide⟩ (UInt256.ofNat 0))
  h5 : Artifact.submissionArtifact.instructions[2434]? =
    some (.push ⟨2, by decide⟩ (UInt256.ofNat 352))
  h6 : Artifact.submissionArtifact.instructions[2435]? =
    some (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114))
  h7 : Artifact.submissionArtifact.instructions[2436]? = some (.op .JUMP)
  wf0 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨2, by decide⟩ (UInt256.ofNat 0x324))
  wf1 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨0, by decide⟩ (UInt256.ofNat 0))
  wf2 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨1, by decide⟩ (UInt256.ofNat 11))
  wf3 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨1, by decide⟩ (UInt256.ofNat 11))
  wf4 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨0, by decide⟩ (UInt256.ofNat 0))
  wf5 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨2, by decide⟩ (UInt256.ofNat 352))
  wf6 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114))
  wf7 : Challenge.EvmProof.Stepper.WellFormed .Osaka (.op .JUMP)

def artifactLastRoundCertificate : LastRoundCertificate where
  h0 := by rfl
  h1 := by rfl
  h2 := by rfl
  h3 := by rfl
  h4 := by rfl
  h5 := by rfl
  h6 := by rfl
  h7 := by rfl
  wf0 := by decide
  wf1 := by decide
  wf2 := by decide
  wf3 := by decide
  wf4 := by decide
  wf5 := by decide
  wf6 := by decide
  wf7 := wfOp (by decide) trivial rfl

def lastRoundWrapperPath (h : LastRoundCertificate) : List Located :=
  ImmediateWrapper.wrapperPath lastRoundSite
    h.h0 h.h1 h.h2 h.h3 h.h4 h.h5 h.h6 h.h7
    h.wf0 h.wf1 h.wf2 h.wf3 h.wf4 h.wf5 h.wf6 h.wf7

@[simp] private theorem pc2428 :
    Artifact.submissionArtifact.instructionPC 2428 = 5116 := by decide
@[simp] private theorem pc2429 :
    Artifact.submissionArtifact.instructionPC 2429 = 5117 := by decide
@[simp] private theorem pc2430 :
    Artifact.submissionArtifact.instructionPC 2430 = 5120 := by decide
@[simp] private theorem pc2431 :
    Artifact.submissionArtifact.instructionPC 2431 = 5121 := by decide
@[simp] private theorem pc2432 :
    Artifact.submissionArtifact.instructionPC 2432 = 5123 := by decide
@[simp] private theorem pc2433 :
    Artifact.submissionArtifact.instructionPC 2433 = 5125 := by decide
@[simp] private theorem pc2434 :
    Artifact.submissionArtifact.instructionPC 2434 = 5126 := by decide
@[simp] private theorem pc2435 :
    Artifact.submissionArtifact.instructionPC 2435 = 5129 := by decide
@[simp] private theorem pc2436 :
    Artifact.submissionArtifact.instructionPC 2436 = 5132 := by decide

@[simp] private theorem valid114 :
    Decode.isValidJumpDest submissionBytecode 0x114 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 208 (by rfl)

@[simp] private theorem valid324 :
    Decode.isValidJumpDest submissionBytecode 0x324 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 563 (by rfl)

/-- State before the final `PUSH0`; this is the previous-message API. -/
def previousMessageState (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2428)
    stack := [messageOffset, outerReturn] ++ rest }

/-- State after the final `PUSH0`, before the eight-instruction wrapper. -/
def wrapperEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2429)
    stack := [UInt256.ofNat 0, messageOffset, outerReturn] ++ rest }

def wrapperRoundEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 352) 0 (UInt256.ofNat 11)
    (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x324)
    ([UInt256.ofNat 0, messageOffset, outerReturn] ++ rest)

/-- The right-round result reframed for the final wrapper return. -/
def lastRoundOutput (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { rightRoundState s messageOffset outerReturn rest 79 with
    pc := UInt256.ofNat 0x324
    stack := [UInt256.ofNat 0, messageOffset, outerReturn] ++ rest }

def LastRoundModel (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : Prop :=
  lastRoundOutput s messageOffset outerReturn rest =
    RoundTrace.roundReturned s (UInt256.ofNat 352) 0 (UInt256.ofNat 11)
      (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x324)
      ([UInt256.ofNat 0, messageOffset, outerReturn] ++ rest)

theorem lastRoundModel_of_pinned
    (s : State) (messageOffset outerReturn : UInt256) (rest : List UInt256)
    (nextPC : UInt256) (nextStack : List UInt256)
    (hmodel :
      {rightRoundState s messageOffset outerReturn rest 79 with
        pc := nextPC, stack := nextStack} =
      RoundTrace.roundReturned s 352 (4 - 79 / 16)
        (UInt256.ofNat (Crypto.Ripemd160.rP[79]!))
        (UInt256.ofNat (Crypto.Ripemd160.sP[79]!))
        (Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[79 / 16]!))
        nextPC nextStack)
    (hpc : nextPC = UInt256.ofNat 0x324)
    (hstack : nextStack =
      [UInt256.ofNat 0, messageOffset, outerReturn] ++ rest) :
    LastRoundModel s messageOffset outerReturn rest := by
  subst nextPC
  subst nextStack
  have hr : Crypto.Ripemd160.rP[79]! = 11 := by decide
  have hs : Crypto.Ripemd160.sP[79]! = 11 := by decide
  have hk : Crypto.Ripemd160.KP[79 / 16]! = 0 := by decide
  have hk0 : UInt32.toNat (0 : UInt32) = 0 := by rfl
  simpa only [LastRoundModel, lastRoundOutput, hr, hs, hk,
    Challenge.EvmProof.Word.ofUInt32,
    Challenge.EvmProof.Word.literal_eq_ofNat, Nat.reduceDiv, Nat.reduceSub,
    hk0] using hmodel

theorem run_push0 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      ([⟨2428, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl,
        by decide⟩] : List Located)
      (previousMessageState s messageOffset outerReturn rest) =
      some (wrapperEntry s messageOffset outerReturn rest) := by
  have hc : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc' : rest.length + 1 + 1 < 1024 := by omega
  simp [previousMessageState, wrapperEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hrun, hc, hc', pc2428, pc2429,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat]

theorem run_lastRoundWrapper (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (h : LastRoundCertificate)
    (hstack : rest.length < 977)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (lastRoundWrapperPath h)
      (wrapperEntry s messageOffset outerReturn rest) =
      some (wrapperRoundEntry s messageOffset outerReturn rest) := by
  have hc0 : ([UInt256.ofNat 0, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 10) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [lastRoundWrapperPath, ImmediateWrapper.wrapperPath, lastRoundSite,
      wrapperEntry, wrapperRoundEntry, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, hrun, hcode, valid114,
      pc2429, pc2430, pc2431, pc2432, pc2433, pc2434, pc2435, pc2436,
      hc0, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_lastRound (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (h : LastRoundCertificate)
    (hmodel : LastRoundModel s messageOffset outerReturn rest)
    (hstack : rest.length < 977)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (previousMessageState s messageOffset outerReturn rest)
      (lastRoundOutput s messageOffset outerReturn rest) := by
  have gPush := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka
      ([⟨2428, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl,
        by decide⟩] : List Located)
      (s := previousMessageState s messageOffset outerReturn rest)
      (by simpa [previousMessageState, Artifact.submissionArtifact] using hcode)
      (by simpa [previousMessageState] using hfork)
      (run_push0 s messageOffset outerReturn rest (by omega) hrun)
      (by simpa [previousMessageState] using hrun)
      (by simpa [previousMessageState] using hnp)
  have gWrap := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (lastRoundWrapperPath h)
      (s := wrapperEntry s messageOffset outerReturn rest)
      (by simpa [wrapperEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [wrapperEntry] using hfork)
      (run_lastRoundWrapper s messageOffset outerReturn rest h hstack hcode hrun)
      (by simpa [wrapperEntry] using hrun)
      (by simpa [wrapperEntry] using hnp)
  have hroundStack :
      ([UInt256.ofNat 0, messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 352) 0
    (by decide) (UInt256.ofNat 11) (UInt256.ofNat 11) (UInt256.ofNat 0)
    (UInt256.ofNat 0x324)
    ([UInt256.ofNat 0, messageOffset, outerReturn] ++ rest)
    hroundStack hcode hfork hrun hnp valid324
  have gRound' := Challenge.EvmProof.GasSteps.cast gRound rfl hmodel.symm
  exact gPush.trans (gWrap.trans gRound')

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLastRound
