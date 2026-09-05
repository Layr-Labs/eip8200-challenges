import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFrameFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionModel

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# H09 immediate block trace

This module composes the H09 frame with the verified immediate left and right
lane traces.  The final right site is supplied as a separate last-round seam.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateBlockTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open ImmediateFrame
open ImmediateFrameFacts
open ImmediateLaneTrace
open ImmediateSites
open ImmediateIteration
open CompressionTrace
open CompressionRightTrace
open CompressionModel

def blockRest (input : ByteArray) (i : Nat) : List UInt256 :=
  CompressionModel.driverRest input i

def blockMessageOffset (_input : ByteArray) (i : Nat) : UInt256 :=
  DriverTrace.messageOffsetWord i

def blockReturnDest : UInt256 := UInt256.ofNat 0x643

def blockInitialState (s : State) (input : ByteArray) (i : Nat) : State :=
  CompressionTrace.leftInitialState s (blockMessageOffset input i)
    blockReturnDest (blockRest input i)

def blockLeft80State (s : State) (input : ByteArray) (i : Nat) : State :=
  CompressionTrace.leftStates (blockInitialState s input i)
    (blockMessageOffset input i) blockReturnDest (blockRest input i) 80

def blockRight80State (s : State) (input : ByteArray) (i : Nat) : State :=
  CompressionRightTrace.rightStates (blockLeft80State s input i)
    (blockMessageOffset input i) blockReturnDest (blockRest input i) 80

private theorem valid643 :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 0x643).toNat = true := by
  decide

theorem firstWrapperEntry_eq_leftAt_zero (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    firstWrapperEntry s messageOffset returnDest rest =
      ImmediateLaneTrace.leftAt
        (CompressionTrace.leftInitialState s messageOffset returnDest rest)
        messageOffset returnDest rest 0 := by
  rw [firstWrapperEntry_normalized]
  simp [normalizedLeftInitialState, ImmediateLaneTrace.leftAt,
    ImmediateWrapper.wrapperEntryAt, ImmediateIteration.leftSite]
  decide

def gasSteps_prologue_to_leftAt_zero (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (prologueEntry s messageOffset returnDest rest)
      (ImmediateLaneTrace.leftAt
        (CompressionTrace.leftInitialState s messageOffset returnDest rest)
        messageOffset returnDest rest 0) := by
  exact (ImmediateFrame.gasSteps_prologue s messageOffset returnDest rest hstack
    hcode hfork hrun hnp).cast rfl
    (firstWrapperEntry_eq_leftAt_zero s messageOffset returnDest rest)

theorem leftAt_80_eq_rightAt_zero (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    ImmediateLaneTrace.leftAt s messageOffset returnDest rest 80 =
      ImmediateLaneTrace.rightAt
        (CompressionTrace.leftStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest 0 := by
  simp [ImmediateLaneTrace.leftAt, ImmediateLaneTrace.rightAt,
    ImmediateLaneTrace.rightRegularSite, ImmediateWrapper.wrapperEntryAt,
    ImmediateIteration.leftSite, ImmediateIteration.rightSite,
    ImmediateIteration.mkImmediateSite]

theorem leftInitialState_tables_of_tables (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (CompressionTrace.leftInitialState s messageOffset returnDest rest).memory := by
  have hfirst := firstWrapperEntry_tables s messageOffset returnDest rest htables
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

theorem leftInitialState_constants_of_constants (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hconstants :
      (∀ j, j < 5 →
        InitializationCorrect.slotWord s.memory 0x620 j =
          Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
      (∀ j, j < 5 →
        InitializationCorrect.slotWord s.memory 0x6c0 j =
          Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))) :
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (CompressionTrace.leftInitialState s messageOffset returnDest rest).memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (CompressionTrace.leftInitialState s messageOffset returnDest rest).memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!)) := by
  have hfirst := firstWrapperEntry_constants s messageOffset returnDest rest hconstants
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

theorem blockInitial_activeWords_ge67 (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hblock : i < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    67 ≤
      (CompressionTrace.leftInitialState s (DriverTrace.messageOffsetWord i)
        returnDest rest).activeWords.toNat := by
  have hfirst := prologueFirstWrapperEntry_activeWords_ge67 s input hfit i hblock
    returnDest rest
  rw [firstWrapperEntry_activeWords_eq_leftInitialState] at hfirst
  exact hfirst

theorem leftInitialState_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (CompressionTrace.leftInitialState s messageOffset returnDest rest).executionEnv =
      s.executionEnv := by
  have hfirst := firstWrapperEntry_executionEnv s messageOffset returnDest rest
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

theorem leftInitialState_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (CompressionTrace.leftInitialState s messageOffset returnDest rest).halt = s.halt := by
  have hfirst := firstWrapperEntry_halt s messageOffset returnDest rest
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

theorem leftInitialState_callStack (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (CompressionTrace.leftInitialState s messageOffset returnDest rest).callStack =
      s.callStack := by
  have hfirst := firstWrapperEntry_callStack s messageOffset returnDest rest
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

theorem leftInitialState_fork (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (CompressionTrace.leftInitialState s messageOffset returnDest rest).fork = s.fork := by
  have hfirst := firstWrapperEntry_fork s messageOffset returnDest rest
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

theorem leftInitialState_precompile (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Precompile.isPrecompileWithConfig
      (CompressionTrace.leftInitialState s messageOffset returnDest rest).executionEnv.precompileConfig
      (CompressionTrace.leftInitialState s messageOffset returnDest rest).executionEnv.fork
      (CompressionTrace.leftInitialState s messageOffset returnDest rest).executionEnv.codeAddr = false := by
  have hfirst : Precompile.isPrecompileWithConfig
      (firstWrapperEntry s messageOffset returnDest rest).executionEnv.precompileConfig
      (firstWrapperEntry s messageOffset returnDest rest).executionEnv.fork
      (firstWrapperEntry s messageOffset returnDest rest).executionEnv.codeAddr = false := by
    simpa [firstWrapperEntry_executionEnv, firstWrapperEntry_fork] using hnp
  rw [firstWrapperEntry_normalized] at hfirst
  simpa [normalizedLeftInitialState] using hfirst

def gasSteps_left80_to_rightAt_zero (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (leftCerts : ∀ i : Fin 80,
      ImmediateSites.ImmediateSiteCertificate (ImmediateSites.leftData i))
    (leftNextPC : ∀ i : Fin 80, (ImmediateIteration.leftSite i).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (ImmediateIteration.leftSite (i.val + 1)).startIndex))
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x620 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ImmediateLaneTrace.leftAt s messageOffset returnDest rest 0)
      (ImmediateLaneTrace.rightAt
        (CompressionTrace.leftStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest 0) := by
  exact (ImmediateLaneTrace.gasSteps_left80 s messageOffset returnDest rest
    leftCerts leftNextPC hactive tables constants hstack hcode hfork hrun hnp).cast
    rfl (leftAt_80_eq_rightAt_zero s messageOffset returnDest rest)

def gasSteps_rightAt_zero_to_rightAt_79 (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (rightCerts : ∀ i : Fin 79,
      ImmediateSites.ImmediateSiteCertificate (ImmediateSites.rightData i))
    (rightNextPC : ∀ i : Fin 79, (ImmediateIteration.rightSite i).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (ImmediateLaneTrace.rightRegularSite (i.val + 1)).startIndex))
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ImmediateLaneTrace.rightAt s messageOffset returnDest rest 0)
      (ImmediateLaneTrace.rightAt s messageOffset returnDest rest 79) :=
  ImmediateLaneTrace.gasSteps_right79 s messageOffset returnDest rest
    rightCerts rightNextPC hactive tables constants hstack hcode hfork hrun hnp

def gasSteps_lanes (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (leftCerts : ∀ i : Fin 80,
      ImmediateSites.ImmediateSiteCertificate (ImmediateSites.leftData i))
    (leftNextPC : ∀ i : Fin 80, (ImmediateIteration.leftSite i).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (ImmediateIteration.leftSite (i.val + 1)).startIndex))
    (rightCerts : ∀ i : Fin 79,
      ImmediateSites.ImmediateSiteCertificate (ImmediateSites.rightData i))
    (rightNextPC : ∀ i : Fin 79, (ImmediateIteration.rightSite i).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (ImmediateLaneTrace.rightRegularSite (i.val + 1)).startIndex))
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (leftConstants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x620 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!))
    (rightConstants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ImmediateLaneTrace.leftAt s messageOffset returnDest rest 0)
      (ImmediateLaneTrace.rightAt
        (CompressionTrace.leftStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest 79) := by
  have gleft := gasSteps_left80_to_rightAt_zero s messageOffset returnDest rest
    leftCerts leftNextPC hactive tables leftConstants hstack hcode hfork hrun hnp
  let q := CompressionTrace.leftStates s messageOffset returnDest rest 80
  have hqactive : 67 ≤ q.activeWords.toNat := by
    change 67 ≤
      (CompressionTrace.leftStates s messageOffset returnDest rest 80).activeWords.toNat
    rw [ImmediateStateFacts.leftStates_activeWords s messageOffset returnDest rest
      tables hactive 80 (by omega)]
    exact hactive
  have hqtables : InitializationCorrect.TablesCorrect q.memory := by
    change InitializationCorrect.TablesCorrect
      (CompressionTrace.leftStates s messageOffset returnDest rest 80).memory
    exact ImmediateStateFacts.leftStates_tables_preserved
      s messageOffset returnDest rest 80 tables
  have hqleftConstants : ∀ j, j < 5 →
      InitializationCorrect.slotWord q.memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!) := by
    intro j hj
    rw [ImmediateStateFacts.leftStates_slotWord s messageOffset returnDest rest
      80 0x620 j (by omega)]
    exact leftConstants j hj
  have hqrightConstants : ∀ j, j < 5 →
      InitializationCorrect.slotWord q.memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
    intro j hj
    rw [ImmediateStateFacts.leftStates_slotWord s messageOffset returnDest rest
      80 0x6c0 j (by omega)]
    exact rightConstants j hj
  have hqcode : q.executionEnv.code = submissionBytecode := by
    change (CompressionTrace.leftStates s messageOffset returnDest rest 80).executionEnv.code =
      submissionBytecode
    rw [CompressionTrace.leftStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    change (CompressionTrace.leftStates s messageOffset returnDest rest 80).fork = .Osaka
    rw [State.fork, CompressionTrace.leftStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by
    change (CompressionTrace.leftStates s messageOffset returnDest rest 80).halt = .Running
    rw [CompressionTrace.leftStates_halt]
    exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig
      (CompressionTrace.leftStates s messageOffset returnDest rest 80).executionEnv.precompileConfig
      (CompressionTrace.leftStates s messageOffset returnDest rest 80).executionEnv.fork
      (CompressionTrace.leftStates s messageOffset returnDest rest 80).executionEnv.codeAddr = false
    rw [CompressionTrace.leftStates_executionEnv]
    exact hnp
  have gright := gasSteps_rightAt_zero_to_rightAt_79 q messageOffset returnDest rest
    rightCerts rightNextPC hqactive hqtables hqrightConstants hstack hqcode hqfork hqrun hqnp
  exact gleft.trans gright

abbrev LastRoundGasSteps (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : Type :=
  Challenge.EvmProof.GasSteps
    (ImmediateLaneTrace.rightAt s messageOffset returnDest rest 79)
    (ImmediateFrame.epilogueEntry
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80)
      messageOffset returnDest rest)

def gasSteps_afterRight79 (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (lastRound : LastRoundGasSteps s messageOffset returnDest rest)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (ImmediateLaneTrace.rightAt s messageOffset returnDest rest 79)
      (epilogueReturned
        (CompressionRightTrace.rightStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest) := by
  have hqcode :
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80).executionEnv.code =
        submissionBytecode := by
    rw [CompressionRightTrace.rightStates_executionEnv]
    exact hcode
  have hqfork :
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80).fork = .Osaka := by
    rw [State.fork, CompressionRightTrace.rightStates_executionEnv]
    exact hfork
  have hqrun :
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80).halt = .Running := by
    rw [CompressionRightTrace.rightStates_halt]
    exact hrun
  have hqnp : Precompile.isPrecompileWithConfig
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80).executionEnv.precompileConfig
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80).executionEnv.fork
      (CompressionRightTrace.rightStates s messageOffset returnDest rest 80).executionEnv.codeAddr = false := by
    rw [CompressionRightTrace.rightStates_executionEnv]
    exact hnp
  exact lastRound.trans (ImmediateFrame.gasSteps_epilogue
    (CompressionRightTrace.rightStates s messageOffset returnDest rest 80)
    messageOffset returnDest rest hstack hqcode hqfork hqrun hqnp hvalid)

def gasSteps_compressBlock (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input)
    (hblock : i < DriverTrace.blockCount input)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hconstants :
      (∀ j, j < 5 →
        InitializationCorrect.slotWord s.memory 0x620 j =
          Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
      (∀ j, j < 5 →
        InitializationCorrect.slotWord s.memory 0x6c0 j =
          Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!)))
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (leftCerts : ∀ j : Fin 80,
      ImmediateSites.ImmediateSiteCertificate (ImmediateSites.leftData j))
    (leftNextPC : ∀ j : Fin 80, (ImmediateIteration.leftSite j).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (ImmediateIteration.leftSite (j.val + 1)).startIndex))
    (rightCerts : ∀ j : Fin 79,
      ImmediateSites.ImmediateSiteCertificate (ImmediateSites.rightData j))
    (rightNextPC : ∀ j : Fin 79, (ImmediateIteration.rightSite j).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (ImmediateLaneTrace.rightRegularSite (j.val + 1)).startIndex))
    (lastRound : LastRoundGasSteps
      (blockLeft80State s input i) (blockMessageOffset input i)
      blockReturnDest (blockRest input i)) :
    Challenge.EvmProof.GasSteps
      (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned
        (CompressionModel.resultState s input i) input i) := by
  have hrest : (blockRest input i).length < 970 := by
    simp [blockRest, CompressionModel.driverRest]
  have hrestFrame : (blockRest input i).length < 978 := by omega
  have hqactive : 67 ≤ (blockInitialState s input i).activeWords.toNat := by
    simpa [blockInitialState, blockMessageOffset, blockReturnDest, blockRest] using
      blockInitial_activeWords_ge67 s input i hfit hblock blockReturnDest
        (blockRest input i)
  have hqtables : InitializationCorrect.TablesCorrect
      (blockInitialState s input i).memory := by
    simpa [blockInitialState, blockMessageOffset, blockReturnDest, blockRest] using
      leftInitialState_tables_of_tables s (blockMessageOffset input i)
        blockReturnDest (blockRest input i) htables
  have hqconstants := leftInitialState_constants_of_constants s
    (blockMessageOffset input i) blockReturnDest (blockRest input i) hconstants
  have hqcode : (blockInitialState s input i).executionEnv.code = submissionBytecode := by
    change (CompressionTrace.leftInitialState s (blockMessageOffset input i)
      blockReturnDest (blockRest input i)).executionEnv.code = submissionBytecode
    rw [leftInitialState_executionEnv]
    exact hcode
  have hqfork : (blockInitialState s input i).fork = .Osaka := by
    change (CompressionTrace.leftInitialState s (blockMessageOffset input i)
      blockReturnDest (blockRest input i)).fork = .Osaka
    rw [leftInitialState_fork]
    exact hfork
  have hqrun : (blockInitialState s input i).halt = .Running := by
    change (CompressionTrace.leftInitialState s (blockMessageOffset input i)
      blockReturnDest (blockRest input i)).halt = .Running
    rw [leftInitialState_halt]
    exact hrun
  have hqnp : Precompile.isPrecompileWithConfig
      (blockInitialState s input i).executionEnv.precompileConfig
      (blockInitialState s input i).executionEnv.fork
      (blockInitialState s input i).executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig
      (CompressionTrace.leftInitialState s (blockMessageOffset input i)
        blockReturnDest (blockRest input i)).executionEnv.precompileConfig
      (CompressionTrace.leftInitialState s (blockMessageOffset input i)
        blockReturnDest (blockRest input i)).executionEnv.fork
      (CompressionTrace.leftInitialState s (blockMessageOffset input i)
        blockReturnDest (blockRest input i)).executionEnv.codeAddr = false
    rw [leftInitialState_executionEnv]
    exact hnp
  have gframe := gasSteps_prologue_to_leftAt_zero s
    (blockMessageOffset input i) blockReturnDest (blockRest input i)
    hrestFrame hcode hfork hrun hnp
  have gframe' : Challenge.EvmProof.GasSteps
      (DriverTrace.compressEntry s input i)
      (ImmediateLaneTrace.leftAt (blockInitialState s input i)
        (blockMessageOffset input i) blockReturnDest (blockRest input i) 0) := by
    exact gframe.cast (by rfl) rfl
  have glanes := gasSteps_lanes (blockInitialState s input i)
    (blockMessageOffset input i) blockReturnDest (blockRest input i)
    leftCerts leftNextPC rightCerts rightNextPC hqactive hqtables
    hqconstants.1 hqconstants.2 hrestFrame hqcode hqfork hqrun hqnp
  have hleft80code : (blockLeft80State s input i).executionEnv.code =
      submissionBytecode := by
    change (CompressionTrace.leftStates (blockInitialState s input i)
      (blockMessageOffset input i) blockReturnDest (blockRest input i) 80).executionEnv.code =
      submissionBytecode
    rw [CompressionTrace.leftStates_executionEnv]
    exact hqcode
  have hleft80fork : (blockLeft80State s input i).fork = .Osaka := by
    change (CompressionTrace.leftStates (blockInitialState s input i)
      (blockMessageOffset input i) blockReturnDest (blockRest input i) 80).fork = .Osaka
    rw [State.fork, CompressionTrace.leftStates_executionEnv]
    exact hqfork
  have hleft80run : (blockLeft80State s input i).halt = .Running := by
    change (CompressionTrace.leftStates (blockInitialState s input i)
      (blockMessageOffset input i) blockReturnDest (blockRest input i) 80).halt = .Running
    rw [CompressionTrace.leftStates_halt]
    exact hqrun
  have hleft80np : Precompile.isPrecompileWithConfig
      (blockLeft80State s input i).executionEnv.precompileConfig
      (blockLeft80State s input i).executionEnv.fork
      (blockLeft80State s input i).executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig
      (CompressionTrace.leftStates (blockInitialState s input i)
        (blockMessageOffset input i) blockReturnDest (blockRest input i) 80).executionEnv.precompileConfig
      (CompressionTrace.leftStates (blockInitialState s input i)
        (blockMessageOffset input i) blockReturnDest (blockRest input i) 80).executionEnv.fork
      (CompressionTrace.leftStates (blockInitialState s input i)
        (blockMessageOffset input i) blockReturnDest (blockRest input i) 80).executionEnv.codeAddr = false
    rw [CompressionTrace.leftStates_executionEnv]
    exact hqnp
  have gtail := gasSteps_afterRight79 (blockLeft80State s input i)
    (blockMessageOffset input i) blockReturnDest (blockRest input i) lastRound
    hrest hleft80code hleft80fork hleft80run hleft80np valid643
  have gtotal := gframe'.trans (glanes.trans gtail)
  have hend : epilogueReturned (blockRight80State s input i)
      (blockMessageOffset input i) blockReturnDest (blockRest input i) =
      DriverTrace.compressReturned (CompressionModel.resultState s input i) input i := by
    simp only [blockRight80State, blockLeft80State, blockInitialState,
      blockMessageOffset, blockReturnDest, blockRest, epilogueReturned,
      CompressionModel.resultState, CompressionModel.driverRest,
      CompressionTrace.leftFinalState, CompressionTailTrace.rightTailResult,
      DriverTrace.compressReturned, CompressionTailTrace.combinationReturned,
      CompressionTailTrace.combinationCleaned]
  exact gtotal.cast rfl hend

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateBlockTrace
