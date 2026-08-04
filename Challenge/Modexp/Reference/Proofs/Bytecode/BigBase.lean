import Challenge.Modexp.Reference.Proofs.Bytecode.BigModulus
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified base-conversion path -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigBase

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def toClearDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 632 .JUMPDEST, pushAt 633 2 823,
   opAt 634 (.Dup ⟨2, by decide⟩), pushAt 635 2 3072,
   pushAt 636 2 19, opAt 637 .JUMP]

def startBaseLoopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 638 .JUMPDEST, pushAt 639 1 1, pushAt 640 2 3072,
   opAt 641 .MSTORE, pushAt 642 0 0]

def frame (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : List UInt256 :=
  [accumulator, UInt256.ofNat count] ++ rest

def afterClearDouble (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  BigHelpers.clearReturned (BigModulus.scanNonzero s count rest) 3072 count
    823 (frame accumulator count rest)

def baseLoopEntry (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  let cleared := afterClearDouble s accumulator count rest
  { cleared with
    pc := UInt256.ofNat 831
    stack := [0, accumulator, UInt256.ofNat count] ++ rest
    memory := MachineState.writeBytes cleared.memory
      (Data.Bytes.natToBytesPadded 1 32) 3072
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      cleared.activeWords.toNat 3072 32) }

@[simp] private theorem baseSetupPCs (i : Nat) (hi : 632 ≤ i)
    (hii : i ≤ 642) :
    Artifact.referenceArtifact.instructionPC i =
      ([811,812,815,816,819,822,823,824,826,829,830])[i - 632]! := by
  interval_cases i <;> decide

private theorem jump19 :
    Decode.isValidJumpDest referenceBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump823 :
    Decode.isValidJumpDest referenceBytecode 823 = true :=
  Artifact.isValidJumpDest_index 638 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_toClearDouble (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClearDoublePath
      (BigModulus.scanNonzero s count rest) =
      some (BigHelpers.clearEntry (BigModulus.scanNonzero s count rest)
        3072 count 823
        (frame accumulator count rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h19 : (19 : UInt256).toNat = 19 := by decide
  have h19Word : (19 : UInt256) = UInt256.ofNat 19 := by decide
  simp [toClearDoublePath, opAt, pushAt, wfOp, BigModulus.scanNonzero,
    BigHelpers.clearEntry, frame, baseSetupPCs, hacc, hcode, hrun, jump19,
    h19, h19Word, hc2, hc3, hc4, hc5, hc6,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_startBaseLoop (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startBaseLoopPath
      (afterClearDouble s accumulator count rest) =
      some (baseLoopEntry s accumulator count rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have h823 : (823 : UInt256).toNat = 823 := by decide
  have h823Word : (823 : UInt256) = UInt256.ofNat 823 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1Nat : (1 : UInt256).toNat = 1 := by decide
  have h3072Nat : (3072 : UInt256).toNat = 3072 := by decide
  simp [startBaseLoopPath, opAt, pushAt, wfOp, afterClearDouble,
    BigModulus.scanNonzero, BigHelpers.clearReturned, baseLoopEntry, frame,
    baseSetupPCs, hrun, h823, h823Word, hzero, h0Word, h1Nat, h3072Nat,
    hc2, hc3, hc4,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_baseSetup (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 998)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (BigModulus.scanNonzero s count rest)
      (baseLoopEntry s accumulator count rest) := by
  have hcapRaw : rest.length < 1016 := by omega
  have hframe : (frame accumulator count rest).length < 1017 := by
    simp [frame]
    omega
  have hcodeScan : (BigModulus.scanNonzero s count rest).executionEnv.code =
      referenceBytecode := by
    simpa [BigModulus.scanNonzero] using hcode
  have hforkScan : (BigModulus.scanNonzero s count rest).fork = .Osaka := by
    simpa [BigModulus.scanNonzero, State.fork] using hfork
  have hrunScan : (BigModulus.scanNonzero s count rest).halt = .Running := by
    simpa [BigModulus.scanNonzero] using hrun
  have hnpScan : Precompile.isPrecompile
      (BigModulus.scanNonzero s count rest).executionEnv.fork
      (BigModulus.scanNonzero s count rest).executionEnv.codeAddr = false := by
    simpa [BigModulus.scanNonzero, State.fork] using hnp
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka toClearDoublePath
      (by simpa [BigModulus.scanNonzero, Artifact.referenceArtifact] using hcode)
      (by simpa [BigModulus.scanNonzero, State.fork] using hfork)
      (run_toClearDouble s accumulator count rest hcapRaw hacc hcode hrun)
      (by simpa [BigModulus.scanNonzero] using hrun)
      (by simpa [BigModulus.scanNonzero, State.fork] using hnp)).trans <|
    (BigHelpers.gasSteps_clear (BigModulus.scanNonzero s count rest) 3072
      count 823 (frame accumulator count rest) hframe hcount hcodeScan
      hforkScan hrunScan hnpScan jump823).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startBaseLoopPath
        (by simpa [afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, Artifact.referenceArtifact] using hcode)
        (by simpa [afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, State.fork] using hfork)
        (run_startBaseLoop s accumulator count rest hcapRaw hrun)
        (by simpa [afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero] using hrun)
        (by simpa [afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, State.fork] using hnp)

theorem gasSteps_baseSetup_cost_potential (s : State)
    (accumulator : UInt256) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 998)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_baseSetup s accumulator count rest hcap hacc hcount hcode hfork
        hrun hnp).cost + MachineState.memCost
          (BigModulus.scanNonzero s count rest).activeWords.toNat =
      (77 + count * 71) + MachineState.memCost
        (baseLoopEntry s accumulator count rest).activeWords.toNat := by
  have hcapRaw : rest.length < 1016 := by omega
  have hframe : (frame accumulator count rest).length < 1017 := by
    simp [frame]
    omega
  have hcodeScan : (BigModulus.scanNonzero s count rest).executionEnv.code =
      referenceBytecode := by simpa [BigModulus.scanNonzero] using hcode
  have hforkScan : (BigModulus.scanNonzero s count rest).fork = .Osaka := by
    simpa [BigModulus.scanNonzero, State.fork] using hfork
  have hrunScan : (BigModulus.scanNonzero s count rest).halt = .Running := by
    simpa [BigModulus.scanNonzero] using hrun
  have hnpScan : Precompile.isPrecompile
      (BigModulus.scanNonzero s count rest).executionEnv.fork
      (BigModulus.scanNonzero s count rest).executionEnv.codeAddr = false := by
    simpa [BigModulus.scanNonzero, State.fork] using hnp
  have hraw := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    toClearDoublePath 21
      (run_toClearDouble s accumulator count rest hcapRaw hacc hcode hrun)
      (by simpa [BigModulus.scanNonzero, State.fork] using hfork)
      (by native_decide) (by native_decide)
  have hclear := BigHelpers.gasSteps_clear_cost_potential
    (BigModulus.scanNonzero s count rest) 3072 count 823
      (frame accumulator count rest) hframe hcount hcodeScan hforkScan
      hrunScan hnpScan jump823
  have htail := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    startBaseLoopPath 12
      (run_startBaseLoop s accumulator count rest hcapRaw hrun)
      (by simpa [afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, State.fork] using hfork)
      (by native_decide) (by native_decide)
  unfold gasSteps_baseSetup
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [BigModulus.scanNonzero, afterClearDouble, baseLoopEntry,
    BigHelpers.clearEntry, BigHelpers.clearReturned] at hraw hclear htail ⊢
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigBase
