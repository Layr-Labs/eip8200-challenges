import Challenge.Modexp.Submission.Proofs.Bytecode.Accessors
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Certified big-endian operand loading

This module follows the emitted `loadBigEndian` loop.  It reuses the certified
`calldataByte` helper and models the destination as little-endian 256-bit
limbs, exactly as the later modular-arithmetic helpers consume it.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def loadSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 376 .JUMPDEST, pushAt 377 0 0]

def loadGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 378 .JUMPDEST, opAt 379 (.Dup ⟨2, by decide⟩),
   opAt 380 (.Dup ⟨1, by decide⟩), opAt 381 .LT, opAt 382 .ISZERO,
   pushAt 383 2 518, opAt 384 .JUMPI]

def loadToBytePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 385 (.Dup ⟨0, by decide⟩), pushAt 386 1 1,
   opAt 387 (.Dup ⟨4, by decide⟩), opAt 388 .SUB, opAt 389 .SUB,
   opAt 390 (.Dup ⟨0, by decide⟩), pushAt 391 1 5, opAt 392 .SHR,
   pushAt 393 1 31, opAt 394 (.Dup ⟨2, by decide⟩), opAt 395 .AND,
   pushAt 396 1 3, opAt 397 .SHL, opAt 398 (.Dup ⟨1, by decide⟩),
   pushAt 399 1 5, opAt 400 .SHL, opAt 401 (.Dup ⟨7, by decide⟩),
   opAt 402 .ADD, pushAt 403 2 496, pushAt 404 0 0,
   opAt 405 (.Dup ⟨6, by decide⟩), opAt 406 (.Dup ⟨8, by decide⟩),
   opAt 407 .ADD, pushAt 408 1 55, opAt 409 .JUMP]

def loadAfterBytePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 410 .JUMPDEST, opAt 411 (.Dup ⟨2, by decide⟩), opAt 412 .SHL,
   opAt 413 (.Dup ⟨1, by decide⟩), opAt 414 .MLOAD, opAt 415 .OR,
   opAt 416 (.Dup ⟨1, by decide⟩), opAt 417 .MSTORE, opAt 418 .POP,
   opAt 419 .POP, opAt 420 .POP, opAt 421 .POP, pushAt 422 1 1,
   opAt 423 (.Dup ⟨1, by decide⟩), opAt 424 .ADD,
   opAt 425 (.Swap ⟨0, by decide⟩), opAt 426 .POP,
   pushAt 427 2 454, opAt 428 .JUMP]

def loadExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 429 .JUMPDEST, opAt 430 .POP, opAt 431 .POP, opAt 432 .POP,
   opAt 433 .POP, opAt 434 .JUMP]

def loadByte (calldata : ByteArray) (offset i : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord calldata (offset + i))

def loadReverse (length i : Nat) : Nat := length - 1 - i

def loadLimb (length i : Nat) : Nat := loadReverse length i / 32

def loadShift (length i : Nat) : Nat := 8 * (loadReverse length i % 32)

def loadReverseWord (length : UInt256) (i : Nat) : UInt256 :=
  length - UInt256.ofNat 1 - UInt256.ofNat i

def loadLimbWord (length : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftRight (loadReverseWord length i) (UInt256.ofNat 5)

def loadShiftWord (length : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (loadReverseWord length i) (UInt256.ofNat 31))
    (UInt256.ofNat 3)

def loadAt (dst : UInt256) (length i : Nat) : UInt256 :=
  dst + UInt256.shiftLeft (loadLimbWord (UInt256.ofNat length) i)
    (UInt256.ofNat 5)

def loadMemory (calldata : ByteArray) (offset : Nat) (dst : UInt256)
    (length : Nat) : Nat → ByteArray → ByteArray
  | 0, memory => memory
  | i + 1, memory =>
      let before := loadMemory calldata offset dst length i memory
      let addr := loadAt dst length i
      let shifted := UInt256.shiftLeft (loadByte calldata offset i)
        (loadShiftWord (UInt256.ofNat length) i)
      let value := UInt256.lor (MachineState.readWord before addr.toNat) shifted
      MachineState.writeBytes before (Data.Bytes.natToBytesPadded value.toNat 32)
        addr.toNat

def loadWords (active : UInt256) (dst : UInt256) (length : Nat) : Nat → UInt256
  | 0 => active
  | i + 1 =>
      let afterLoad := UInt256.ofNat (MachineState.activeWordsAfter
        (loadWords active dst length i).toNat (loadAt dst length i).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter afterLoad.toNat
        (loadAt dst length i).toNat 32)

def loadEntry (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 452
           stack := [offset, length, dst, returnDest] ++ rest }

def loadLoop (s : State) (offset length dst : UInt256) (i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 454
           stack := [UInt256.ofNat i, offset, length, dst, returnDest] ++ rest
           memory := loadMemory s.executionEnv.calldata offset.toNat dst
             length.toNat i s.memory
           activeWords := loadWords s.activeWords dst length.toNat i }

def loadBody (s : State) (offset length dst : UInt256) (i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { loadLoop s offset length dst i returnDest rest with pc := UInt256.ofNat 463 }

def loadSaved (offset length dst : UInt256) (i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  let reverse := loadReverseWord length i
  let limb := loadLimbWord length i
  let shift := loadShiftWord length i
  let addr := dst + UInt256.shiftLeft limb (UInt256.ofNat 5)
  [addr, shift, limb, reverse, UInt256.ofNat i, offset, length, dst,
    returnDest] ++ rest

def loadByteEntry (s : State) (offset length dst : UInt256) (i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  Accessors.calldataByteEntry (loadBody s offset length dst i returnDest rest)
    (offset + UInt256.ofNat i) (UInt256.ofNat 0) (UInt256.ofNat 496)
    (loadSaved offset length dst i returnDest rest)

def loadAfterByte (s : State) (offset length dst : UInt256) (i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  Accessors.calldataByteReturned
    (loadBody s offset length dst i returnDest rest)
    (offset + UInt256.ofNat i) (UInt256.ofNat 496)
    (loadSaved offset length dst i returnDest rest)

def loadReturned (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) : State :=
  { loadLoop s offset length dst length.toNat returnDest rest with
      pc := returnDest, stack := rest }

@[simp] private theorem listGetZero {α : Type} (head default : α)
    (tail : List α) :
    (head :: tail)[0]?.getD default = head := by
  rfl

@[simp] private theorem listGetElemZero {α : Type} (head : α)
    (tail : List α) :
    (head :: tail)[0]? = some head := by
  rfl

@[simp] private theorem loadSetupPCs (i : Nat)
    (hi : 376 ≤ i) (hii : i ≤ 384) :
    Artifact.submissionArtifact.instructionPC i =
      ([452,453,454,455,456,457,458,459,462] : List Nat)[i - 376]! := by
  interval_cases i <;> decide

@[simp] private theorem loadBodyPCs (i : Nat)
    (hi : 385 ≤ i) (hii : i ≤ 409) :
    Artifact.submissionArtifact.instructionPC i =
      ([463,464,466,467,468,469,470,472,473,475,476,477,479,480,481,483,484,485,486,489,490,491,492,493,495] : List Nat)[i - 385]! := by
  interval_cases i <;> decide

@[simp] private theorem loadStorePCs (i : Nat)
    (hi : 410 ≤ i) (hii : i ≤ 428) :
    Artifact.submissionArtifact.instructionPC i =
      ([496,497,498,499,500,501,502,503,504,505,506,507,508,510,511,512,513,514,517] : List Nat)[i - 410]! := by
  interval_cases i <;> decide

@[simp] private theorem loadExitPCs (i : Nat)
    (hi : 429 ≤ i) (hii : i ≤ 434) :
    Artifact.submissionArtifact.instructionPC i =
      ([518,519,520,521,522,523] : List Nat)[i - 429]! := by
  interval_cases i <;> decide

private theorem jump441 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 454 = true :=
  Artifact.isValidJumpDest_index 378 (by rfl)

private theorem jump4 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 55 = true :=
  Artifact.isValidJumpDest_index 40 (by rfl)

private theorem jump484 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 496 = true :=
  Artifact.isValidJumpDest_index 410 (by rfl)

private theorem jump506 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 518 = true :=
  Artifact.isValidJumpDest_index 429 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_loadSetup (s : State) (offset length : Nat) (dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadSetupPath
      (loadEntry s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest) =
    some (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst 0
      returnDest rest) := by
  have hc : ∀ n ≤ 8, rest.length + n < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (disch := omega) [loadSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadEntry, loadLoop, loadMemory, loadWords, loadSetupPCs, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, hzero]

set_option linter.unusedSimpArgs false in
theorem run_loadGuard (s : State) (offset length : Nat) (dst returnDest : UInt256)
    (i : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hi : i < length) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadGuardPath
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
        returnDest rest) =
    some { loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
      returnDest rest with pc := UInt256.ofNat 463 } := by
  have hc : ∀ n ≤ 8, rest.length + n < 1024 := by omega
  have hi256 : i < 2 ^ 256 := hi.trans hlength
  have hlt : i % 2 ^ 256 < length % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hlength]
    exact hi
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : (UInt256.ofNat 459 + UInt256.ofNat 3).succ =
      UInt256.ofNat 463 := by decide
  simp (disch := omega) [loadGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadLoop, loadSetupPCs, hrun, UInt256.lt, UInt256.isTrue, hi, hlt,
    honeIsZero, hpc, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, hoffset, hlength]

set_option linter.unusedSimpArgs false in
theorem run_loadFinishGuard (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hoffset : offset < 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadGuardPath
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst length
        returnDest rest) =
    some { loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst length
      returnDest rest with pc := UInt256.ofNat 518 } := by
  have hc : ∀ n ≤ 8, rest.length + n < 1024 := by omega
  have h506 : (518 : UInt256) = UInt256.ofNat 518 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (518 : UInt256).toNat = true := by
    rw [show (518 : UInt256).toNat = 518 by decide]
    exact jump506
  simp (disch := omega) [loadGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadLoop, loadSetupPCs, hcode, hrun, UInt256.lt, UInt256.isTrue,
    hzeroFalse, hvalid, jump506, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h506, hoffset, hlength]

set_option linter.unusedSimpArgs false in
theorem run_loadExit (s : State) (offset length : Nat) (dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadExitPath
      { loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst length
        returnDest rest with pc := UInt256.ofNat 518 } =
    some (loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length) dst
      returnDest rest) := by
  have hc : ∀ n ≤ 8, rest.length + n < 1024 := by omega
  simp (disch := omega) [loadExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadLoop, loadReturned, loadExitPCs, hcode, hrun, hvalid,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    List.exchange, Nat.add_assoc, hc, hoffset, hlength]

set_option linter.unusedSimpArgs false in
theorem run_loadToByte (s : State) (offset length : Nat) (dst returnDest : UInt256)
    (i : Nat) (rest : List UInt256) (hcap : rest.length < 1000)
    (hoffset : offset + i < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadToBytePath
      (loadBody s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
        returnDest rest) =
    some (loadByteEntry s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
      returnDest rest) := by
  have hc : ∀ n ≤ 24, rest.length + n < 1024 := by omega
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (55 : UInt256).toNat = true := by
    rw [show (55 : UInt256).toNat = 55 by decide]
    exact jump4
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hthree : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have hfour : (55 : UInt256) = UInt256.ofNat 55 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hthirtyOne : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h484 : (496 : UInt256) = UInt256.ofNat 496 := by decide
  simp (config := { maxSteps := 600000 }) (disch := omega)
    [loadToBytePath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      loadBody, loadLoop, loadByteEntry, loadSaved, loadReverseWord,
      loadLimbWord, loadShiftWord, loadBodyPCs, Accessors.calldataByteEntry,
      hcode, hrun, hvalid, jump4, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.lt, UInt256.isTrue, List.exchange, Nat.add_assoc, hc,
      hoffset, hlength, hzero, hone, hthree, hfour, hfive, hthirtyOne,
      h484]

set_option linter.unusedSimpArgs false in
theorem run_loadAfterByte (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffset : offset + i < 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hi : i < length)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadAfterBytePath
      (loadAfterByte s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
        returnDest rest) =
    some (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst (i + 1)
      returnDest rest) := by
  have hc : ∀ n ≤ 24, rest.length + n < 1024 := by omega
  have hi256 : i < 2 ^ 256 := hi.trans hlength
  have hi1 : i + 1 < 2 ^ 256 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 =
      UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hi1
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (454 : UInt256).toNat = true := by
    rw [show (454 : UInt256).toNat = 454 by decide]
    exact jump441
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h441 : (454 : UInt256) = UInt256.ofNat 454 := by decide
  have hbody :
      loadBody s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
          returnDest rest =
        { loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
            returnDest rest with pc := UInt256.ofNat 463 } := by
    rfl
  unfold loadAfterByte
  rw [hbody]
  simp (config := { maxSteps := 800000 }) (disch := omega)
    [loadAfterBytePath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      loadAfterByte, loadLoop, loadMemory, loadWords, loadSaved,
      Accessors.calldataByteReturned, Accessors.calldataByteValue,
      loadByte, loadAt, loadLimbWord, loadReverseWord, loadShiftWord,
      loadStorePCs, hcode, hrun, hvalid, jump441,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Nat.mod_eq_of_lt,
      State.activeWordsAfterUInt256, UInt256.lt, UInt256.isTrue,
      List.exchange, Nat.add_assoc, hc, hlength, hi, hi256, hi1, hadd,
      hoffset, hone, h441]

theorem loadSetup_staticCost :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost loadSetupPath = 3 := by
  decide

theorem loadGuard_staticCost :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost loadGuardPath = 26 := by
  decide

theorem loadToByte_staticCost :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost loadToBytePath = 79 := by
  decide

theorem loadAfterByte_staticCost :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost loadAfterBytePath = 55 := by
  decide

theorem loadExit_staticCost :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost loadExitPath = 17 := by
  decide

def gasSteps_loadIteration (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffset : offset + i < 2 ^ 256)
    (hlength : length < 2 ^ 256) (hi : i < length)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
        returnDest rest)
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst (i + 1)
        returnDest rest) := by
  let loop := loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
    returnDest rest
  let body := loadBody s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
    returnDest rest
  let byteEntry := loadByteEntry s (UInt256.ofNat offset)
    (UInt256.ofNat length) dst i returnDest rest
  let afterByte := loadAfterByte s (UInt256.ofNat offset)
    (UInt256.ofNat length) dst i returnDest rest
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadGuardPath
      (by simpa [loop, loadLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [loop, loadLoop, State.fork] using hfork)
      (run_loadGuard s offset length dst returnDest i rest (by omega)
        (by omega) hlength hi hrun)
      (by simpa [loop, loadLoop] using hrun)
      (by simpa [loop, loadLoop, State.fork] using hnp)
  have htoByte := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadToBytePath (s := body)
      (by simpa [body, loadBody, loadLoop,
        Artifact.submissionArtifact] using hcode)
      (by simpa [body, loadBody, loadLoop, State.fork] using hfork)
      (run_loadToByte s offset length dst returnDest i rest hcap hoffset
        hlength hcode hrun)
      (by simpa [body, loadBody, loadLoop] using hrun)
      (by simpa [body, loadBody, loadLoop, State.fork] using hnp)
  have hbyte := Accessors.gasSteps_calldataByte body
    (UInt256.ofNat offset + UInt256.ofNat i) (UInt256.ofNat 0)
    (UInt256.ofNat 496) (loadSaved (UInt256.ofNat offset)
      (UInt256.ofNat length) dst i returnDest rest)
    (by simp [loadSaved]; omega)
    (by simpa [body, loadBody, loadLoop] using hcode)
    (by simpa [body, loadBody, loadLoop, State.fork] using hfork)
    (by simpa [body, loadBody, loadLoop] using hrun)
    (by simpa [body, loadBody, loadLoop, State.fork] using hnp)
    (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 496 < 2 ^ 256)]
      exact jump484)
  have hbyte' : Challenge.EvmProof.GasSteps byteEntry afterByte := by
    exact Challenge.EvmProof.GasSteps.cast hbyte
      (by simp [byteEntry, loadByteEntry, body])
      (by simp [afterByte, loadAfterByte, body])
  have hafter := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadAfterBytePath (s := afterByte)
      (by simpa [afterByte, loadAfterByte, body, loadBody, loadLoop,
        Accessors.calldataByteReturned,
        Artifact.submissionArtifact] using hcode)
      (by simpa [afterByte, loadAfterByte, body, loadBody, loadLoop,
        Accessors.calldataByteReturned, State.fork] using hfork)
      (by simpa [afterByte] using (run_loadAfterByte s offset length dst
        returnDest i rest hcap hoffset hlength hi hcode hrun))
      (by simpa [afterByte, loadAfterByte, body, loadBody, loadLoop,
        Accessors.calldataByteReturned] using hrun)
      (by simpa [afterByte, loadAfterByte, body, loadBody, loadLoop,
        Accessors.calldataByteReturned, State.fork] using hnp)
  exact hguard.trans <| htoByte.trans <| hbyte'.trans hafter

theorem gasSteps_loadIteration_cost_potential (s : State)
    (offset length : Nat) (dst returnDest : UInt256) (i : Nat)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hoffset : offset + i < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hi : i < length)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_loadIteration s offset length dst returnDest i rest hcap
        hoffset hlength hi hcode hfork hrun hnp).cost +
        MachineState.memCost
          (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
            returnDest rest).activeWords.toNat =
      190 + MachineState.memCost
        (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst (i + 1)
          returnDest rest).activeWords.toNat := by
  let loop := loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
    returnDest rest
  let body := loadBody s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
    returnDest rest
  let byteEntry := loadByteEntry s (UInt256.ofNat offset)
    (UInt256.ofNat length) dst i returnDest rest
  let afterByte := loadAfterByte s (UInt256.ofNat offset)
    (UInt256.ofNat length) dst i returnDest rest
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    loadGuardPath 26
      (run_loadGuard s offset length dst returnDest i rest (by omega)
        (by omega) hlength hi hrun)
      (by simpa [loop, loadLoop, State.fork] using hfork)
      (by decide) (by decide)
  have htoByte := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    loadToBytePath 79
      (run_loadToByte s offset length dst returnDest i rest hcap hoffset
        hlength hcode hrun)
      (by simpa [body, loadBody, loadLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hbyte := Accessors.gasSteps_calldataByte_cost_potential body
    (UInt256.ofNat offset + UInt256.ofNat i) (UInt256.ofNat 0)
    (UInt256.ofNat 496) (loadSaved (UInt256.ofNat offset)
      (UInt256.ofNat length) dst i returnDest rest)
    (by simp [loadSaved]; omega)
    (by simpa [body, loadBody, loadLoop] using hcode)
    (by simpa [body, loadBody, loadLoop, State.fork] using hfork)
    (by simpa [body, loadBody, loadLoop] using hrun)
    (by simpa [body, loadBody, loadLoop, State.fork] using hnp)
    (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 496 < 2 ^ 256)]
      exact jump484)
  have hafter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    loadAfterBytePath 55
      (run_loadAfterByte s offset length dst returnDest i rest hcap hoffset
        hlength hi hcode hrun)
      (by simpa [afterByte, loadAfterByte, body, loadBody, loadLoop,
        Accessors.calldataByteReturned, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_loadIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [loop, body, byteEntry, afterByte] at hguard htoByte hbyte hafter
  simp only [loadBody, loadByteEntry, loadAfterByte,
    Accessors.calldataByteEntry, Accessors.calldataByteReturned] at hguard htoByte hbyte hafter ⊢
  omega

def gasSteps_loadLoop (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffset : offset + length ≤ 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst 0
        returnDest rest)
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst length
        returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length)
      dst i returnDest rest) length (fun i hi =>
        gasSteps_loadIteration s offset length dst returnDest i rest hcap
          (by omega) hlength hi hcode hfork hrun hnp)

theorem gasSteps_loadLoop_cost_potential (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffset : offset + length ≤ 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_loadLoop s offset length dst returnDest rest hcap hoffset
        hlength hcode hfork hrun hnp).cost +
        MachineState.memCost
          (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst 0
            returnDest rest).activeWords.toNat =
      length * 190 + MachineState.memCost
        (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst length
          returnDest rest).activeWords.toNat := by
  let body := fun i (hi : i < length) => gasSteps_loadIteration s offset
    length dst returnDest i rest hcap (by omega) hlength hi hcode hfork hrun hnp
  have hcost : ∀ i (hi : i < length),
      (body i hi).cost + MachineState.memCost
          (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
            returnDest rest).activeWords.toNat =
        190 + MachineState.memCost
          (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst (i + 1)
            returnDest rest).activeWords.toNat := by
    intro i hi
    exact gasSteps_loadIteration_cost_potential s offset length dst returnDest
      i rest hcap (by omega) hlength hi hcode hfork hrun hnp
  have htelescope := Challenge.EvmProof.GasSteps.iterateBounded_cost_potential_eq
    length 190 (fun i => MachineState.memCost
      (loadLoop s (UInt256.ofNat offset) (UInt256.ofNat length) dst i
        returnDest rest).activeWords.toNat) body hcost
  unfold gasSteps_loadLoop
  simpa [body] using htelescope

def gasSteps_loadBigEndian (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffsetWord : offset < 2 ^ 256)
    (hoffset : offset + length ≤ 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (loadEntry s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest)
      (loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest) := by
  have hsetup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadSetupPath
      (by simpa [loadEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [loadEntry, State.fork] using hfork)
      (run_loadSetup s offset length dst returnDest rest (by omega) hrun)
      (by simpa [loadEntry] using hrun)
      (by simpa [loadEntry, State.fork] using hnp)
  have hloop := gasSteps_loadLoop s offset length dst returnDest rest hcap
    hoffset hlength hcode hfork hrun hnp
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadGuardPath
      (by simpa [loadLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [loadLoop, State.fork] using hfork)
      (run_loadFinishGuard s offset length dst returnDest rest (by omega)
        hoffsetWord hlength hcode hrun)
      (by simpa [loadLoop] using hrun)
      (by simpa [loadLoop, State.fork] using hnp)
  have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadExitPath
      (by simpa [loadLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [loadLoop, State.fork] using hfork)
      (run_loadExit s offset length dst returnDest rest (by omega) hoffsetWord
        hlength hcode hrun hvalid)
      (by simpa [loadLoop] using hrun)
      (by simpa [loadLoop, State.fork] using hnp)
  exact hsetup.trans <| hloop.trans <| hfinish.trans hexit

theorem gasSteps_loadBigEndian_cost_potential (s : State)
    (offset length : Nat) (dst returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffsetWord : offset < 2 ^ 256)
    (hoffset : offset + length ≤ 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    (gasSteps_loadBigEndian s offset length dst returnDest rest hcap
        hoffsetWord hoffset hlength hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost s.activeWords.toNat =
      (46 + length * 190) + MachineState.memCost
        (loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length) dst
          returnDest rest).activeWords.toNat := by
  have hsetup := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    loadSetupPath 3
      (run_loadSetup s offset length dst returnDest rest (by omega) hrun)
      (by simpa [loadEntry, State.fork] using hfork)
      (by decide) (by decide)
  have hloop := gasSteps_loadLoop_cost_potential s offset length dst returnDest
    rest hcap hoffset hlength hcode hfork hrun hnp
  have hfinish := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    loadGuardPath 26
      (run_loadFinishGuard s offset length dst returnDest rest (by omega)
        hoffsetWord hlength hcode hrun)
      (by simpa [loadLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    loadExitPath 17
      (run_loadExit s offset length dst returnDest rest (by omega) hoffsetWord
        hlength hcode hrun hvalid)
      (by simpa [loadLoop, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_loadBigEndian
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [loadEntry, loadLoop, loadReturned, loadMemory, loadWords] at hsetup hloop hfinish hexit ⊢
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad
