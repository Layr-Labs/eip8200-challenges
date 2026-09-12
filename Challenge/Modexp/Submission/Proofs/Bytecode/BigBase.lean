import Challenge.Modexp.Submission.Proofs.Bytecode.BigModulus
set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000
/-! # Certified base-conversion path -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBase

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

def toClearDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 555 .JUMPDEST, pushAt 556 2 698,
   opAt 557 (.Dup ⟨2, by decide⟩), pushAt 558 2 3072,
   pushAt 559 1 14, opAt 560 .JUMP]

def startBaseLoopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 561 .JUMPDEST, pushAt 562 1 1, pushAt 563 2 3072,
   opAt 564 .MSTORE, pushAt 565 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 566 .JUMPDEST, opAt 567 (.Dup ⟨3, by decide⟩),
   opAt 568 (.Dup ⟨1, by decide⟩), opAt 569 .LT, opAt 570 .ISZERO,
   pushAt 571 2 796, opAt 572 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 573 (.Dup ⟨0, by decide⟩), opAt 574 (.Dup ⟨7, by decide⟩),
   opAt 575 .ADD, opAt 576 (.Dup ⟨0, by decide⟩),
   opAt 577 .CALLDATALOAD, pushAt 578 0 0, opAt 579 .BYTE,
   pushAt 580 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 581 .JUMPDEST, pushAt 582 1 8, opAt 583 (.Dup ⟨1, by decide⟩),
   opAt 584 .LT, opAt 585 .ISZERO, pushAt 586 2 782,
   opAt 587 .JUMPI]

def innerToDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 588 2 747, opAt 589 (.Dup ⟨6, by decide⟩),
   pushAt 590 0 0, pushAt 591 1 1, pushAt 592 2 1024,
   opAt 593 (.Dup ⟨0, by decide⟩), pushAt 594 1 85, opAt 595 .JUMP]

def innerToAddBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 596 .JUMPDEST, pushAt 597 2 771,
   opAt 598 (.Dup ⟨6, by decide⟩), pushAt 599 0 0,
   pushAt 600 1 1, opAt 601 (.Dup ⟨5, by decide⟩),
   opAt 602 (.Dup ⟨5, by decide⟩), pushAt 603 1 7,
   opAt 604 .SUB, opAt 605 .SHR, opAt 606 .AND,
   pushAt 607 2 3072, pushAt 608 2 1024,
   pushAt 609 1 85, opAt 610 .JUMP]

def innerAfterBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 611 .JUMPDEST, pushAt 612 1 1,
   opAt 613 (.Dup ⟨1, by decide⟩), opAt 614 .ADD,
   opAt 615 (.Swap ⟨0, by decide⟩), opAt 616 .POP,
   pushAt 617 2 723, opAt 618 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 619 .JUMPDEST, opAt 620 .POP, opAt 621 .POP, opAt 622 .POP,
   pushAt 623 1 1, opAt 624 (.Dup ⟨1, by decide⟩), opAt 625 .ADD,
   opAt 626 (.Swap ⟨0, by decide⟩), opAt 627 .POP,
   pushAt 628 2 706, opAt 629 .JUMP]

def outerFinishToAccumulatorPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 630 .JUMPDEST, opAt 631 .POP, pushAt 632 2 814,
   opAt 633 (.Dup ⟨2, by decide⟩), pushAt 634 0 0,
   pushAt 635 1 1, pushAt 636 2 3072, pushAt 637 2 2048,
   pushAt 638 1 85, opAt 639 .JUMP]

def frame (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : List UInt256 :=
  [accumulator, UInt256.ofNat count] ++ rest

def afterClearDouble (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  BigHelpers.clearReturned (BigModulus.scanNonzero s count rest) 3072 count
    698 (frame accumulator count rest)

def baseLoopEntry (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  let cleared := afterClearDouble s accumulator count rest
  { cleared with
    pc := UInt256.ofNat 706
    stack := [0, accumulator, UInt256.ofNat count] ++ rest
    memory := MachineState.writeBytes cleared.memory
      (Data.Bytes.natToBytesPadded 1 32) 3072
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      cleared.activeWords.toNat 3072 32) }

def baseBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) 1

def loadedBaseByte (s : State) (baseOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (baseOff + i))

def bitProgress (count : Nat) (byte : UInt256) : Nat → State → State
  | 0, s => s
  | j + 1, s =>
      let before := bitProgress count byte j s
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 747 []
      BigHelpers.addReturned doubled 1024 3072 (baseBit byte j) 0 count 771 []

def baseProgress (count baseOff : Nat) : Nat → State → State
  | 0, s => s
  | i + 1, s =>
      let before := baseProgress count baseOff i s
      bitProgress count (loadedBaseByte before baseOff i) 8 before

@[simp] theorem bitProgress_halt (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) : (bitProgress count byte j s).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [bitProgress, BigHelpers.addReturned, ih]

@[simp] theorem bitProgress_executionEnv (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (bitProgress count byte j s).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [bitProgress, BigHelpers.addReturned, ih]

@[simp] theorem bitProgress_activeFork (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (bitProgress count byte j s).fork = s.fork := by
  simp [State.fork]

@[simp] theorem baseProgress_halt (count baseOff i : Nat) (s : State) :
    (baseProgress count baseOff i s).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [baseProgress, ih]

@[simp] theorem baseProgress_executionEnv (count baseOff i : Nat) (s : State) :
    (baseProgress count baseOff i s).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [baseProgress, ih]

@[simp] theorem baseProgress_activeFork (count baseOff i : Nat) (s : State) :
    (baseProgress count baseOff i s).fork = s.fork := by
  simp [State.fork]

@[simp] theorem loadedBaseByte_baseProgress (count baseOff i j : Nat)
    (s : State) :
    loadedBaseByte (baseProgress count baseOff j s) baseOff i =
      loadedBaseByte s baseOff i := by
  simp [loadedBaseByte]

def outerLoop (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 706
           stack := [UInt256.ofNat i, accumulator, UInt256.ofNat count,
             UInt256.ofNat baseSize] ++ rest }

def outerBody (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulator count baseSize rest i with
      pc := UInt256.ofNat 715 }

def innerLoop (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  let progress := bitProgress count byte j s
  { progress with
    pc := UInt256.ofNat 723
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
      UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest }

def innerBody (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest j with
      pc := UInt256.ofNat 733 }

def innerExit (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest 8 with
      pc := UInt256.ofNat 782 }

def outerExit (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) : State :=
  { outerLoop s accumulator count baseSize rest baseSize with
      pc := UInt256.ofNat 796 }

def innerFrame (accumulator : UInt256) (count baseSize i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
    UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest

def doubledReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 747
    (innerFrame accumulator count baseSize i j offset byte rest)

def bitReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (doubledReturned s accumulator count baseSize i j offset byte rest)
    1024 3072 (baseBit byte j) 0 count 771
    (innerFrame accumulator count baseSize i j offset byte rest)

@[simp] private theorem baseSetupPCs (i : Nat)
    (hi : 555 ≤ i) (hii : i ≤ 565) :
    Artifact.submissionArtifact.instructionPC i =
      ([687,688,691,692,695,697,698,699,701,704,705] : List Nat)[i - 555]! := by
  interval_cases i <;> decide

@[simp] private theorem baseLoopPCs (i : Nat)
    (hi : 566 ≤ i) (hii : i ≤ 639) :
    Artifact.submissionArtifact.instructionPC i =
      ([706,707,708,709,710,711,714,715,716,717,718,719,720,721,722,723,724,726,727,728,729,732,733,736,737,738,740,743,744,746,747,748,751,752,753,755,756,757,759,760,761,762,765,768,770,771,772,774,775,776,777,778,781,782,783,784,785,786,788,789,790,791,792,795,796,797,798,801,802,803,805,808,811,813] : List Nat)[i - 566]! := by
  interval_cases i <;> decide

private theorem jump104 :
    Decode.isValidJumpDest submissionBytecode 85 = true :=
  Artifact.isValidJumpDest_index 74 (by rfl)

private theorem jump831 :
    Decode.isValidJumpDest submissionBytecode 706 = true :=
  Artifact.isValidJumpDest_index 566 (by rfl)

private theorem jump848 :
    Decode.isValidJumpDest submissionBytecode 723 = true :=
  Artifact.isValidJumpDest_index 581 (by rfl)

private theorem jump875 :
    Decode.isValidJumpDest submissionBytecode 747 = true :=
  Artifact.isValidJumpDest_index 596 (by rfl)

private theorem jump900 :
    Decode.isValidJumpDest submissionBytecode 771 = true :=
  Artifact.isValidJumpDest_index 611 (by rfl)

private theorem jump911 :
    Decode.isValidJumpDest submissionBytecode 782 = true :=
  Artifact.isValidJumpDest_index 619 (by rfl)

private theorem jump925 :
    Decode.isValidJumpDest submissionBytecode 796 = true :=
  Artifact.isValidJumpDest_index 630 (by rfl)

private theorem jump944 :
    Decode.isValidJumpDest submissionBytecode 814 = true :=
  Artifact.isValidJumpDest_index 640 (by rfl)

private theorem jump19 :
    Decode.isValidJumpDest submissionBytecode 14 = true :=
  Artifact.isValidJumpDest_index 12 (by rfl)

private theorem jump823 :
    Decode.isValidJumpDest submissionBytecode 698 = true :=
  Artifact.isValidJumpDest_index 561 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_toClearDouble (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClearDoublePath
      (BigModulus.scanNonzero s count rest) =
      some (BigHelpers.clearEntry (BigModulus.scanNonzero s count rest)
        3072 count 698
        (frame accumulator count rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h19 : (14 : UInt256).toNat = 14 := by decide
  have h19Word : (14 : UInt256) = UInt256.ofNat 14 := by decide
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
  have h823 : (698 : UInt256).toNat = 698 := by decide
  have h823Word : (698 : UInt256) = UInt256.ofNat 698 := by decide
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

set_option linter.unusedSimpArgs false in
theorem run_outerGuard (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (hbase : baseSize < 2 ^ 256)
    (hi : i < baseSize) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulator count baseSize rest i) =
      some (outerBody s accumulator count baseSize rest i) := by
  have hi256 : i < 2 ^ 256 := hi.trans hbase
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat baseSize) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hbase, if_pos hi]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerBody,
    baseLoopPCs, hrun, hlt, honeNat, hc4, hc5, hc6, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerToInner (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1013) (hbaseOff : baseOff + i < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerToInnerPath
      (outerBody s accumulator count baseSize
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) i) =
      some (innerLoop s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) (loadedBaseByte s baseOff i)
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) 0) := by
  have hi : i < 2 ^ 256 := by omega
  have hbase : baseOff < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := baseOff) (by omega)
  have hoffNat : (UInt256.ofNat (baseOff + i)).toNat = baseOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbaseOff]
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [outerToInnerPath, opAt, pushAt, wfOp, outerBody, outerLoop,
    innerLoop, bitProgress, loadedBaseByte, baseLoopPCs, hrun, hadd,
    hoffNat, hzero, h0Word, hc7, hc8, hc9, hc10,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

set_option linter.unusedSimpArgs false in
theorem run_innerGuard (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1013) (hj : j < 8)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulator count baseSize i offset byte rest j) =
      some (innerBody s accumulator count baseSize i offset byte rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat j) 8 = 1 := by
    have hj256 : j < 2 ^ 256 := by omega
    have h8 : (8 : UInt256).toNat = 8 := by decide
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hj256, h8, if_pos hj]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerBody,
    baseLoopPCs, hrun, hlt, honeNat, hc7, hc8, hc9, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerToDouble (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerToDoublePath
      (innerBody s accumulator count baseSize i offset byte rest j) =
      some (BigHelpers.addEntry
        (innerBody s accumulator count baseSize i offset byte rest j)
        1024 1024 1 0 count 747
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have h104 : (85 : UInt256).toNat = 85 := by decide
  have h104Word : (85 : UInt256) = UInt256.ofNat 85 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [innerToDoublePath, opAt, pushAt, wfOp, innerBody, innerLoop,
    BigHelpers.addEntry, innerFrame, baseLoopPCs, hcode, hrun, jump104,
    h104, h104Word, hzero, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerToAddBit (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerToAddBitPath
      (doubledReturned s accumulator count baseSize i j offset byte rest) =
      some (BigHelpers.addEntry
        (doubledReturned s accumulator count baseSize i j offset byte rest)
        1024 3072 (baseBit byte j) 0 count 771
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hj7 : j ≤ 7 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj7
    (by norm_num : 7 < 2 ^ 256)
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have h104 : (85 : UInt256).toNat = 85 := by decide
  have h104Word : (85 : UInt256) = UInt256.ofNat 85 := by decide
  have h875 : (747 : UInt256).toNat = 747 := by decide
  have h875Word : (747 : UInt256) = UInt256.ofNat 747 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  simp [innerToAddBitPath, opAt, pushAt, wfOp, doubledReturned,
    innerBody, innerLoop, BigHelpers.addReturned, BigHelpers.addEntry,
    innerFrame, baseBit, baseLoopPCs, hcode, hrun, jump104, hsub,
    h104, h104Word, h875, h875Word, hzero, hone, hseven,
    hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerAfterBit (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1013) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerAfterBitPath
      (bitReturned s accumulator count baseSize i j offset byte rest) =
      some (innerLoop s accumulator count baseSize i offset byte rest (j + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) (by omega : j + 1 < 2 ^ 256)
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h848 : (723 : UInt256).toNat = 723 := by decide
  have h848Word : (723 : UInt256) = UInt256.ofNat 723 := by decide
  have h900 : (771 : UInt256).toNat = 771 := by decide
  have h900Word : (771 : UInt256) = UInt256.ofNat 771 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [innerAfterBitPath, opAt, pushAt, wfOp, bitReturned,
    doubledReturned, innerBody, innerLoop, innerFrame, bitProgress,
    BigHelpers.addReturned, baseLoopPCs, hcode, hrun, jump848,
    hinc, h848, h848Word, h900, h900Word, hone, hc7, hc8, hc9,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, List.exchange, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerFinishGuard (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulator count baseSize i offset byte rest 8) =
      some (innerExit s accumulator count baseSize i offset byte rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h911 : (782 : UInt256).toNat = 782 := by decide
  have h911Word : (782 : UInt256) = UInt256.ofNat 782 := by decide
  have h8Nat : (8 : UInt256).toNat = 8 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerExit,
    baseLoopPCs, hcode, hrun, jump911, hzeroFalse, h911, h911Word,
    h8Nat, hc7, hc8, hc9, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerFinish (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerFinishPath
      (innerExit s accumulator count baseSize i offset byte rest) =
      some (outerLoop (bitProgress count byte 8 s) accumulator count baseSize
        rest (i + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h831 : (706 : UInt256).toNat = 706 := by decide
  have h831Word : (706 : UInt256) = UInt256.ofNat 706 := by decide
  have h911 : (782 : UInt256).toNat = 782 := by decide
  have h911Word : (782 : UInt256) = UInt256.ofNat 782 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [innerFinishPath, opAt, pushAt, wfOp, innerExit, innerLoop,
    outerLoop, baseLoopPCs, hcode, hrun, jump831, hinc,
    h831, h831Word, h911, h911Word, hone, hc4, hc5, hc6, hc7, hc8,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, List.exchange, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerFinishGuard (s : State) (accumulator : UInt256)
    (count baseSize : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (_hbase : baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulator count baseSize rest baseSize) =
      some (outerExit s accumulator count baseSize rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h925 : (796 : UInt256).toNat = 796 := by decide
  have h925Word : (796 : UInt256) = UInt256.ofNat 796 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerExit,
    baseLoopPCs, hcode, hrun, jump925, hzeroFalse, h925, h925Word,
    hc4, hc5, hc6, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerFinishToAccumulator (s : State) (accumulator : UInt256)
    (count baseSize : Nat) (rest : List UInt256)
    (hcap : rest.length < 1009) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerFinishToAccumulatorPath
      (outerExit s accumulator count baseSize rest) =
      some (BigHelpers.addEntry (outerExit s accumulator count baseSize rest)
        2048 3072 1 0 count 814
        ([accumulator, UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have h104 : (85 : UInt256).toNat = 85 := by decide
  have h104Word : (85 : UInt256) = UInt256.ofNat 85 := by decide
  have h925 : (796 : UInt256).toNat = 796 := by decide
  have h925Word : (796 : UInt256) = UInt256.ofNat 796 := by decide
  have h944Word : (814 : UInt256) = UInt256.ofNat 814 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [outerFinishToAccumulatorPath, opAt, pushAt, wfOp, outerExit,
    outerLoop, BigHelpers.addEntry, baseLoopPCs, hcode, hrun, jump104,
    h104, h104Word, h925, h925Word, h944Word, hzero,
    hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_innerIteration (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulator count baseSize i offset byte rest j)
      (innerLoop s accumulator count baseSize i offset byte rest (j + 1)) := by
  have hframe : (innerFrame accumulator count baseSize i j offset byte rest).length <
      1000 := by
    simp [innerFrame]
    omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerGuardPath
      (by simpa [innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerLoop, State.fork] using hfork)
      (run_innerGuard s accumulator count baseSize i j offset byte rest
        (by omega) hj hrun)
      (by simpa [innerLoop] using hrun)
      (by simpa [innerLoop, State.fork] using hnp)
  have htoDouble := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerToDoublePath
      (by simpa [innerBody, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerBody, innerLoop, State.fork] using hfork)
      (run_innerToDouble s accumulator count baseSize i j offset byte rest
        (by omega) hcode hrun)
      (by simpa [innerBody, innerLoop] using hrun)
      (by simpa [innerBody, innerLoop, State.fork] using hnp)
  have hdouble := BigHelpers.gasSteps_addMaskedMod
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 747
    (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
    (by simpa [innerBody, innerLoop] using hcode)
    (by simpa [innerBody, innerLoop, State.fork] using hfork)
    (by simpa [innerBody, innerLoop] using hrun)
    (by simpa [innerBody, innerLoop, State.fork] using hnp) jump875
  have htoBit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerToAddBitPath
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hfork)
      (run_innerToAddBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop] using hrun)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hnp)
  have hbit := BigHelpers.gasSteps_addMaskedMod
    (doubledReturned s accumulator count baseSize i j offset byte rest)
    1024 3072 (baseBit byte j) 0 count 771
    (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop] using hcode)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop, State.fork] using hfork)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop] using hrun)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop, State.fork] using hnp) jump900
  have hafter := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerAfterBitPath
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, State.fork] using hfork)
      (run_innerAfterBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop] using hrun)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, State.fork] using hnp)
  exact hguard.trans <| htoDouble.trans <| hdouble.trans <|
    htoBit.trans <| hbit.trans hafter

theorem gasSteps_innerIteration_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize i j : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_innerIteration s accumulator count baseSize i j offset byte rest
      hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (innerLoop s accumulator count baseSize i offset byte rest j).activeWords.toNat =
      (425 + count * 906) + MachineState.memCost
        (innerLoop s accumulator count baseSize i offset byte rest
          (j + 1)).activeWords.toNat := by
  have hframe : (innerFrame accumulator count baseSize i j offset byte rest).length <
      1000 := by simp [innerFrame]; omega
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    innerGuardPath 26
      (run_innerGuard s accumulator count baseSize i j offset byte rest
        (by omega) hj hrun)
      (by simpa [innerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have htoDouble := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    innerToDoublePath 28
      (run_innerToDouble s accumulator count baseSize i j offset byte rest
        (by omega) hcode hrun)
      (by simpa [innerBody, innerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hdouble := BigHelpers.gasSteps_addMaskedMod_cost_potential
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 747
    (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
    (by simpa [innerBody, innerLoop] using hcode)
    (by simpa [innerBody, innerLoop, State.fork] using hfork)
    (by simpa [innerBody, innerLoop] using hrun)
    (by simpa [innerBody, innerLoop, State.fork] using hnp) jump875
  have htoBit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    innerToAddBitPath 47
      (run_innerToAddBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hbit := BigHelpers.gasSteps_addMaskedMod_cost_potential
    (doubledReturned s accumulator count baseSize i j offset byte rest)
    1024 3072 (baseBit byte j) 0 count 771
    (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop] using hcode)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop, State.fork] using hfork)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop] using hrun)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop, State.fork] using hnp) jump900
  have hafter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    innerAfterBitPath 26
      (run_innerAfterBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hguard' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost innerGuardPath
          (innerLoop s accumulator count baseSize i offset byte rest j) +
        MachineState.memCost
          (innerLoop s accumulator count baseSize i offset byte rest j).activeWords.toNat =
      26 + MachineState.memCost
        (innerBody s accumulator count baseSize i offset byte rest j).activeWords.toNat := by
    simpa [innerLoop, innerBody] using hguard
  have htoDouble' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost innerToDoublePath
          (innerBody s accumulator count baseSize i offset byte rest j) +
        MachineState.memCost
          (innerBody s accumulator count baseSize i offset byte rest j).activeWords.toNat =
      28 + MachineState.memCost
        (innerBody s accumulator count baseSize i offset byte rest j).activeWords.toNat := by
    simpa [BigHelpers.addEntry] using htoDouble
  have hdouble' :
      (BigHelpers.gasSteps_addMaskedMod
        (innerBody s accumulator count baseSize i offset byte rest j)
        1024 1024 1 0 count 747
        (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
        (by simpa [innerBody, innerLoop] using hcode)
        (by simpa [innerBody, innerLoop, State.fork] using hfork)
        (by simpa [innerBody, innerLoop] using hrun)
        (by simpa [innerBody, innerLoop, State.fork] using hnp) jump875).cost +
          MachineState.memCost
            (innerBody s accumulator count baseSize i offset byte rest j).activeWords.toNat =
      (149 + count * 453) + MachineState.memCost
        (doubledReturned s accumulator count baseSize i j offset byte rest).activeWords.toNat := by
    simpa [doubledReturned] using hdouble
  have htoBit' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost innerToAddBitPath
          (doubledReturned s accumulator count baseSize i j offset byte rest) +
        MachineState.memCost
          (doubledReturned s accumulator count baseSize i j offset byte rest).activeWords.toNat =
      47 + MachineState.memCost
        (doubledReturned s accumulator count baseSize i j offset byte rest).activeWords.toNat := by
    simpa [BigHelpers.addEntry] using htoBit
  have hbit' :
      (BigHelpers.gasSteps_addMaskedMod
        (doubledReturned s accumulator count baseSize i j offset byte rest)
        1024 3072 (baseBit byte j) 0 count 771
        (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
        (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
          innerLoop] using hcode)
        (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
          innerLoop, State.fork] using hfork)
        (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
          innerLoop] using hrun)
        (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
          innerLoop, State.fork] using hnp) jump900).cost +
          MachineState.memCost
            (doubledReturned s accumulator count baseSize i j offset byte rest).activeWords.toNat =
      (149 + count * 453) + MachineState.memCost
        (bitReturned s accumulator count baseSize i j offset byte rest).activeWords.toNat := by
    simpa [bitReturned] using hbit
  unfold gasSteps_innerIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

def gasSteps_innerLoop (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulator count baseSize i offset byte rest 0)
      (innerLoop s accumulator count baseSize i offset byte rest 8) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded 8 fun j hj =>
    gasSteps_innerIteration s accumulator count baseSize i j offset byte rest
      hcap hcount hj hcode hfork hrun hnp

theorem gasSteps_innerLoop_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_innerLoop s accumulator count baseSize i offset byte rest hcap
      hcount hcode hfork hrun hnp).cost + MachineState.memCost
        (innerLoop s accumulator count baseSize i offset byte rest 0).activeWords.toNat =
      8 * (425 + count * 906) + MachineState.memCost
        (innerLoop s accumulator count baseSize i offset byte rest 8).activeWords.toNat := by
  unfold gasSteps_innerLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro j hj
  exact gasSteps_innerIteration_cost_potential s accumulator count baseSize i j
    offset byte rest hcap hcount hj hcode hfork hrun hnp

def gasSteps_baseByte (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hi : i < baseSize)
    (hoff : baseOff + i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulator count baseSize
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) i)
      (outerLoop (bitProgress count (loadedBaseByte s baseOff i) 8 s)
        accumulator count baseSize
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
        (i + 1)) := by
  let byte := loadedBaseByte s baseOff i
  let fullRest := [UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest
  have hfull : fullRest.length < 993 := by simp [fullRest]; omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerGuardPath
      (by simpa [outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerLoop, State.fork] using hfork)
      (run_outerGuard s accumulator count baseSize i fullRest
        (by simp [fullRest]; omega) hbase hi hrun)
      (by simpa [outerLoop] using hrun)
      (by simpa [outerLoop, State.fork] using hnp)
  have hload := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerToInnerPath
      (by simpa [outerBody, outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerBody, outerLoop, State.fork] using hfork)
      (run_outerToInner s accumulator count baseSize e m baseOff i rest
        (by omega) hoff hrun)
      (by simpa [outerBody, outerLoop] using hrun)
      (by simpa [outerBody, outerLoop, State.fork] using hnp)
  have hinner := gasSteps_innerLoop s accumulator count baseSize i
    (UInt256.ofNat (baseOff + i)) byte fullRest hfull hcount hcode hfork hrun hnp
  have hfinishGuard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerGuardPath
      (by simpa [innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerLoop, State.fork] using hfork)
      (run_innerFinishGuard s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) byte fullRest
        (by simp [fullRest]; omega) hcode hrun)
      (by simpa [innerLoop] using hrun)
      (by simpa [innerLoop, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerFinishPath
      (by simpa [innerExit, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerExit, innerLoop, State.fork] using hfork)
      (run_innerFinish s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) byte fullRest
        (by simp [fullRest]; omega) (by omega) hcode hrun)
      (by simpa [innerExit, innerLoop] using hrun)
      (by simpa [innerExit, innerLoop, State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (hload.trans (hinner.trans (hfinishGuard.trans hfinish))))
    (by simp [fullRest]) (by simp [byte, fullRest])

set_option linter.unusedSimpArgs false in
theorem gasSteps_baseByte_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff i : Nat)
    (rest : List UInt256) (hcap : rest.length < 990)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hi : i < baseSize) (hoff : baseOff + i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_baseByte s accumulator count baseSize e m baseOff i rest hcap
      hcount hbase hi hoff hcode hfork hrun hnp).cost + MachineState.memCost
        (outerLoop s accumulator count baseSize
          ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
          i).activeWords.toNat =
      (3506 + count * 7248) + MachineState.memCost
        (outerLoop (bitProgress count (loadedBaseByte s baseOff i) 8 s)
          accumulator count baseSize
          ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
          (i + 1)).activeWords.toNat := by
  let byte := loadedBaseByte s baseOff i
  let fullRest := [UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest
  have hfull : fullRest.length < 993 := by simp [fullRest]; omega
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    outerGuardPath 26
      (run_outerGuard s accumulator count baseSize i fullRest
        (by simp [fullRest]; omega) hbase hi hrun)
      (by simpa [outerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hload := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    outerToInnerPath 22
      (run_outerToInner s accumulator count baseSize e m baseOff i rest
        (by omega) hoff hrun)
      (by simpa [outerBody, outerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hinner := gasSteps_innerLoop_cost_potential s accumulator count baseSize i
    (UInt256.ofNat (baseOff + i)) byte fullRest hfull hcount hcode hfork hrun hnp
  have hfinishGuard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    innerGuardPath 26
      (run_innerFinishGuard s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) byte fullRest
        (by simp [fullRest]; omega) hcode hrun)
      (by simpa [innerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hfinish := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    innerFinishPath 32
      (run_innerFinish s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) byte fullRest
        (by simp [fullRest]; omega) (by omega) hcode hrun)
      (by simpa [innerExit, innerLoop, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_baseByte
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [outerLoop, outerBody, innerLoop, innerExit, bitProgress] at hguard hload hinner hfinishGuard hfinish ⊢
  simp only [byte, fullRest] at hguard hload hinner hfinishGuard hfinish ⊢
  omega

def gasSteps_baseSetup (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 998)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (BigModulus.scanNonzero s count rest)
      (baseLoopEntry s accumulator count rest) := by
  have hcapRaw : rest.length < 1016 := by omega
  have hframe : (frame accumulator count rest).length < 1017 := by
    simp [frame]
    omega
  have hcodeScan : (BigModulus.scanNonzero s count rest).executionEnv.code =
      submissionBytecode := by
    simpa [BigModulus.scanNonzero] using hcode
  have hforkScan : (BigModulus.scanNonzero s count rest).fork = .Osaka := by
    simpa [BigModulus.scanNonzero, State.fork] using hfork
  have hrunScan : (BigModulus.scanNonzero s count rest).halt = .Running := by
    simpa [BigModulus.scanNonzero] using hrun
  have hnpScan : Precompile.isPrecompileWithConfig (BigModulus.scanNonzero s count rest).executionEnv.precompileConfig (BigModulus.scanNonzero s count rest).executionEnv.fork
      (BigModulus.scanNonzero s count rest).executionEnv.codeAddr = false := by
    simpa [BigModulus.scanNonzero, State.fork] using hnp
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka toClearDoublePath
      (by simpa [BigModulus.scanNonzero, Artifact.submissionArtifact] using hcode)
      (by simpa [BigModulus.scanNonzero, State.fork] using hfork)
      (run_toClearDouble s accumulator count rest hcapRaw hacc hcode hrun)
      (by simpa [BigModulus.scanNonzero] using hrun)
      (by simpa [BigModulus.scanNonzero, State.fork] using hnp)).trans <|
    (BigHelpers.gasSteps_clear (BigModulus.scanNonzero s count rest) 3072
      count 698 (frame accumulator count rest) hframe hcount hcodeScan
      hforkScan hrunScan hnpScan jump823).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startBaseLoopPath
        (by simpa [afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, Artifact.submissionArtifact] using hcode)
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
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
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
      submissionBytecode := by simpa [BigModulus.scanNonzero] using hcode
  have hforkScan : (BigModulus.scanNonzero s count rest).fork = .Osaka := by
    simpa [BigModulus.scanNonzero, State.fork] using hfork
  have hrunScan : (BigModulus.scanNonzero s count rest).halt = .Running := by
    simpa [BigModulus.scanNonzero] using hrun
  have hnpScan : Precompile.isPrecompileWithConfig (BigModulus.scanNonzero s count rest).executionEnv.precompileConfig (BigModulus.scanNonzero s count rest).executionEnv.fork
      (BigModulus.scanNonzero s count rest).executionEnv.codeAddr = false := by
    simpa [BigModulus.scanNonzero, State.fork] using hnp
  have hraw := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    toClearDoublePath 21
      (run_toClearDouble s accumulator count rest hcapRaw hacc hcode hrun)
      (by simpa [BigModulus.scanNonzero, State.fork] using hfork)
      (by decide) (by decide)
  have hclear := BigHelpers.gasSteps_clear_cost_potential
    (BigModulus.scanNonzero s count rest) 3072 count 698
      (frame accumulator count rest) hframe hcount hcodeScan hforkScan
      hrunScan hnpScan jump823
  have htail := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    startBaseLoopPath 12
      (run_startBaseLoop s accumulator count rest hcapRaw hrun)
      (by simpa [afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_baseSetup
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [BigModulus.scanNonzero, afterClearDouble, baseLoopEntry,
    BigHelpers.clearEntry, BigHelpers.clearReturned] at hraw hclear htail ⊢
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBase
