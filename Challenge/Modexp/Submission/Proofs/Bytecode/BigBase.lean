import Challenge.Modexp.Submission.Proofs.Bytecode.BigModulus
import Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
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
  [opAt 632 .JUMPDEST, pushAt 633 2 1518,
   opAt 634 (.Dup ⟨2, by decide⟩), pushAt 635 2 3072,
   pushAt 636 2 19, opAt 637 .JUMP]

def startBaseLoopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 638 .JUMPDEST, pushAt 639 1 1, pushAt 640 2 3072,
   opAt 641 .MSTORE, pushAt 642 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 643 .JUMPDEST, opAt 644 (.Dup ⟨3, by decide⟩),
   opAt 645 (.Dup ⟨1, by decide⟩), opAt 646 .EQ, opAt 647 .JUMPDEST,
   pushAt 648 2 925, opAt 649 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 650 (.Dup ⟨0, by decide⟩), opAt 651 (.Dup ⟨7, by decide⟩),
   opAt 652 .ADD, opAt 653 (.Dup ⟨0, by decide⟩),
   opAt 654 .CALLDATALOAD, pushAt 655 0 0, opAt 656 .BYTE,
   pushAt 657 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 658 .JUMPDEST, pushAt 659 1 8, opAt 660 (.Dup ⟨1, by decide⟩),
   opAt 661 .EQ, opAt 662 .JUMPDEST, pushAt 663 2 911,
   opAt 664 .JUMPI]

def innerToDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 665 2 875, opAt 666 (.Dup ⟨6, by decide⟩),
   pushAt 667 0 0, pushAt 668 1 1, pushAt 669 2 1024,
   pushAt 670 2 1024, pushAt 671 2 1473, opAt 672 .JUMP]

def innerToAddBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 673 .JUMPDEST, pushAt 674 2 900,
   opAt 675 (.Dup ⟨6, by decide⟩), pushAt 676 0 0,
   pushAt 677 1 1, opAt 678 (.Dup ⟨5, by decide⟩),
   opAt 679 (.Dup ⟨5, by decide⟩), pushAt 680 1 7,
   opAt 681 .SUB, opAt 682 .SHR, opAt 683 .AND,
   pushAt 684 2 3072, pushAt 685 2 1024,
   pushAt 686 2 1461, opAt 687 .JUMP]

/-- Appended trampoline `T2` at pc 1461: it
re-tests the masked-add's `take` argument and enters `addMaskedMod` only when
it is set.  The base-conversion call site pushes exactly the same six-slot
frame, so the very same routine serves it. -/
def baseT2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1075 .JUMPDEST, opAt 1076 (.Dup ⟨2, by decide⟩),
   pushAt 1077 2 104, opAt 1078 .JUMPI]

/-- `T2`'s zero-bit tail: drop the five arguments and return. -/
def baseT2SkipPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1079 .POP, opAt 1080 .POP, opAt 1081 .POP, opAt 1082 .POP,
   opAt 1083 .POP, opAt 1084 .JUMP]

def innerAfterBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 688 .JUMPDEST, pushAt 689 1 1,
   opAt 690 (.Dup ⟨1, by decide⟩), opAt 691 .ADD,
   opAt 692 (.Swap ⟨0, by decide⟩), opAt 693 .POP,
   pushAt 694 2 848, opAt 695 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 696 .JUMPDEST, opAt 697 .POP, opAt 698 .POP, opAt 699 .POP,
   pushAt 700 1 1, opAt 701 (.Dup ⟨1, by decide⟩), opAt 702 .ADD,
   opAt 703 (.Swap ⟨0, by decide⟩), opAt 704 .POP,
   pushAt 705 2 831, opAt 706 .JUMP]

def outerFinishToAccumulatorPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 707 .JUMPDEST, opAt 708 .POP, pushAt 709 2 1335,
   opAt 710 (.Dup ⟨2, by decide⟩), pushAt 711 0 0,
   pushAt 712 1 1, pushAt 713 2 3072, pushAt 714 2 2048,
   pushAt 715 2 104, opAt 716 .JUMP]

def frame (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : List UInt256 :=
  [accumulator, UInt256.ofNat count] ++ rest

def afterClearDouble (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  BigHelpers.clearReturned (BigModulus.scanNonzero s count rest) 3072 count
    1518 (frame accumulator count rest)

def legacyBaseLoopStart (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  { afterClearDouble s accumulator count rest with pc := UInt256.ofNat 823 }

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

def baseBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) 1

def loadedBaseByte (s : State) (baseOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (baseOff + i))

/-- The two possible outcomes of the conditional masked add of one base bit,
as a memory/active-words pair.  Keeping it a single application (instead of
inlining an `if` into two `State` fields) keeps `bitProgress`'s term the same
size as before the rewrite. -/
def bitChoice (count : Nat) (byte : UInt256) (j : Nat)
    (doubled : State) : BigHelpers.SelectProgress :=
  if (baseBit byte j).toNat = 0 then ⟨doubled.memory, doubled.activeWords⟩
  else
    let added := BigHelpers.addReturned doubled 1024 3072 (baseBit byte j) 0
      count 900 []
    ⟨added.memory, added.activeWords⟩

/-- Effect of the conditional masked add of one base bit.  Both `T2` branches
agree on pc, stack, environment and halt flag, so the conditional is pushed
down to the only two fields that differ. -/
def bitAfterAdd (count : Nat) (byte : UInt256) (j : Nat)
    (doubled : State) : State :=
  { doubled with
      memory := (bitChoice count byte j doubled).memory
      activeWords := (bitChoice count byte j doubled).activeWords }

def bitProgress (count : Nat) (byte : UInt256) : Nat → State → State
  | 0, s => s
  | j + 1, s =>
      let before := bitProgress count byte j s
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 875 []
      { bitAfterAdd count byte j doubled with
          pc := UInt256.ofNat 900
          stack := [] }

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
      simp [bitProgress, bitAfterAdd, bitChoice, BigHelpers.addReturned, ih]

@[simp] theorem bitProgress_executionEnv (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (bitProgress count byte j s).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [bitProgress, bitAfterAdd, bitChoice, BigHelpers.addReturned, ih]

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
  { s with pc := UInt256.ofNat 831
           stack := [UInt256.ofNat i, accumulator, UInt256.ofNat count,
             UInt256.ofNat baseSize] ++ rest }

def outerBody (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulator count baseSize rest i with
      pc := UInt256.ofNat 840 }

def innerLoop (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  let progress := bitProgress count byte j s
  { progress with
    pc := UInt256.ofNat 848
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
      UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest }

def innerBody (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest j with
      pc := UInt256.ofNat 858 }

def innerExit (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest 8 with
      pc := UInt256.ofNat 911 }

def outerExit (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) : State :=
  { outerLoop s accumulator count baseSize rest baseSize with
      pc := UInt256.ofNat 925 }

def innerFrame (accumulator : UInt256) (count baseSize i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
    UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest

def doubledReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 875
    (innerFrame accumulator count baseSize i j offset byte rest)

/-- Entry frame of the appended `T2` trampoline for the base-conversion call
site: exactly the `addMaskedMod` frame the inner loop used to jump to, parked
at `JUMPDEST` 1461 instead of at 104. -/
def bitT2Entry (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { BigHelpers.addEntry
      (doubledReturned s accumulator count baseSize i j offset byte rest)
      1024 3072 (baseBit byte j) 0 count 900
      (innerFrame accumulator count baseSize i j offset byte rest) with
    pc := UInt256.ofNat 1461 }

/-- `T2`'s `JUMPI` fell through: the base bit is zero. -/
def bitT2Fallthrough (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { bitT2Entry s accumulator count baseSize i j offset byte rest with
    pc := UInt256.ofNat 1467 }

/-- The zero-bit branch pops the five arguments and returns to 900 without
touching memory. -/
def bitSkipped (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { doubledReturned s accumulator count baseSize i j offset byte rest with
    pc := UInt256.ofNat 900
    stack := innerFrame accumulator count baseSize i j offset byte rest }

def bitReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { bitAfterAdd count byte j
      (doubledReturned s accumulator count baseSize i j offset byte rest) with
    pc := UInt256.ofNat 900
    stack := innerFrame accumulator count baseSize i j offset byte rest }

/-- Zero base bit: the whole masked add was skipped. -/
theorem bitReturned_of_zero (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (h : (baseBit byte j).toNat = 0) :
    bitReturned s accumulator count baseSize i j offset byte rest =
      bitSkipped s accumulator count baseSize i j offset byte rest := by
  simp [bitReturned, bitSkipped, bitAfterAdd, bitChoice, h]

/-- Set base bit: `addMaskedMod` ran exactly as before. -/
theorem bitReturned_of_pos (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (h : ¬ (baseBit byte j).toNat = 0) :
    bitReturned s accumulator count baseSize i j offset byte rest =
      BigHelpers.addReturned
        (doubledReturned s accumulator count baseSize i j offset byte rest)
        1024 3072 (baseBit byte j) 0 count 900
        (innerFrame accumulator count baseSize i j offset byte rest) := by
  have h900 : (UInt256.ofNat 900 : UInt256) = 900 := by decide
  simp [bitReturned, bitAfterAdd, bitChoice, BigHelpers.addReturned, h, h900]

@[simp] private theorem baseSetupPCs (i : Nat) (hi : 632 ≤ i)
    (hii : i ≤ 642) :
    Artifact.submissionArtifact.instructionPC i =
      ([811,812,815,816,819,822,823,824,826,829,830])[i - 632]! := by
  interval_cases i <;> decide

@[simp] private theorem baseLoopPCs (i : Nat) (hi : 643 ≤ i)
    (hii : i ≤ 716) :
    Artifact.submissionArtifact.instructionPC i =
      ([831,832,833,834,835,836,839,840,841,842,843,844,845,846,847,
        848,849,851,852,853,854,857,858,861,862,863,865,868,871,874,
        875,876,879,880,881,883,884,885,887,888,889,890,893,896,899,
        900,901,903,904,905,906,907,910,911,912,913,914,915,917,918,
        919,920,921,924,925,926,927,930,931,932,934,937,940,943])[
          i - 643]! := by
  interval_cases i <;> decide

@[simp] private theorem baseT2PCs (i : Nat) (hi : 1075 ≤ i) (hii : i ≤ 1084) :
    Artifact.submissionArtifact.instructionPC i =
      [1461,1462,1463,1466,1467,1468,1469,1470,1471,1472][i - 1075]! := by
  interval_cases i <;> decide

private theorem jump104 :
    Decode.isValidJumpDest submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

private theorem jump1461 :
    Decode.isValidJumpDest submissionBytecode 1461 = true :=
  Artifact.isValidJumpDest_index 1075 (by rfl)

private theorem jump1473 :
    Decode.isValidJumpDest submissionBytecode 1473 = true :=
  Artifact.isValidJumpDest_index 1085 (by rfl)

private theorem jump831 :
    Decode.isValidJumpDest submissionBytecode 831 = true :=
  Artifact.isValidJumpDest_index 643 (by rfl)

private theorem jump848 :
    Decode.isValidJumpDest submissionBytecode 848 = true :=
  Artifact.isValidJumpDest_index 658 (by rfl)

private theorem jump875 :
    Decode.isValidJumpDest submissionBytecode 875 = true :=
  Artifact.isValidJumpDest_index 673 (by rfl)

private theorem jump900 :
    Decode.isValidJumpDest submissionBytecode 900 = true :=
  Artifact.isValidJumpDest_index 688 (by rfl)

private theorem jump911 :
    Decode.isValidJumpDest submissionBytecode 911 = true :=
  Artifact.isValidJumpDest_index 696 (by rfl)

private theorem jump925 :
    Decode.isValidJumpDest submissionBytecode 925 = true :=
  Artifact.isValidJumpDest_index 707 (by rfl)

private theorem jump944 :
    Decode.isValidJumpDest submissionBytecode 944 = true :=
  Artifact.isValidJumpDest_index 717 (by rfl)

private theorem jump19 :
    Decode.isValidJumpDest submissionBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump823 :
    Decode.isValidJumpDest submissionBytecode 823 = true :=
  Artifact.isValidJumpDest_index 638 (by rfl)

private theorem jump1518 :
    Decode.isValidJumpDest submissionBytecode 1518 = true :=
  Artifact.isValidJumpDest_index 1123 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_toClearDouble (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClearDoublePath
      (BigModulus.scanNonzero s count rest) =
      some (BigHelpers.clearEntry (BigModulus.scanNonzero s count rest)
        3072 count 1518
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
      (legacyBaseLoopStart s accumulator count rest) =
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
  simp [startBaseLoopPath, opAt, pushAt, wfOp, legacyBaseLoopStart,
    afterClearDouble,
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
  have hne : UInt256.eq (UInt256.ofNat i) (UInt256.ofNat baseSize) = 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hbase, if_neg (by omega)]
    decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerBody,
    baseLoopPCs, hrun, hne, hzeroNat, hc4, hc5, hc6, UInt256.isTrue,
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
  have hne : UInt256.eq (UInt256.ofNat j) 8 = 0 := by
    have hj256 : j < 2 ^ 256 := by omega
    have h8 : (8 : UInt256).toNat = 8 := by decide
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hj256, h8, if_neg (by omega)]
    decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerBody,
    baseLoopPCs, hrun, hne, hzeroNat, hc7, hc8, hc9, UInt256.isTrue,
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
      some (BigDouble.entry
        (innerBody s accumulator count baseSize i offset byte rest j)
        1024 0 count 875
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have h1473 : (1473 : UInt256).toNat = 1473 := by decide
  have h1473Word : (1473 : UInt256) = UInt256.ofNat 1473 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [innerToDoublePath, opAt, pushAt, wfOp, innerBody, innerLoop,
    BigDouble.entry, innerFrame, baseLoopPCs, hcode, hrun, jump1473,
    h1473, h1473Word, hzero, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
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
      some (bitT2Entry s accumulator count baseSize i j offset byte rest) := by
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
  have h104 : (1461 : UInt256).toNat = 1461 := by decide
  have h104Word : (1461 : UInt256) = UInt256.ofNat 1461 := by decide
  have h875 : (875 : UInt256).toNat = 875 := by decide
  have h875Word : (875 : UInt256) = UInt256.ofNat 875 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  simp [innerToAddBitPath, opAt, pushAt, wfOp, doubledReturned, bitT2Entry,
    innerBody, innerLoop, BigHelpers.addReturned, BigHelpers.addEntry,
    innerFrame, baseBit, baseLoopPCs, hcode, hrun, jump1461, hsub,
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
  have h848 : (848 : UInt256).toNat = 848 := by decide
  have h848Word : (848 : UInt256) = UInt256.ofNat 848 := by decide
  have h900 : (900 : UInt256).toNat = 900 := by decide
  have h900Word : (900 : UInt256) = UInt256.ofNat 900 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [innerAfterBitPath, opAt, pushAt, wfOp, bitReturned, bitAfterAdd,
    bitChoice, doubledReturned, innerBody, innerLoop, innerFrame, bitProgress,
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
  have h911 : (911 : UInt256).toNat = 911 := by decide
  have h911Word : (911 : UInt256) = UInt256.ofNat 911 := by decide
  have h8Nat : (8 : UInt256).toNat = 8 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerExit,
    baseLoopPCs, hcode, hrun, jump911, h911, h911Word,
    h8Nat, hc7, hc8, hc9, UInt256.eq, UInt256.isTrue,
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
  have h831 : (831 : UInt256).toNat = 831 := by decide
  have h831Word : (831 : UInt256) = UInt256.ofNat 831 := by decide
  have h911 : (911 : UInt256).toNat = 911 := by decide
  have h911Word : (911 : UInt256) = UInt256.ofNat 911 := by decide
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
  have h925 : (925 : UInt256).toNat = 925 := by decide
  have h925Word : (925 : UInt256) = UInt256.ofNat 925 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerExit,
    baseLoopPCs, hcode, hrun, jump925, h925, h925Word,
    hc4, hc5, hc6, UInt256.eq, UInt256.isTrue,
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
        2048 3072 1 0 count 1335
        ([accumulator, UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h925 : (925 : UInt256).toNat = 925 := by decide
  have h925Word : (925 : UInt256) = UInt256.ofNat 925 := by decide
  have h1335Word : (1335 : UInt256) = UInt256.ofNat 1335 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [outerFinishToAccumulatorPath, opAt, pushAt, wfOp, outerExit,
    outerLoop, BigHelpers.addEntry, baseLoopPCs, hcode, hrun, jump104,
    h104, h104Word, h925, h925Word, h1335Word, hzero,
    hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
/-- `T2` with the base bit set: `JUMPI` lands on `addMaskedMod`'s entry with
exactly the frame the old direct jump produced. -/
theorem run_baseT2Branch (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (hbit : ¬ (baseBit byte j).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseT2Path
      (bitT2Entry s accumulator count baseSize i j offset byte rest) =
      some (BigHelpers.addEntry
        (doubledReturned s accumulator count baseSize i j offset byte rest)
        1024 3072 (baseBit byte j) 0 count 900
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have hvalid : Decode.isValidJumpDest submissionBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  have hdr : (doubledReturned s accumulator count baseSize i j offset byte
      rest).halt = .Running := by
    simp [doubledReturned, BigHelpers.addReturned, innerBody, innerLoop, hrun]
  have hdc : (doubledReturned s accumulator count baseSize i j offset byte
      rest).executionEnv.code = submissionBytecode := by
    simp [doubledReturned, BigHelpers.addReturned, innerBody, innerLoop, hcode]
  simp [baseT2Path, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitT2Entry, BigHelpers.addEntry, innerFrame, baseT2PCs, hcode, hrun,
    hdr, hdc, hvalid, jump104, UInt256.isTrue, hbit, h104, hc12, hc13, hc14, hc15,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc]

set_option linter.unusedSimpArgs false in
/-- `T2` with the base bit clear: `JUMPI` falls through to pc 1337. -/
theorem run_baseT2Fall (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (hbit : (baseBit byte j).toNat = 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseT2Path
      (bitT2Entry s accumulator count baseSize i j offset byte rest) =
      some (bitT2Fallthrough s accumulator count baseSize i j offset byte
        rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have hdr : (doubledReturned s accumulator count baseSize i j offset byte
      rest).halt = .Running := by
    simp [doubledReturned, BigHelpers.addReturned, innerBody, innerLoop, hrun]
  simp [baseT2Path, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitT2Entry, bitT2Fallthrough, BigHelpers.addEntry, innerFrame, baseT2PCs,
    hrun, hdr, UInt256.isTrue, hbit, h104, hc12, hc13, hc14, hc15,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc]

set_option linter.unusedSimpArgs false in
/-- `T2`'s zero-bit tail: five `POP`s and a `JUMP` back to 900, memory
untouched. -/
theorem run_baseT2Skip (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseT2SkipPath
      (bitT2Fallthrough s accumulator count baseSize i j offset byte rest) =
      some (bitSkipped s accumulator count baseSize i j offset byte rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have h900 : (900 : UInt256) = UInt256.ofNat 900 := by decide
  have hvalid : Decode.isValidJumpDest submissionBytecode
      (900 : UInt256).toNat = true := by
    rw [show (900 : UInt256).toNat = 900 by decide]
    exact jump900
  have hdr : (doubledReturned s accumulator count baseSize i j offset byte
      rest).halt = .Running := by
    simp [doubledReturned, BigHelpers.addReturned, innerBody, innerLoop, hrun]
  have hdc : (doubledReturned s accumulator count baseSize i j offset byte
      rest).executionEnv.code = submissionBytecode := by
    simp [doubledReturned, BigHelpers.addReturned, innerBody, innerLoop, hcode]
  simp [baseT2SkipPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitT2Fallthrough, bitT2Entry, bitSkipped, BigHelpers.addEntry, innerFrame,
    baseT2PCs, hcode, hrun, hdr, hdc, hvalid, jump900, h900,
    hc7, hc8, hc9, hc10, hc11, hc12, hc13,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc]

/-- The `T2` trampoline at the base-conversion call site as a single
certificate: either it forwards into `addMaskedMod` (base bit set) or it pops
the frame and returns (base bit clear).  Both ends are `bitReturned`, so the
surrounding bit iteration stays a flat chain. -/
def gasSteps_bitT2Segment (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitT2Entry s accumulator count baseSize i j offset byte rest)
      (bitReturned s accumulator count baseSize i j offset byte rest) := by
  have hframe : (innerFrame accumulator count baseSize i j offset byte rest).length <
      1000 := by
    simp [innerFrame]
    omega
  by_cases hbit : (baseBit byte j).toNat = 0
  · have hfall := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseT2Path
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop, State.fork] using hfork)
        (run_baseT2Fall s accumulator count baseSize i j offset byte rest
          (by omega) hbit
          (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
            innerLoop] using hrun))
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop] using hrun)
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop, State.fork] using hnp)
    have hskip := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseT2SkipPath
        (by simpa [bitT2Fallthrough, bitT2Entry, BigHelpers.addEntry,
          doubledReturned, BigHelpers.addReturned, innerBody, innerLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [bitT2Fallthrough, bitT2Entry, BigHelpers.addEntry,
          doubledReturned, BigHelpers.addReturned, innerBody, innerLoop,
          State.fork] using hfork)
        (run_baseT2Skip s accumulator count baseSize i j offset byte rest
          (by omega)
          (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
            innerLoop] using hcode)
          (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
            innerLoop] using hrun))
        (by simpa [bitT2Fallthrough, bitT2Entry, BigHelpers.addEntry,
          doubledReturned, BigHelpers.addReturned, innerBody,
          innerLoop] using hrun)
        (by simpa [bitT2Fallthrough, bitT2Entry, BigHelpers.addEntry,
          doubledReturned, BigHelpers.addReturned, innerBody, innerLoop,
          State.fork] using hnp)
    exact Challenge.EvmProof.GasSteps.cast (hfall.trans hskip) rfl
      (bitReturned_of_zero s accumulator count baseSize i j offset byte rest
        hbit).symm
  · have hbranch := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseT2Path
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop, State.fork] using hfork)
        (run_baseT2Branch s accumulator count baseSize i j offset byte rest
          (by omega) hbit
          (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
            innerLoop] using hcode)
          (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
            innerLoop] using hrun))
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop] using hrun)
        (by simpa [bitT2Entry, BigHelpers.addEntry, doubledReturned,
          BigHelpers.addReturned, innerBody, innerLoop, State.fork] using hnp)
    have hadd := BigHelpers.gasSteps_addMaskedMod
      (doubledReturned s accumulator count baseSize i j offset byte rest)
      1024 3072 (baseBit byte j) 0 count 900
      (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop] using hcode)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hfork)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop] using hrun)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hnp) jump900
    exact Challenge.EvmProof.GasSteps.cast (hbranch.trans hadd) rfl
      (bitReturned_of_pos s accumulator count baseSize i j offset byte rest
        hbit).symm

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
  have hdouble := BigDouble.gasSteps_doubleMod
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 0 count 875
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
  have hbit := gasSteps_bitT2Segment s accumulator count baseSize i j offset
    byte rest hcap hcount hcode hfork hrun hnp
  have hafter := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerAfterBitPath
      (by simpa [bitReturned, bitAfterAdd, bitChoice, doubledReturned,
        BigHelpers.addReturned, innerBody, innerLoop,
        Artifact.submissionArtifact] using hcode)
      (by simpa [bitReturned, bitAfterAdd, bitChoice, doubledReturned,
        BigHelpers.addReturned, innerBody, innerLoop, State.fork] using hfork)
      (run_innerAfterBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [bitReturned, bitAfterAdd, bitChoice, doubledReturned,
        BigHelpers.addReturned, innerBody, innerLoop] using hrun)
      (by simpa [bitReturned, bitAfterAdd, bitChoice, doubledReturned,
        BigHelpers.addReturned, innerBody, innerLoop, State.fork] using hnp)
  exact hguard.trans <| htoDouble.trans <| hdouble.trans <|
    htoBit.trans <| hbit.trans hafter

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

def gasSteps_baseSetup (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 998)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (BigModulus.scanNonzero s count rest)
      (afterClearDouble s accumulator count rest) := by
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
    BigHelpers.gasSteps_clear (BigModulus.scanNonzero s count rest) 3072
      count 1518 (frame accumulator count rest) hframe hcount hcodeScan
      hforkScan hrunScan hnpScan jump1518
end Challenge.Modexp.Submission.Proofs.Bytecode.BigBase
