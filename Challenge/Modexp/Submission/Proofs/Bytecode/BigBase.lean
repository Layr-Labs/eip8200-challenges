import Challenge.Modexp.Submission.Proofs.Bytecode.BigModulus
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
  [opAt 629 .JUMPDEST, pushAt 630 2 819,
   opAt 631 (.Dup ⟨2, by decide⟩), pushAt 632 2 3072,
   pushAt 633 2 19, opAt 634 .JUMP]

def startBaseLoopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 635 .JUMPDEST, pushAt 636 1 1, pushAt 637 2 3072,
   opAt 638 .MSTORE, pushAt 639 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 640 .JUMPDEST, opAt 641 (.Dup ⟨3, by decide⟩),
   opAt 642 (.Dup ⟨1, by decide⟩), opAt 643 .LT, opAt 644 .ISZERO,
   pushAt 645 2 921, opAt 646 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 647 (.Dup ⟨0, by decide⟩), opAt 648 (.Dup ⟨7, by decide⟩),
   opAt 649 .ADD, opAt 650 (.Dup ⟨0, by decide⟩),
   opAt 651 .CALLDATALOAD, pushAt 652 0 0, opAt 653 .BYTE,
   pushAt 654 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 655 .JUMPDEST, pushAt 656 1 8, opAt 657 (.Dup ⟨1, by decide⟩),
   opAt 658 .LT, opAt 659 .ISZERO, pushAt 660 2 907,
   opAt 661 .JUMPI]

def innerToDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 662 2 871, opAt 663 (.Dup ⟨6, by decide⟩),
   pushAt 664 0 0, pushAt 665 1 1, pushAt 666 2 1024,
   pushAt 667 2 1024, pushAt 668 2 104, opAt 669 .JUMP]

def innerToAddBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 670 .JUMPDEST, pushAt 671 2 896,
   opAt 672 (.Dup ⟨6, by decide⟩), pushAt 673 0 0,
   pushAt 674 1 1, opAt 675 (.Dup ⟨5, by decide⟩),
   opAt 676 (.Dup ⟨5, by decide⟩), pushAt 677 1 7,
   opAt 678 .SUB, opAt 679 .SHR, opAt 680 .AND,
   pushAt 681 2 3072, pushAt 682 2 1024,
   pushAt 683 2 104, opAt 684 .JUMP]

def innerAfterBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 685 .JUMPDEST, pushAt 686 1 1,
   opAt 687 (.Dup ⟨1, by decide⟩), opAt 688 .ADD,
   opAt 689 (.Swap ⟨0, by decide⟩), opAt 690 .POP,
   pushAt 691 2 844, opAt 692 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 693 .JUMPDEST, opAt 694 .POP, opAt 695 .POP, opAt 696 .POP,
   pushAt 697 1 1, opAt 698 (.Dup ⟨1, by decide⟩), opAt 699 .ADD,
   opAt 700 (.Swap ⟨0, by decide⟩), opAt 701 .POP,
   pushAt 702 2 827, opAt 703 .JUMP]

def outerFinishToAccumulatorPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 704 .JUMPDEST, opAt 705 .POP, pushAt 706 2 940,
   opAt 707 (.Dup ⟨2, by decide⟩), pushAt 708 0 0,
   pushAt 709 1 1, pushAt 710 2 3072, pushAt 711 2 2048,
   pushAt 712 2 104, opAt 713 .JUMP]

def frame (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : List UInt256 :=
  [accumulator, UInt256.ofNat count] ++ rest

def afterClearDouble (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  BigHelpers.clearReturned (BigModulus.scanNonzero s count rest) 3072 count
    819 (frame accumulator count rest)

def baseLoopEntry (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  let cleared := afterClearDouble s accumulator count rest
  { cleared with
    pc := UInt256.ofNat 827
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
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 871 []
      BigHelpers.addReturned doubled 1024 3072 (baseBit byte j) 0 count 896 []

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
  { s with pc := UInt256.ofNat 827
           stack := [UInt256.ofNat i, accumulator, UInt256.ofNat count,
             UInt256.ofNat baseSize] ++ rest }

def outerBody (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulator count baseSize rest i with
      pc := UInt256.ofNat 836 }

def innerLoop (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  let progress := bitProgress count byte j s
  { progress with
    pc := UInt256.ofNat 844
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
      UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest }

def innerBody (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest j with
      pc := UInt256.ofNat 854 }

def innerExit (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest 8 with
      pc := UInt256.ofNat 907 }

def outerExit (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) : State :=
  { outerLoop s accumulator count baseSize rest baseSize with
      pc := UInt256.ofNat 921 }

def innerFrame (accumulator : UInt256) (count baseSize i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
    UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest

def doubledReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 871
    (innerFrame accumulator count baseSize i j offset byte rest)

def bitReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (doubledReturned s accumulator count baseSize i j offset byte rest)
    1024 3072 (baseBit byte j) 0 count 896
    (innerFrame accumulator count baseSize i j offset byte rest)

@[simp] private theorem baseSetupPCs (i : Nat)
    (hi : 629 ≤ i) (hii : i ≤ 639) :
    Artifact.submissionArtifact.instructionPC i =
      [807,808,811,812,815,818,819,820,822,825,826][i - 629]! := by
  interval_cases i <;> decide

@[simp] private theorem baseLoopPCs (i : Nat)
    (hi : 640 ≤ i) (hii : i ≤ 713) :
    Artifact.submissionArtifact.instructionPC i =
      [827,828,829,830,831,832,835,836,837,838,839,840,841,842,843,844,845,847,848,849,850,853,854,857,858,859,861,864,867,870,871,872,875,876,877,879,880,881,883,884,885,886,889,892,895,896,897,899,900,901,902,903,906,907,908,909,910,911,913,914,915,916,917,920,921,922,923,926,927,928,930,933,936,939][i - 640]! := by
  interval_cases i <;> decide

private theorem jump104 :
    Decode.isValidJumpDest submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

private theorem jump831 :
    Decode.isValidJumpDest submissionBytecode 827 = true :=
  Artifact.isValidJumpDest_index 640 (by rfl)

private theorem jump848 :
    Decode.isValidJumpDest submissionBytecode 844 = true :=
  Artifact.isValidJumpDest_index 655 (by rfl)

private theorem jump875 :
    Decode.isValidJumpDest submissionBytecode 871 = true :=
  Artifact.isValidJumpDest_index 670 (by rfl)

private theorem jump900 :
    Decode.isValidJumpDest submissionBytecode 896 = true :=
  Artifact.isValidJumpDest_index 685 (by rfl)

private theorem jump911 :
    Decode.isValidJumpDest submissionBytecode 907 = true :=
  Artifact.isValidJumpDest_index 693 (by rfl)

private theorem jump925 :
    Decode.isValidJumpDest submissionBytecode 921 = true :=
  Artifact.isValidJumpDest_index 704 (by rfl)

private theorem jump944 :
    Decode.isValidJumpDest submissionBytecode 940 = true :=
  Artifact.isValidJumpDest_index 714 (by rfl)

private theorem jump19 :
    Decode.isValidJumpDest submissionBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump823 :
    Decode.isValidJumpDest submissionBytecode 819 = true :=
  Artifact.isValidJumpDest_index 635 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_toClearDouble (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClearDoublePath
      (BigModulus.scanNonzero s count rest) =
      some (BigHelpers.clearEntry (BigModulus.scanNonzero s count rest)
        3072 count 819
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
  have h823 : (819 : UInt256).toNat = 819 := by decide
  have h823Word : (819 : UInt256) = UInt256.ofNat 819 := by decide
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
        1024 1024 1 0 count 871
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
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
        1024 3072 (baseBit byte j) 0 count 896
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
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h875 : (871 : UInt256).toNat = 871 := by decide
  have h875Word : (871 : UInt256) = UInt256.ofNat 871 := by decide
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
  have h848 : (844 : UInt256).toNat = 844 := by decide
  have h848Word : (844 : UInt256) = UInt256.ofNat 844 := by decide
  have h900 : (896 : UInt256).toNat = 896 := by decide
  have h900Word : (896 : UInt256) = UInt256.ofNat 896 := by decide
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
  have h911 : (907 : UInt256).toNat = 907 := by decide
  have h911Word : (907 : UInt256) = UInt256.ofNat 907 := by decide
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
  have h831 : (827 : UInt256).toNat = 827 := by decide
  have h831Word : (827 : UInt256) = UInt256.ofNat 827 := by decide
  have h911 : (907 : UInt256).toNat = 907 := by decide
  have h911Word : (907 : UInt256) = UInt256.ofNat 907 := by decide
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
  have h925 : (921 : UInt256).toNat = 921 := by decide
  have h925Word : (921 : UInt256) = UInt256.ofNat 921 := by decide
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
        2048 3072 1 0 count 940
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
  have h925 : (921 : UInt256).toNat = 921 := by decide
  have h925Word : (921 : UInt256) = UInt256.ofNat 921 := by decide
  have h944Word : (940 : UInt256) = UInt256.ofNat 940 := by decide
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
    1024 1024 1 0 count 871
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
    1024 3072 (baseBit byte j) 0 count 896
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
    1024 1024 1 0 count 871
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
    1024 3072 (baseBit byte j) 0 count 896
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
        1024 1024 1 0 count 871
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
        1024 3072 (baseBit byte j) 0 count 896
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
      count 819 (frame accumulator count rest) hframe hcount hcodeScan
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
    (BigModulus.scanNonzero s count rest) 3072 count 819
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
