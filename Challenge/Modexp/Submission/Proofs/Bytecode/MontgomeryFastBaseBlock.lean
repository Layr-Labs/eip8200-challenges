import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryBaseLoadValue
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReadyValue

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryFastBaseBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Montgomery

def frame (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) : List UInt256 :=
  [A, UInt256.ofNat n, UInt256.ofNat b, eWord, mWord,
    UInt256.ofNat baseOff, expWord] ++ rest

def fastAt (s : State) (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256)
    (pc : Nat) : State :=
  {s with pc := UInt256.ofNat pc, stack := frame A n b eWord mWord baseOff expWord rest}

def readyAt (s : State) (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256)
    (pc : Nat) : State :=
  {s with pc := UInt256.ofNat pc, stack := UInt256.ofNat b :: frame A n b eWord mWord baseOff expWord rest}

def fastEntry (s : State) (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) : State :=
  fastAt s A n b eWord mWord baseOff expWord rest 2393

def fastReturned (s : State) (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) : State :=
  if n = 0 then
    fastAt s A n b eWord mWord baseOff expWord rest 811
  else if 32 < n then
    fastAt s A n b eWord mWord baseOff expWord rest 811
  else if 32 * n < b then
    fastAt s A n b eWord mWord baseOff expWord rest 811
  else
    let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
    if (MachineState.readWord s.memory 0).toNat % 2 = 0 then
      fastAt touched A n b eWord mWord baseOff expWord rest 811
    else
      let ready := MontgomeryReadyValue.directReady touched baseOff b n
      readyAt ready A n b eWord mWord baseOff expWord rest 925

def readyEntry (s : State) (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) : State :=
  readyAt s A n b eWord mWord baseOff expWord rest 925

def initialized (s : State) (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) : State :=
  MontgomeryReadyValue.initialize s n 2126
    (frame A n b eWord mWord baseOff expWord rest)

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def fastZeroGuardPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1705 .JUMPDEST, opAt 1706 (.Dup ⟨1, by decide⟩),
   opAt 1707 .ISZERO, pushAt 1708 2 2465, opAt 1709 .JUMPI]

def fastLargeGuardPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1710 1 32, opAt 1711 (.Dup ⟨2, by decide⟩),
   opAt 1712 .GT, pushAt 1713 2 2465, opAt 1714 .JUMPI]

def fastLengthGuardPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1715 (.Dup ⟨1, by decide⟩), pushAt 1716 1 5,
   opAt 1717 .SHL, opAt 1718 (.Dup ⟨3, by decide⟩),
   opAt 1719 .GT, pushAt 1720 2 2465, opAt 1721 .JUMPI]

def fastParityGuardPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1722 0 0, opAt 1723 .MLOAD, pushAt 1724 1 1,
   opAt 1725 .AND, opAt 1726 .ISZERO, pushAt 1727 2 2465,
   opAt 1728 .JUMPI]

def fastClearCallPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1729 (.Dup ⟨1, by decide⟩), pushAt 1730 2 2440,
   opAt 1731 (.Swap ⟨0, by decide⟩), pushAt 1732 2 3072,
   pushAt 1733 2 19, opAt 1734 .JUMP]

def fastClearReturnPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1735 .JUMPDEST, pushAt 1736 1 1, pushAt 1737 2 3072,
   opAt 1738 .MSTORE, pushAt 1739 2 2459, pushAt 1740 2 1024,
   opAt 1741 (.Dup ⟨4, by decide⟩), opAt 1742 (.Dup ⟨8, by decide⟩),
   pushAt 1743 2 439, opAt 1744 .JUMP]

def fastLoadReturnPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1745 .JUMPDEST, opAt 1746 (.Dup ⟨2, by decide⟩),
   pushAt 1747 2 925, opAt 1748 .JUMP]

def fastFallbackPath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1749 .JUMPDEST, pushAt 1750 2 811, opAt 1751 .JUMP]

def initializePath :
    List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 707 .JUMPDEST, opAt 708 .POP, pushAt 709 2 2126,
   opAt 710 (.Dup ⟨2, by decide⟩), pushAt 711 0 0,
   pushAt 712 1 1, pushAt 713 2 3072, pushAt 714 2 2048,
   pushAt 715 2 104, opAt 716 .JUMP]

@[simp] private theorem localPCs (i : Nat) (hi : 707 ≤ i) (hii : i ≤ 716) :
    Artifact.submissionArtifact.instructionPC i =
      [925,926,927,930,931,932,934,937,940,943][i - 707]! := by
  interval_cases i <;> decide

@[simp] private theorem fastPCs (i : Nat) (hi : 1705 ≤ i) (hii : i ≤ 1751) :
    Artifact.submissionArtifact.instructionPC i =
      [2393,2394,2395,2396,2399,2400,2402,2403,2404,2407,
       2408,2409,2411,2412,2413,2414,2417,2418,2419,2420,
       2422,2423,2424,2427,2428,2429,2432,2433,2436,2439,
       2440,2441,2443,2446,2447,2450,2453,2454,2455,2458,
       2459,2460,2461,2464,2465,2466,2469][i - 1705]! := by
  interval_cases i <;> decide

private theorem jump811 :
    Decode.isValidJumpDest submissionBytecode 811 = true :=
  Artifact.isValidJumpDest_index 632 (by rfl)

private theorem jump925 :
    Decode.isValidJumpDest submissionBytecode 925 = true :=
  Artifact.isValidJumpDest_index 707 (by rfl)

private theorem jump2126 :
    Decode.isValidJumpDest submissionBytecode 2126 = true :=
  Artifact.isValidJumpDest_index 1545 (by rfl)

private theorem jump19 :
    Decode.isValidJumpDest submissionBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump439 :
    Decode.isValidJumpDest submissionBytecode 439 = true :=
  Artifact.isValidJumpDest_index 353 (by rfl)

private theorem jump2440 :
    Decode.isValidJumpDest submissionBytecode 2440 = true :=
  Artifact.isValidJumpDest_index 1735 (by rfl)

private theorem jump2459 :
    Decode.isValidJumpDest submissionBytecode 2459 = true :=
  Artifact.isValidJumpDest_index 1745 (by rfl)

private theorem jump2440Word :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 2440).toNat = true := by
  rw [show (UInt256.ofNat 2440).toNat = 2440 by decide]
  exact jump2440

private theorem jump2459Word :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 2459).toNat = true := by
  rw [show (UInt256.ofNat 2459).toNat = 2459 by decide]
  exact jump2459

private theorem jump2465 :
    Decode.isValidJumpDest submissionBytecode 2465 = true :=
  Artifact.isValidJumpDest_index 1749 (by rfl)

private theorem lowBit (w : UInt256) :
    (UInt256.land (UInt256.ofNat 1) w).toNat = w.toNat % 2 := by
  rw [Word.word_toNat_land, Word.word_toNat_ofNat]
  change 1 &&& w.toNat = w.toNat % 2
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem run_zeroPass (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hn : 1 ≤ n) (hcount : n < 2 ^ 256) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastZeroGuardPath
      (fastEntry s A n b eWord mWord baseOff expWord rest) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 2400) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero (UInt256.ofNat n)) := by
    simp only [UInt256.isZero, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hcount,
      if_neg (show n ≠ 0 by omega)]
    decide
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastZeroGuardPath, opAt, pushAt, wfOp, fastEntry, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hc]

theorem run_zeroFallback (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hn : n = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastZeroGuardPath
      (fastEntry s A n b eWord mWord baseOff expWord rest) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 2465) := by
  have hc : UInt256.isTrue (UInt256.isZero (UInt256.ofNat 0)) := by decide
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastZeroGuardPath, opAt, pushAt, wfOp, fastEntry, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hc, hcode, hn, jump2465]

theorem run_largePass (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hN : n ≤ 32) (hcount : n < 2 ^ 256) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastLargeGuardPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2400) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 2408) := by
  have hc : ¬ UInt256.isTrue (UInt256.gt (UInt256.ofNat n)
      (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hcount,
      Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide),
      if_neg (show ¬n > 32 by omega)]
    decide
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastLargeGuardPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hc]

theorem run_largeFallback (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hlarge : 32 < n) (hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastLargeGuardPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2400) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 2465) := by
  have hc : UInt256.isTrue (UInt256.gt (UInt256.ofNat n)
      (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hcount,
      Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide), if_pos hlarge]
    decide
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastLargeGuardPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hc, hcode, jump2465]

theorem run_lengthPass (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hN : n ≤ 32) (hcount : n < 2 ^ 256) (hfit : b ≤ 32 * n)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastLengthGuardPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2408) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 2418) := by
  have hshift : 32 * n < 2 ^ 256 := by omega
  have hshiftWord : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := by
    calc
      UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
          UInt256.ofNat (n * 2 ^ 5) := by
            apply Word.shiftLeft_ofNat (by omega) (by norm_num)
            omega
      _ = UInt256.ofNat (32 * n) := by
        congr 1
        omega
  have hb : b < 2 ^ 256 := by omega
  have hc : ¬ UInt256.isTrue (UInt256.gt
      (UInt256.ofNat b) (UInt256.ofNat (32 * n))) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      hshiftWord, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hb,
      if_neg (show ¬b > 32 * n by omega)]
    decide
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastLengthGuardPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hshiftWord,
    Nat.add_assoc, cap, hrun, hc, hshift]

theorem run_lengthFallback (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hN : n ≤ 32) (hcount : n < 2 ^ 256) (hb : b < 2 ^ 256)
    (hwide : 32 * n < b)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastLengthGuardPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2408) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 2465) := by
  have hshift : 32 * n < 2 ^ 256 := by omega
  have hshiftWord : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := by
    calc
      UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
          UInt256.ofNat (n * 2 ^ 5) := by
            apply Word.shiftLeft_ofNat (by omega) (by norm_num)
            omega
      _ = UInt256.ofNat (32 * n) := by
        congr 1
        omega
  have hc : UInt256.isTrue (UInt256.gt
      (UInt256.ofNat b) (UInt256.ofNat (32 * n))) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      hshiftWord, Nat.mod_eq_of_lt hshift,
      Nat.mod_eq_of_lt hb,
      if_pos (show 32 * n < b by omega)]
    decide
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastLengthGuardPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hshiftWord,
    Nat.add_assoc, cap, hrun, hc, hshift, hcode, jump2465]

theorem run_parityOdd (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastParityGuardPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2418) =
        some (fastAt (MontgomeryWrapperBlock.loadLowLeaf s 0) A n b
          eWord mWord baseOff expWord rest 2428) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, hodd]
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  have hzeroStruct : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [fastParityGuardPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hc, hzeroStruct, MontgomeryWrapperBlock.loadLowLeaf,
    State.activeWordsAfterUInt256]

theorem run_parityEven (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (heven : (MachineState.readWord s.memory 0).toNat % 2 = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastParityGuardPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2418) =
        some (fastAt (MontgomeryWrapperBlock.loadLowLeaf s 0) A n b
          eWord mWord baseOff expWord rest 2465) := by
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, heven]
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  have hzeroStruct : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [fastParityGuardPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hc, hcode, hzeroStruct, jump2465,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_clearCall (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastClearCallPath
      (fastAt (MontgomeryWrapperBlock.loadLowLeaf s 0) A n b
        eWord mWord baseOff expWord rest 2428) =
    some (BigHelpers.clearEntry (MontgomeryWrapperBlock.loadLowLeaf s 0)
          3072 n 2440 (frame A n b eWord mWord baseOff expWord rest)) := by
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  have hexchange :
      List.exchange
          ([UInt256.ofNat 2440, UInt256.ofNat n] ++
            frame A n b eWord mWord baseOff expWord rest) 0 1 =
        some ([UInt256.ofNat n, UInt256.ofNat 2440] ++
          frame A n b eWord mWord baseOff expWord rest) := by
    simp [List.exchange, frame]
  have hexchange' :
      List.exchange
          (UInt256.ofNat 2440 :: UInt256.ofNat n ::
            (A :: UInt256.ofNat n :: UInt256.ofNat b :: eWord :: mWord ::
              UInt256.ofNat baseOff :: expWord :: rest)) 0 1 =
        some (UInt256.ofNat n :: UInt256.ofNat 2440 ::
          (A :: UInt256.ofNat n :: UInt256.ofNat b :: eWord :: mWord ::
            UInt256.ofNat baseOff :: expWord :: rest)) := by
    simp [List.exchange, frame]
  simp [fastClearCallPath, opAt, pushAt, wfOp, fastAt, frame,
    BigHelpers.clearEntry, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hcode, hexchange, hexchange',
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256,
    jump2440, jump19]

theorem run_clearReturn (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastClearReturnPath
      (BigHelpers.clearReturned s 3072 n 2440
        (frame A n b eWord mWord baseOff expWord rest)) =
      let cleared := OneMemory.clearLeaf s 3072 n 0 []
      let seeded := OneMemory.storeOneLeaf cleared 3072
      some (BigLoad.loadEntry seeded (UInt256.ofNat baseOff)
        (UInt256.ofNat b) 1024 2459
        (frame A n b eWord mWord baseOff expWord rest)) := by
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastClearReturnPath, opAt, pushAt, wfOp,
    BigHelpers.clearReturned, OneMemory.clearLeaf, OneMemory.flatLeaf,
    OneMemory.storeOneLeaf, OneMemory.storeOneMemory,
    OneMemory.storeOneActiveWords, BigLoad.loadEntry, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hcode,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256,
    List.exchange, jump439]

theorem run_loadReturn_generic (t : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hpc : t.pc = UInt256.ofNat 2459)
    (hstack : t.stack = frame A n b eWord mWord baseOff expWord rest)
    (hcode : t.executionEnv.code = submissionBytecode)
    (hrun : t.halt = .Running) :
    Stepper.runLocatedBlock fastLoadReturnPath t =
      some { t with
        pc := UInt256.ofNat 925
        stack := UInt256.ofNat b :: frame A n b eWord mWord baseOff expWord rest} := by
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastLoadReturnPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hpc, hstack, hrun, hcode, jump925]

theorem run_loadReturn (_s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (seeded : State)
    (hcap : rest.length < 973)
    (hcode : seeded.executionEnv.code = submissionBytecode)
    (hrun : seeded.halt = .Running) :
    Stepper.runLocatedBlock fastLoadReturnPath
      (BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
        (UInt256.ofNat b) 1024 2459
        (frame A n b eWord mWord baseOff expWord rest)) =
      some { BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
        (UInt256.ofNat b) 1024 2459
        (frame A n b eWord mWord baseOff expWord rest) with
          pc := UInt256.ofNat 925
          stack := UInt256.ofNat b ::
            frame A n b eWord mWord baseOff expWord rest } := by
  have hpc : (BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
      (UInt256.ofNat b) 1024 2459
      (frame A n b eWord mWord baseOff expWord rest)).pc =
        UInt256.ofNat 2459 := by
    rfl
  have hstack : (BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
      (UInt256.ofNat b) 1024 2459
      (frame A n b eWord mWord baseOff expWord rest)).stack =
        frame A n b eWord mWord baseOff expWord rest := by
    rfl
  have hcode' : (BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
      (UInt256.ofNat b) 1024 2459
      (frame A n b eWord mWord baseOff expWord rest)).executionEnv.code =
        submissionBytecode := by
    change seeded.executionEnv.code = submissionBytecode
    exact hcode
  have hrun' : (BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
      (UInt256.ofNat b) 1024 2459
      (frame A n b eWord mWord baseOff expWord rest)).halt = .Running := by
    change seeded.halt = .Running
    exact hrun
  simpa [hstack] using run_loadReturn_generic
    (t := BigLoad.loadReturned seeded (UInt256.ofNat baseOff)
      (UInt256.ofNat b) 1024 2459
      (frame A n b eWord mWord baseOff expWord rest))
    A n b eWord mWord baseOff expWord rest hcap hpc hstack hcode' hrun'

theorem run_fallback (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastFallbackPath
      (fastAt s A n b eWord mWord baseOff expWord rest 2465) =
        some (fastAt s A n b eWord mWord baseOff expWord rest 811) := by
  have cap : ∀ k, k ≤ 30 → rest.length + k < 1024 := by omega
  simp [fastFallbackPath, opAt, pushAt, wfOp, fastAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fastPCs, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hcode, jump811]

theorem run_initializePath (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : rest.length < 973)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock initializePath
      (readyEntry s A n b eWord mWord baseOff expWord rest) =
        some (BigHelpers.addEntry s 2048 3072 1 0 n 2126
          (frame A n b eWord mWord baseOff expWord rest)) := by
  have cap : ∀ k, k ≤ 40 → rest.length + k < 1024 := by omega
  have hzeroStruct : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [initializePath, opAt, pushAt, wfOp, readyEntry, readyAt, frame,
    BigHelpers.addEntry, localPCs, Stepper.runLocatedBlock,
    Stepper.runLocated, Stepper.runInstr, Word.succ_ofNat_mod,
    Word.ofNat_add_mod, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, Nat.add_assoc, cap, hrun, hcode,
    hzeroStruct, jump2126]

def gasSteps_initialize (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : (frame A n b eWord mWord baseOff expWord rest).length < 980)
    (hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (readyEntry s A n b eWord mWord baseOff expWord rest)
      (initialized s A n b eWord mWord baseOff expWord rest) := by
  have hrest : rest.length < 973 := by
    simp [frame] at hcap
    omega
  have hframe : (frame A n b eWord mWord baseOff expWord rest).length < 1000 := by
    omega
  have h2126 : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 2126).toNat = true := by
    simp only [Word.word_toNat_ofNat]
    exact jump2126
  have hp := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    initializePath
    (by simpa [readyEntry, readyAt, Artifact.submissionArtifact] using hcode)
    (by simpa [readyEntry, readyAt, State.fork] using hfork)
    (run_initializePath s A n b eWord mWord baseOff expWord rest hrest hcount
      hcode hrun)
    (by simpa [readyEntry, readyAt] using hrun)
    (by simpa [readyEntry, readyAt, State.fork] using hnp)
  have ha := BigHelpers.gasSteps_addMaskedMod s 2048 3072 1 0 n 2126
    (frame A n b eWord mWord baseOff expWord rest) hframe hcount hcode
    hfork hrun hnp h2126
  exact GasSteps.cast (hp.trans ha)
    (by simp [readyEntry, readyAt, frame, BigHelpers.addEntry])
    (by simp [initialized, frame, MontgomeryReadyValue.initialize])

def gasSteps_fastBase (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (hcap : (frame A n b eWord mWord baseOff expWord rest).length < 980)
    (hcount : n < 2 ^ 256) (hb : b < 2 ^ 256)
    (hoff : baseOff + b < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (fastEntry s A n b eWord mWord baseOff expWord rest)
      (fastReturned s A n b eWord mWord baseOff expWord rest) := by
  have hrest : rest.length < 973 := by
    simp [frame] at hcap
    omega
  have hframeClear :
      (frame A n b eWord mWord baseOff expWord rest).length < 1017 := by
    omega
  have hframeLoad :
      (frame A n b eWord mWord baseOff expWord rest).length < 1000 := by
    omega
  have hoffWord : baseOff < 2 ^ 256 := by omega
  have hloadOffset : baseOff + b ≤ 2 ^ 256 := by omega
  have hzero : n = 0 ∨ n ≠ 0 := by omega
  by_cases hzero' : n = 0
  · have hp := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      fastZeroGuardPath
      (by simpa [fastEntry, fastAt, frame, Artifact.submissionArtifact] using hcode)
      (by simpa [fastEntry, fastAt, frame, State.fork] using hfork)
      (run_zeroFallback s A n b eWord mWord baseOff expWord rest hrest hzero' hcode hrun)
      (by simpa [fastEntry, fastAt, frame] using hrun) hnp
    have hf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      fastFallbackPath
      (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
      (by simpa [fastAt, frame, State.fork] using hfork)
      (run_fallback s A n b eWord mWord baseOff expWord rest hrest hcode hrun)
      (by simpa [fastAt, frame] using hrun)
      (by simpa [fastAt, frame, State.fork] using hnp)
    simpa [fastReturned, fastEntry, fastAt, frame, hzero'] using hp.trans hf
  · have hn : 1 ≤ n := by omega
    have hp := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      fastZeroGuardPath
      (by simpa [fastEntry, fastAt, frame, Artifact.submissionArtifact] using hcode)
      (by simpa [fastEntry, fastAt, frame, State.fork] using hfork)
      (run_zeroPass s A n b eWord mWord baseOff expWord rest hrest hn hcount hrun)
      (by simpa [fastEntry, fastAt, frame] using hrun) hnp
    by_cases hlarge : 32 < n
    · have hl := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        fastLargeGuardPath
        (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
        (by simpa [fastAt, frame, State.fork] using hfork)
        (run_largeFallback s A n b eWord mWord baseOff expWord rest hrest
          hlarge hcount hcode hrun)
        (by simpa [fastAt, frame] using hrun) hnp
      have hf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        fastFallbackPath
        (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
        (by simpa [fastAt, frame, State.fork] using hfork)
        (run_fallback s A n b eWord mWord baseOff expWord rest hrest hcode hrun)
        (by simpa [fastAt, frame] using hrun)
        (by simpa [fastAt, frame, State.fork] using hnp)
      simpa [fastReturned, fastEntry, fastAt, frame, hzero', hlarge] using
        hp.trans (hl.trans hf)
    · have hN : n ≤ 32 := by omega
      have hl := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        fastLargeGuardPath
        (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
        (by simpa [fastAt, frame, State.fork] using hfork)
        (run_largePass s A n b eWord mWord baseOff expWord rest hrest hN hcount hrun)
        (by simpa [fastAt, frame] using hrun) hnp
      by_cases hwide : 32 * n < b
      · have hw := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          fastLengthGuardPath
          (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
          (by simpa [fastAt, frame, State.fork] using hfork)
          (run_lengthFallback s A n b eWord mWord baseOff expWord rest hrest
            hN hcount hb hwide hcode hrun)
          (by simpa [fastAt, frame] using hrun) hnp
        have hf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          fastFallbackPath
          (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
          (by simpa [fastAt, frame, State.fork] using hfork)
          (run_fallback s A n b eWord mWord baseOff expWord rest hrest hcode hrun)
          (by simpa [fastAt, frame] using hrun)
          (by simpa [fastAt, frame, State.fork] using hnp)
        simpa [fastReturned, fastEntry, fastAt, frame, hzero', hlarge, hwide] using
          hp.trans (hl.trans (hw.trans hf))
      · have hfit : b ≤ 32 * n := by omega
        have hw := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          fastLengthGuardPath
          (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
          (by simpa [fastAt, frame, State.fork] using hfork)
          (run_lengthPass s A n b eWord mWord baseOff expWord rest hrest
            hN hcount hfit hrun)
          (by simpa [fastAt, frame] using hrun) hnp
        by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
        · have hpar := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
            fastParityGuardPath
            (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
            (by simpa [fastAt, frame, State.fork] using hfork)
            (run_parityEven s A n b eWord mWord baseOff expWord rest hrest
              heven hcode hrun)
            (by simpa [fastAt, frame] using hrun) hnp
          let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
          have touchedCode : touched.executionEnv.code = submissionBytecode := by
            simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hcode
          have touchedHalt : touched.halt = .Running := by
            simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hrun
          have touchedFork : touched.fork = .Osaka := by
            simpa only [touched, MontgomeryWrapperBlock.loadLowLeaf, State.fork] using hfork
          have touchedNp : Precompile.isPrecompileWithConfig touched.executionEnv.precompileConfig
              touched.executionEnv.fork touched.executionEnv.codeAddr = false := by
            simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hnp
          have hf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
            fastFallbackPath
            (by simpa [fastAt, frame,
              Artifact.submissionArtifact] using touchedCode)
            (by simpa [fastAt, frame,
              State.fork] using touchedFork)
            (run_fallback touched A n b eWord mWord baseOff expWord rest hrest
              touchedCode touchedHalt)
            (by simpa [fastAt, frame] using touchedHalt)
            (by simpa [fastAt, frame, State.fork] using touchedNp)
          simpa [fastReturned, fastEntry, fastAt, frame, hzero', hlarge,
            hwide, heven, touched, MontgomeryWrapperBlock.loadLowLeaf] using
            hp.trans (hl.trans (hw.trans (hpar.trans hf)))
        · have hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1 := by
            omega
          let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
          let cleared := OneMemory.clearLeaf touched 3072 n 0 []
          let seeded := OneMemory.storeOneLeaf cleared 3072
          have touchedCode : touched.executionEnv.code = submissionBytecode := by
            simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hcode
          have touchedHalt : touched.halt = .Running := by
            simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hrun
          have touchedFork : touched.fork = .Osaka := by
            simpa only [touched, MontgomeryWrapperBlock.loadLowLeaf, State.fork] using hfork
          have touchedNp : Precompile.isPrecompileWithConfig touched.executionEnv.precompileConfig
              touched.executionEnv.fork touched.executionEnv.codeAddr = false := by
            simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hnp
          have clearedCode : cleared.executionEnv.code = submissionBytecode := by
            change touched.executionEnv.code = submissionBytecode
            exact touchedCode
          have clearedHalt : cleared.halt = .Running := by
            change touched.halt = .Running
            exact touchedHalt
          have clearedFork : cleared.fork = .Osaka := by
            change touched.fork = .Osaka
            exact touchedFork
          have clearedNp : Precompile.isPrecompileWithConfig cleared.executionEnv.precompileConfig
              cleared.executionEnv.fork cleared.executionEnv.codeAddr = false := by
            change Precompile.isPrecompileWithConfig touched.executionEnv.precompileConfig
              touched.executionEnv.fork touched.executionEnv.codeAddr = false
            exact touchedNp
          have seededCode : seeded.executionEnv.code = submissionBytecode := by
            change cleared.executionEnv.code = submissionBytecode
            exact clearedCode
          have seededHalt : seeded.halt = .Running := by
            change cleared.halt = .Running
            exact clearedHalt
          have seededFork : seeded.fork = .Osaka := by
            change cleared.fork = .Osaka
            exact clearedFork
          have seededNp : Precompile.isPrecompileWithConfig seeded.executionEnv.precompileConfig
              seeded.executionEnv.fork seeded.executionEnv.codeAddr = false := by
            change Precompile.isPrecompileWithConfig cleared.executionEnv.precompileConfig
              cleared.executionEnv.fork cleared.executionEnv.codeAddr = false
            exact clearedNp
          have hpar := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
            fastParityGuardPath
            (by simpa [fastAt, frame, Artifact.submissionArtifact] using hcode)
            (by simpa [fastAt, frame, State.fork] using hfork)
            (run_parityOdd s A n b eWord mWord baseOff expWord rest hrest
              hodd hrun)
            (by simpa [fastAt, frame] using hrun) hnp
          have hcall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
            fastClearCallPath
            (by simpa [fastAt, frame, Artifact.submissionArtifact] using touchedCode)
            (by simpa [fastAt, frame, State.fork] using touchedFork)
            (run_clearCall s A n b eWord mWord baseOff expWord rest hrest
              hcount hcode hrun)
            (by simpa [fastAt, frame] using touchedHalt)
            (by simpa [fastAt, frame, State.fork] using touchedNp)
          have hclear := BigHelpers.gasSteps_clear touched 3072 n 2440
            (frame A n b eWord mWord baseOff expWord rest) hframeClear hcount
            touchedCode touchedFork touchedHalt touchedNp
            jump2440Word
          have hreturn := Stepper.runLocatedBlock_sound
            Artifact.submissionArtifact .Osaka fastClearReturnPath
            (by simpa [touched, BigHelpers.clearReturned,
              Artifact.submissionArtifact] using touchedCode)
            (by simpa [touched, BigHelpers.clearReturned, State.fork] using touchedFork)
            (run_clearReturn touched A n b eWord mWord baseOff expWord rest
              hrest hcount touchedCode touchedHalt)
            (by simpa [touched, BigHelpers.clearReturned] using touchedHalt)
            (by simpa [touched, BigHelpers.clearReturned, State.fork] using touchedNp)
          have hload := BigLoad.gasSteps_loadBigEndian seeded baseOff b 1024
            2459 (frame A n b eWord mWord baseOff expWord rest) hframeLoad hoffWord
            hloadOffset hb
            seededCode seededFork seededHalt seededNp
            jump2459Word
          have hloadReturn := Stepper.runLocatedBlock_sound
            Artifact.submissionArtifact .Osaka fastLoadReturnPath
            (by simpa [seeded, BigLoad.loadReturned, BigLoad.loadLoop,
              Artifact.submissionArtifact] using seededCode)
            (by simpa [seeded, BigLoad.loadReturned, BigLoad.loadLoop, State.fork] using seededFork)
            (run_loadReturn s A n b eWord mWord baseOff expWord rest seeded
              hrest seededCode seededHalt)
            (by simpa [seeded, BigLoad.loadReturned, BigLoad.loadLoop] using seededHalt)
            (by simpa [seeded, BigLoad.loadReturned, BigLoad.loadLoop, State.fork] using seededNp)
          simpa [fastReturned, fastEntry, fastAt, readyAt, frame, hzero', hlarge,
            hwide, heven, touched, cleared, seeded,
            MontgomeryWrapperBlock.loadLowLeaf,
            MontgomeryReadyValue.directReady,
            MontgomeryBaseLoadValue.loadBaseLeaf,
            MontgomerySetupBlock.flatLeaf, BigLoad.loadReturned,
            BigLoad.loadLoop] using
            hp.trans (hl.trans (hw.trans (hpar.trans
              (hcall.trans (hclear.trans (hreturn.trans
                (hload.trans hloadReturn)))))))

theorem fastReturned_correct (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (m : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hb : b ≤ 32 * n)
    (hoff : baseOff < 2 ^ 256) (hm : 0 < m)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hmod : Limbs.Represents s.memory 0 n m)
    (hbase : Limbs.Represents s.memory 1024 n 0)
    (hacc : Limbs.Represents s.memory 2048 n 0) :
    Limbs.Represents
        (fastReturned s A n b eWord mWord baseOff expWord rest).memory 0 n m ∧
      Limbs.Represents
        (fastReturned s A n b eWord mWord baseOff expWord rest).memory 1024 n
          (Precompile.bytesToNatPadded s.executionEnv.calldata baseOff b) ∧
      Limbs.Represents
        (fastReturned s A n b eWord mWord baseOff expWord rest).memory 2048 n 0 ∧
      Limbs.Represents
        (fastReturned s A n b eWord mWord baseOff expWord rest).memory 3072 n 1 := by
  have hnzero : ¬n = 0 := by omega
  have hnlarge : ¬32 < n := by omega
  have hfit : ¬32 * n < b := by omega
  have hoddBranch :
      ¬(MachineState.readWord s.memory 0).toNat % 2 = 0 := by omega
  have htouched := MontgomeryReadyValue.directReady_correct
    (MontgomeryWrapperBlock.loadLowLeaf s 0) baseOff b n m hn hN hoff hb hm
    (by simpa [MontgomeryWrapperBlock.loadLowLeaf] using hmod)
    (by simpa [MontgomeryWrapperBlock.loadLowLeaf] using hbase)
    (by simpa [MontgomeryWrapperBlock.loadLowLeaf] using hacc)
  simpa [fastReturned, readyAt, fastAt, frame, hnzero, hnlarge, hfit,
    hoddBranch,
    MontgomeryWrapperBlock.loadLowLeaf] using htouched

theorem initialized_correct (s : State) (A : UInt256) (n b : Nat)
    (eWord mWord : UInt256) (baseOff : Nat) (expWord : UInt256)
    (rest : List UInt256) (m base : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hm : 0 < m)
    (hmod : Limbs.Represents s.memory 0 n m)
    (hbase : Limbs.Represents s.memory 1024 n base)
    (hacc : Limbs.Represents s.memory 2048 n 0)
    (hone : Limbs.Represents s.memory 3072 n 1) :
    Limbs.Represents
        (initialized s A n b eWord mWord baseOff expWord rest).memory
          2048 n (1 % m) ∧
      Limbs.Represents
        (initialized s A n b eWord mWord baseOff expWord rest).memory
          1024 n base ∧
      Limbs.Represents
        (initialized s A n b eWord mWord baseOff expWord rest).memory
          0 n m := by
  simpa [initialized, frame] using
    MontgomeryReadyValue.initialize_correct s n base m 2126
      (frame A n b eWord mWord baseOff expWord rest) hn hN hm
      hmod hbase hacc hone

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryFastBaseBlock
