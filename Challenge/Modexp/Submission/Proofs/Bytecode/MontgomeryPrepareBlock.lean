import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryPrepareValue

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryPrepareBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Montgomery

/- The private setup frame contains only the caller value, count, and suffix. -/
def frame (A : UInt256) (n : Nat) (tail : List UInt256) : List UInt256 :=
  [A, UInt256.ofNat n] ++ tail

def setupEntry (s : State) (A : UInt256) (n : Nat) (tail : List UInt256) : State :=
  {s with pc := UInt256.ofNat 2126, stack := frame A n tail}

def setupAt (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (pc : Nat) : State :=
  {s with pc := UInt256.ofNat pc, stack := frame A n tail}

def setupEffects (s : State) (n : Nat) : MontgomeryWrapperBlock.Effects :=
  if n = 0 ∨ 32 < n then
    MontgomeryWrapperBlock.effectsOf s
  else
    let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
    if (MachineState.readWord s.memory 0).toNat % 2 = 0 then
      MontgomeryWrapperBlock.effectsOf touched
    else
      let loaded := MontgomeryWrapperBlock.loadLowLeaf touched 0
      let np := InverseArithmetic.nprime (MachineState.readWord loaded.memory 0)
      MontgomeryWrapperBlock.effectsOf
        (MontgomeryPrepareValue.prepare loaded n np)

def setupReturned (s : State) (A : UInt256) (n : Nat) (tail : List UInt256) : State :=
  MontgomeryWrapperBlock.returnedState s (setupEffects s n) 1343 (frame A n tail)

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
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def zeroGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1545 .JUMPDEST,
   opAt 1546 (.Dup ⟨1, by decide⟩),
   opAt 1547 .ISZERO,
   pushAt 1548 2 2249,
   opAt 1549 .JUMPI]

def largeGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1550 1 32,
   opAt 1551 (.Dup ⟨2, by decide⟩),
   opAt 1552 .GT,
   pushAt 1553 2 2249,
   opAt 1554 .JUMPI]

def parityGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1555 0 0,
   opAt 1556 .MLOAD,
   pushAt 1557 1 1,
   opAt 1558 .AND,
   opAt 1559 .ISZERO,
   pushAt 1560 2 2249,
   opAt 1561 .JUMPI]

def inverseCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1562 2 2160,
   pushAt 1563 0 0,
   opAt 1564 .MLOAD,
   pushAt 1565 2 1447,
   opAt 1566 .JUMP]

def unitCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1567 .JUMPDEST,
   pushAt 1568 2 2170,
   pushAt 1569 0 0,
   opAt 1570 (.Dup ⟨4, by decide⟩),
   pushAt 1571 2 1786,
   opAt 1572 .JUMP]

def copyUnitPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1573 .JUMPDEST,
   opAt 1574 (.Dup ⟨2, by decide⟩),
   pushAt 1575 2 2186,
   opAt 1576 (.Swap ⟨0, by decide⟩),
   pushAt 1577 2 7168,
   pushAt 1578 2 2048,
   pushAt 1579 2 58,
   opAt 1580 .JUMP]

def r2CallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1581 .JUMPDEST,
   opAt 1582 (.Dup ⟨2, by decide⟩),
   pushAt 1583 2 2200,
   opAt 1584 (.Swap ⟨0, by decide⟩),
   pushAt 1585 0 0,
   opAt 1586 (.Swap ⟨0, by decide⟩),
   opAt 1587 (.Dup ⟨3, by decide⟩),
   opAt 1588 (.Swap ⟨0, by decide⟩),
   pushAt 1589 2 1904,
   opAt 1590 .JUMP]

def coreCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1591 .JUMPDEST,
   opAt 1592 (.Dup ⟨2, by decide⟩),
   pushAt 1593 2 2222,
   opAt 1594 (.Swap ⟨0, by decide⟩),
   opAt 1595 (.Dup ⟨2, by decide⟩),
   opAt 1596 (.Swap ⟨0, by decide⟩),
   pushAt 1597 0 0,
   pushAt 1598 2 3072,
   pushAt 1599 2 8192,
   pushAt 1600 2 1024,
   pushAt 1601 2 1625,
   opAt 1602 .JUMP]

def copyBasePath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1603 .JUMPDEST,
   opAt 1604 (.Dup ⟨2, by decide⟩),
   pushAt 1605 2 2238,
   opAt 1606 (.Swap ⟨0, by decide⟩),
   pushAt 1607 2 3072,
   pushAt 1608 2 1024,
   pushAt 1609 2 58,
   opAt 1610 .JUMP]

def finalPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1611 .JUMPDEST,
   opAt 1612 (.Dup ⟨0, by decide⟩),
   pushAt 1613 2 11264,
   opAt 1614 .MSTORE,
   opAt 1615 .POP,
   pushAt 1616 2 1343,
   opAt 1617 .JUMP]

def fallbackPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1618 .JUMPDEST,
   pushAt 1619 2 1343,
   opAt 1620 .JUMP]

@[simp] private theorem setupPCs (i : Nat) (hi : 1545 ≤ i) (hii : i ≤ 1621) :
    Artifact.submissionArtifact.instructionPC i =
      [2126,2127,2128,2129,2132,2133,2135,2136,2137,2140,
       2141,2142,2143,2145,2146,2147,2150,2151,2154,2155,
       2156,2159,2160,2161,2164,2165,2166,2169,2170,2171,
       2172,2175,2176,2179,2182,2185,2186,2187,2188,2191,
       2192,2193,2194,2195,2196,2199,2200,2201,2202,2205,
       2206,2207,2208,2209,2212,2215,2218,2221,2222,2223,
       2224,2227,2228,2231,2234,2237,2238,2239,2240,2243,
       2244,2245,2248,2249,2250,2253,2254][i - 1545]! := by
  interval_cases i <;> decide

@[simp] private theorem fallbackDest :
    Decode.isValidJumpDest submissionBytecode 2249 = true :=
  Artifact.isValidJumpDest_index 1618 (by rfl)

@[simp] private theorem inverseDest :
    Decode.isValidJumpDest submissionBytecode 1447 = true :=
  Artifact.isValidJumpDest_index 1072 (by rfl)

@[simp] private theorem unitDest :
    Decode.isValidJumpDest submissionBytecode 1786 = true :=
  Artifact.isValidJumpDest_index 1331 (by rfl)

@[simp] private theorem copyDest :
    Decode.isValidJumpDest submissionBytecode 58 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)

@[simp] private theorem r2Dest :
    Decode.isValidJumpDest submissionBytecode 1904 = true :=
  Artifact.isValidJumpDest_index 1408 (by rfl)

@[simp] private theorem coreDest :
    Decode.isValidJumpDest submissionBytecode 1625 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

@[simp] private theorem setupReturnDest :
    Decode.isValidJumpDest submissionBytecode 1343 = true :=
  Artifact.isValidJumpDest_index 995 (by rfl)

private theorem lowBit (w : UInt256) :
    (UInt256.land (UInt256.ofNat 1) w).toNat = w.toNat % 2 := by
  rw [Word.word_toNat_land, Word.word_toNat_ofNat]
  change 1 &&& w.toNat = w.toNat % 2
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

private theorem frame_length (A : UInt256) (n : Nat) (tail : List UInt256) :
    (frame A n tail).length = tail.length + 2 := by
  simp [frame]

private theorem saved_length (A : UInt256) (n : Nat) (np : UInt256)
    (tail : List UInt256) :
    (np :: frame A n tail).length = tail.length + 3 := by
  simp [frame]

set_option linter.unusedSimpArgs false

theorem run_zeroPass (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973) (hn : 1 ≤ n) (hbound : n < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath (setupEntry s A n tail) =
      some (setupAt s A n tail 2133) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero (UInt256.ofNat n)) := by
    simp only [UInt256.isZero, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound,
      if_neg (show n ≠ 0 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [zeroGuardPath, opAt, pushAt, wfOp, setupEntry, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_zeroFallback (s : State) (A : UInt256) (tail : List UInt256)
    (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath (setupEntry s A 0 tail) =
      some (setupAt s A 0 tail 2249) := by
  have hc : UInt256.isTrue (UInt256.isZero (UInt256.ofNat 0)) := by decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [zeroGuardPath, opAt, pushAt, wfOp, setupEntry, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_largePass (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973) (hbound : n < 2 ^ 256) (hN : n ≤ 32)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath (setupAt s A n tail 2133) =
      some (setupAt s A n tail 2141) := by
  have hc : ¬ UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide),
      if_neg (show ¬n > 32 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_largeFallback (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973) (hlarge : 32 < n) (hbound : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath (setupAt s A n tail 2133) =
      some (setupAt s A n tail 2249) := by
  have hc : UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide),
      if_pos hlarge]
    decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_parityOdd (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath (setupAt s A n tail 2141) =
      some (setupAt (MontgomeryWrapperBlock.loadLowLeaf s 0) A n tail 2151) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, hodd]
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hzeroNat,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_parityEven (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973)
    (heven : (MachineState.readWord s.memory 0).toNat % 2 = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath (setupAt s A n tail 2141) =
      some (setupAt (MontgomeryWrapperBlock.loadLowLeaf s 0) A n tail 2249) := by
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, heven]
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hzeroNat, hcode,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_inverseCall (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock inverseCallPath
        (setupAt s A n tail 2151) =
      some (MontgomeryInverseBlock.inverseEntry
        (MontgomeryWrapperBlock.loadLowLeaf s 0)
        (MachineState.readWord s.memory 0) 2160 (frame A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  simp [inverseCallPath, opAt, pushAt, wfOp, setupAt, frame,
    MontgomeryInverseBlock.inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hzeroNat,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_unitCall (s : State) (A : UInt256) (n : Nat) (low : UInt256)
    (tail : List UInt256) (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock unitCallPath
        (MontgomeryInverseBlock.inverseReturned s low 2160 (frame A n tail)) =
      some (MontgomeryOneBlock.entry s n 2170
        (InverseArithmetic.nprime low :: frame A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [unitCallPath, opAt, pushAt, wfOp, frame,
    MontgomeryInverseBlock.inverseReturned, MontgomeryOneBlock.entry,
    MontgomeryOneBlock.atFrame, MontgomeryOneBlock.frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hzeroWord]

theorem run_copyUnit (s : State) (A : UInt256) (n : Nat) (np : UInt256)
    (tail : List UInt256) (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock copyUnitPath
        ({ MontgomeryWrapperBlock.unitSetupLeaf s n with
          pc := 2170, stack := np :: frame A n tail }) =
      some (BigHelpers.copyEntry (MontgomeryWrapperBlock.unitSetupLeaf s n)
        2048 7168 n 2186 (np :: frame A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [copyUnitPath, opAt, pushAt, wfOp, frame,
    MontgomeryWrapperBlock.unitSetupLeaf, MontgomerySetupBlock.flatLeaf,
    BigHelpers.copyEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, List.exchange]

theorem run_r2Call (s : State) (A : UInt256) (n : Nat) (np : UInt256)
    (tail : List UInt256) (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock r2CallPath
        ({s with pc := 2186, stack := np :: frame A n tail}) =
      some (MontgomerySetupBlock.r2At s n np 0 2200 (np :: frame A n tail) 1904) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [r2CallPath, opAt, pushAt, wfOp, frame,
    MontgomerySetupBlock.r2At, MontgomerySetupBlock.r2EntryAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hzeroWord, List.exchange]

theorem run_coreCall (s : State) (A : UInt256) (n : Nat) (np : UInt256)
    (tail : List UInt256) (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock coreCallPath
        ({s with pc := 2200, stack := np :: frame A n tail}) =
      some (MontgomerySetupBlock.coreEntry s 1024 8192 3072 0 n np 2222
        (np :: frame A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [coreCallPath, opAt, pushAt, wfOp, frame,
    MontgomerySetupBlock.coreEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hzeroWord, List.exchange]

theorem run_copyBase (s : State) (A : UInt256) (n : Nat) (np : UInt256)
    (tail : List UInt256) (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock copyBasePath
        ({s with pc := 2222, stack := np :: frame A n tail}) =
      some (BigHelpers.copyEntry s 1024 3072 n 2238 (np :: frame A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [copyBasePath, opAt, pushAt, wfOp, frame, BigHelpers.copyEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, List.exchange]

theorem run_final (s : State) (A : UInt256) (n : Nat) (np : UInt256)
    (tail : List UInt256) (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock finalPath
        ({s with pc := 2238, stack := np :: frame A n tail}) =
      some ({MontgomeryWrapperBlock.storeNpLeaf s np with
        pc := UInt256.ofNat 1343, stack := frame A n tail}) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [finalPath, opAt, pushAt, wfOp, frame,
    MontgomeryWrapperBlock.storeNpLeaf, MachineState.writeBytes,
    Data.Bytes.natToBytesPadded,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, State.activeWordsAfterUInt256]

theorem run_fallback (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fallbackPath (setupAt s A n tail 2249) =
      some ({s with pc := UInt256.ofNat 1343, stack := frame A n tail}) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [fallbackPath, opAt, pushAt, wfOp, setupAt, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

private theorem frame_trans (s t u : State)
    (ht : {t with memory := s.memory, activeWords := s.activeWords} = s)
    (hu : {u with memory := t.memory, activeWords := t.activeWords} = t) :
    {u with memory := s.memory, activeWords := s.activeWords} = s := by
  have h := congrArg (fun v : State =>
    {v with memory := s.memory, activeWords := s.activeWords}) hu
  exact h.trans ht

private theorem unitSetup_frame (s : State) (n : Nat) :
    {MontgomeryWrapperBlock.unitSetupLeaf s n with
      memory := s.memory, activeWords := s.activeWords} = s := by
  cases s
  rfl

private theorem flatLeaf_frame (s result : State) :
    {MontgomerySetupBlock.flatLeaf s result with
      memory := s.memory, activeWords := s.activeWords} = s := by
  cases s
  rfl

private theorem storeNp_frame (s : State) (np : UInt256) :
    {MontgomeryWrapperBlock.storeNpLeaf s np with
      memory := s.memory, activeWords := s.activeWords} = s := by
  cases s
  rfl

private theorem loadLow_frame (s : State) (ptr : UInt256) :
    {MontgomeryWrapperBlock.loadLowLeaf s ptr with
      memory := s.memory, activeWords := s.activeWords} = s := by
  cases s
  rfl

private theorem prepare_frame (s : State) (n : Nat) (np : UInt256) :
    {MontgomeryPrepareValue.prepare s n np with
      memory := s.memory, activeWords := s.activeWords} = s := by
  let unit := MontgomeryWrapperBlock.unitSetupLeaf s n
  let acc := MontgomerySetupBlock.flatLeaf unit
    (BigHelpers.copyReturned unit 2048 7168 n 0 [])
  let r2 := MontgomeryWrapperValue.r2Leaf acc n np
  let encoded := MontgomeryWrapperValue.coreLeaf r2 1024 8192 3072 n np
  let base := MontgomerySetupBlock.flatLeaf encoded
    (BigHelpers.copyReturned encoded 1024 3072 n 0 [])
  have hunit := unitSetup_frame s n
  have hacc := frame_trans s unit acc hunit (flatLeaf_frame unit
    (BigHelpers.copyReturned unit 2048 7168 n 0 []))
  have hr2 := frame_trans s acc r2 hacc
    (MontgomeryWrapperValue.r2Leaf_frame acc n np)
  have hencoded := frame_trans s r2 encoded hr2
    (MontgomeryWrapperValue.coreLeaf_frame r2 1024 8192 3072 n np)
  have hbase := frame_trans s encoded base hencoded
    (flatLeaf_frame encoded (BigHelpers.copyReturned encoded 1024 3072 n 0 []))
  have hprepare := frame_trans s base
    (MontgomeryWrapperBlock.storeNpLeaf base np) hbase
    (storeNp_frame base np)
  simpa only [MontgomeryPrepareValue.prepare, unit, acc, r2, encoded, base] using hprepare

private theorem unitReturned_frame (s : State) (n : Nat) (ret : UInt256)
    (saved : List UInt256) :
    MontgomeryOneBlock.returned s n ret saved =
      {MontgomeryWrapperBlock.unitSetupLeaf s n with
        pc := ret, stack := saved} := by
  cases s
  rfl

private theorem copyReturned_frame (s : State) (dst src : UInt256) (count : Nat)
    (ret : UInt256) (saved : List UInt256) :
    BigHelpers.copyReturned s dst src count ret saved =
      {MontgomerySetupBlock.flatLeaf s
          (BigHelpers.copyReturned s dst src count 0 []) with
        pc := ret, stack := saved} := by
  cases s
  rfl

private theorem returnedState_effects (s : State)
    (effects : MontgomeryWrapperBlock.Effects) (ret : UInt256)
    (saved : List UInt256) :
    MontgomeryWrapperBlock.returnedState s
        (MontgomeryWrapperBlock.effectsOf
          (MontgomeryWrapperBlock.returnedState s effects ret saved)) ret saved =
      MontgomeryWrapperBlock.returnedState s effects ret saved := rfl

private theorem returnedState_loadLow (s : State)
    (effects : MontgomeryWrapperBlock.Effects) (ptr ret : UInt256)
    (saved : List UInt256) :
    MontgomeryWrapperBlock.returnedState s effects ret saved =
      MontgomeryWrapperBlock.returnedState
        (MontgomeryWrapperBlock.loadLowLeaf s ptr) effects ret saved := by
  cases s
  rfl

private theorem frame_env (s t : State)
    (hframe : {t with memory := s.memory, activeWords := s.activeWords} = s) :
    t.executionEnv = s.executionEnv := by
  have h := congrArg (fun u : State => u.executionEnv) hframe
  exact h

private theorem frame_halt (s t : State)
    (hframe : {t with memory := s.memory, activeWords := s.activeWords} = s) :
    t.halt = s.halt := by
  have h := congrArg State.halt hframe
  exact h

private theorem prepare_erased (s : State) (n : Nat) (np : UInt256) :
    MontgomeryWrapperBlock.eraseEffects
        (MontgomeryPrepareValue.prepare s n np) =
      MontgomeryWrapperBlock.eraseEffects s := by
  have h := congrArg MontgomeryWrapperBlock.eraseEffects (prepare_frame s n np)
  simpa only [MontgomeryWrapperBlock.eraseEffects] using h

private theorem artifactCode :
    Artifact.submissionArtifact.code = submissionBytecode := by
  rfl

private theorem returnedState_self (s : State) (ret : UInt256)
    (saved : List UInt256) :
    MontgomeryWrapperBlock.returnedState s
        (MontgomeryWrapperBlock.effectsOf s) ret saved =
      {s with pc := ret, stack := saved} := by
  rfl

theorem setupReturned_correct (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (baseValue M : Nat) (hN : n ≤ 32) (hM : 0 < M)
    (hmod : Limbs.Represents s.memory 0 n M)
    (hbase : Limbs.Represents s.memory 1024 n baseValue)
    (hacc : Limbs.Represents s.memory 2048 n (1 % M)) :
    Limbs.Represents (setupReturned s A n tail).memory 0 n M ∧
      Limbs.Represents (setupReturned s A n tail).memory 1024 n
        (if M % 2 = 1 then Domain.encode M n baseValue else baseValue) ∧
      Limbs.Represents (setupReturned s A n tail).memory 2048 n
        (if M % 2 = 1 then Domain.encode M n (1 % M) else 1 % M) ∧
      (M % 2 = 1 →
        (M * (MachineState.readWord (setupReturned s A n tail).memory
          11264).toNat + 1) % (2 ^ 256) = 0) := by
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hbound := hmod.1
    rw [hn0, pow_zero] at hbound
    omega
  have hguard : ¬(n = 0 ∨ 32 < n) := by omega
  have hparity := MontgomeryWrapperBlock.modulusLow_parity s n M hn hmod
  by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
  · have hMeven : M % 2 = 0 := by omega
    have hmodTouched : Limbs.Represents
        (MontgomeryWrapperBlock.loadLowLeaf s 0).memory 0 n M := by
      simpa [MontgomeryWrapperBlock.loadLowLeaf] using hmod
    have hbaseTouched : Limbs.Represents
        (MontgomeryWrapperBlock.loadLowLeaf s 0).memory 1024 n baseValue := by
      simpa [MontgomeryWrapperBlock.loadLowLeaf] using hbase
    have haccTouched : Limbs.Represents
        (MontgomeryWrapperBlock.loadLowLeaf s 0).memory 2048 n (1 % M) := by
      simpa [MontgomeryWrapperBlock.loadLowLeaf] using hacc
    have hreturnMod : Limbs.Represents
        (setupReturned s A n tail).memory 0 n M := by
      simpa [setupReturned, setupEffects, hguard, heven,
        MontgomeryWrapperBlock.returnedState,
        MontgomeryWrapperBlock.effectsOf] using hmodTouched
    have hreturnBase : Limbs.Represents
        (setupReturned s A n tail).memory 1024 n baseValue := by
      simpa [setupReturned, setupEffects, hguard, heven,
        MontgomeryWrapperBlock.returnedState,
        MontgomeryWrapperBlock.effectsOf] using hbaseTouched
    have hreturnAcc : Limbs.Represents
        (setupReturned s A n tail).memory 2048 n (1 % M) := by
      simpa [setupReturned, setupEffects, hguard, heven,
        MontgomeryWrapperBlock.returnedState,
        MontgomeryWrapperBlock.effectsOf] using haccTouched
    refine ⟨hreturnMod, ?_, ?_, ?_⟩
    · simpa [hMeven] using hreturnBase
    · simpa [hMeven] using hreturnAcc
    · intro hModOdd
      omega
  · have hModOdd : M % 2 = 1 := by omega
    let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
    let loaded := MontgomeryWrapperBlock.loadLowLeaf touched 0
    let np := InverseArithmetic.nprime (MachineState.readWord loaded.memory 0)
    have hmodLoaded : Limbs.Represents loaded.memory 0 n M := by
      simpa [loaded, touched, MontgomeryWrapperBlock.loadLowLeaf] using hmod
    have hbaseLoaded : Limbs.Represents loaded.memory 1024 n baseValue := by
      simpa [loaded, touched, MontgomeryWrapperBlock.loadLowLeaf] using hbase
    have hinv : (M * np.toNat + 1) % (2 ^ 256) = 0 := by
      simpa [np] using
        (MontgomeryWrapperBlock.modulusInverse_correct loaded n M hn hModOdd hmodLoaded)
    have hprepared := MontgomeryPrepareValue.prepare_correct loaded n np baseValue M
      hn hN hM hModOdd hinv hmodLoaded hbaseLoaded
    have hpreparedAcc : Limbs.Represents
        (MontgomeryPrepareValue.prepare loaded n np).memory 2048 n
          (Domain.encode M n (1 % M)) := by
      have hencode : Domain.encode M n (1 % M) = Domain.encode M n 1 := by
        by_cases hMone : M = 1
        · subst M
          simp [Domain.encode, Domain.R, Nat.mod_one]
        · have hMgt : 1 < M := by omega
          have hone : 1 % M = 1 := Nat.mod_eq_of_lt (by omega)
          simp [hone]
      rw [hencode]
      exact hprepared.2.2.1
    have hpreparedInv :
        (M * (MachineState.readWord
          (MontgomeryPrepareValue.prepare loaded n np).memory 11264).toNat + 1) %
            (2 ^ 256) = 0 := by
      rw [hprepared.2.2.2]
      exact hinv
    have hresult := And.intro hprepared.1
      (And.intro hprepared.2.1 (And.intro hpreparedAcc hpreparedInv))
    simpa [setupReturned, setupEffects, hguard, heven, hModOdd, touched, loaded, np,
      MontgomeryWrapperBlock.returnedState, MontgomeryWrapperBlock.effectsOf] using hresult

def gasSteps_setup (s : State) (A : UInt256) (n : Nat) (tail : List UInt256)
    (hcap : tail.length < 973) (hbound : n < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (setupEntry s A n tail) (setupReturned s A n tail) := by
  by_cases hzero : n = 0
  · subst n
    have guard := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      zeroGuardPath (s := setupEntry s A 0 tail)
      (by simpa only [setupEntry, artifactCode] using hcode)
      (by simpa [setupEntry, State.fork] using hfork)
      (run_zeroFallback s A tail hcap hcode hrun)
      (by simpa [setupEntry] using hrun) (by simpa [setupEntry, State.fork] using hnp)
    have finish := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      fallbackPath (s := setupAt s A 0 tail 2249)
      (by simpa only [setupAt, artifactCode] using hcode)
      (by simpa [setupAt, State.fork] using hfork)
      (run_fallback s A 0 tail hcap hcode hrun)
      (by simpa [setupAt] using hrun) (by simpa [setupAt, State.fork] using hnp)
    refine GasSteps.cast (guard.trans finish) rfl ?_
    rw [setupReturned, setupEffects,
      if_pos (show (0 : Nat) = 0 ∨ 32 < 0 by omega)]
    simp only [MontgomeryWrapperBlock.returnedState,
      MontgomeryWrapperBlock.effectsOf, Word.literal_eq_ofNat]
  · have hn : 1 ≤ n := by omega
    have zero := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      zeroGuardPath (s := setupEntry s A n tail)
      (by simpa only [setupEntry, artifactCode] using hcode)
      (by simpa [setupEntry, State.fork] using hfork)
      (run_zeroPass s A n tail hcap hn hbound hrun)
      (by simpa [setupEntry] using hrun) (by simpa [setupEntry, State.fork] using hnp)
    by_cases hlarge : 32 < n
    · have guard := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        largeGuardPath (s := setupAt s A n tail 2133)
        (by simpa only [setupAt, artifactCode] using hcode)
        (by simpa [setupAt, State.fork] using hfork)
        (run_largeFallback s A n tail hcap hlarge hbound hcode hrun)
        (by simpa [setupAt] using hrun) (by simpa [setupAt, State.fork] using hnp)
      have finish := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        fallbackPath (s := setupAt s A n tail 2249)
        (by simpa only [setupAt, artifactCode] using hcode)
        (by simpa [setupAt, State.fork] using hfork)
        (run_fallback s A n tail hcap hcode hrun)
        (by simpa [setupAt] using hrun) (by simpa [setupAt, State.fork] using hnp)
      refine GasSteps.cast (zero.trans (guard.trans finish)) rfl ?_
      rw [setupReturned, setupEffects,
        if_pos (show n = 0 ∨ 32 < n by omega)]
      simp only [MontgomeryWrapperBlock.returnedState,
        MontgomeryWrapperBlock.effectsOf, Word.literal_eq_ofNat]
    · have hN : n ≤ 32 := by omega
      have large := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        largeGuardPath (s := setupAt s A n tail 2133)
        (by simpa only [setupAt, artifactCode] using hcode)
        (by simpa [setupAt, State.fork] using hfork)
        (run_largePass s A n tail hcap hbound hN hrun)
        (by simpa [setupAt] using hrun) (by simpa [setupAt, State.fork] using hnp)
      by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
      · let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
        have parity := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          parityGuardPath (s := setupAt s A n tail 2141)
          (by simpa only [setupAt, artifactCode] using hcode)
          (by simpa [setupAt, State.fork] using hfork)
          (run_parityEven s A n tail hcap heven hcode hrun)
          (by simpa [setupAt] using hrun) (by simpa [setupAt, State.fork] using hnp)
        have touchedCode : touched.executionEnv.code = submissionBytecode := by
          simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hcode
        have touchedHalt : touched.halt = .Running := by
          simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hrun
        have touchedFork : touched.fork = .Osaka := by
          simpa only [touched, MontgomeryWrapperBlock.loadLowLeaf, State.fork] using hfork
        have touchedNp : Precompile.isPrecompileWithConfig touched.executionEnv.precompileConfig
            touched.executionEnv.fork touched.executionEnv.codeAddr = false := by
          simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hnp
        have finish := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          fallbackPath (s := setupAt touched A n tail 2249)
          (by simpa only [setupAt, artifactCode] using touchedCode)
          (by simpa [setupAt, State.fork] using touchedFork)
          (run_fallback touched A n tail hcap
            touchedCode touchedHalt)
          (by simpa [setupAt] using touchedHalt)
          (by simpa [setupAt, State.fork] using touchedNp)
        have hret := returnedState_loadLow s
          (MontgomeryWrapperBlock.effectsOf touched) 0 1343 (frame A n tail)
        rw [setupReturned, setupEffects,
          if_neg (show ¬(n = 0 ∨ 32 < n) by omega), if_pos heven, hret]
        refine GasSteps.cast (zero.trans (large.trans (parity.trans finish))) rfl ?_
        simp [touched, MontgomeryWrapperBlock.loadLowLeaf,
          MontgomeryWrapperBlock.returnedState, MontgomeryWrapperBlock.effectsOf,
          Word.literal_eq_ofNat]
      · have hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1 := by omega
        let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
        let loaded := MontgomeryWrapperBlock.loadLowLeaf touched 0
        let low := MachineState.readWord s.memory 0
        let np := InverseArithmetic.nprime low
        let saved := np :: frame A n tail
        have parity := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          parityGuardPath (s := setupAt s A n tail 2141)
          (by simpa only [setupAt, artifactCode] using hcode)
          (by simpa [setupAt, State.fork] using hfork)
          (run_parityOdd s A n tail hcap hodd hrun)
          (by simpa [setupAt] using hrun) (by simpa [setupAt, State.fork] using hnp)
        have touchedCode : touched.executionEnv.code = submissionBytecode := by
          simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hcode
        have touchedHalt : touched.halt = .Running := by
          simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hrun
        have touchedFork : touched.fork = .Osaka := by
          simpa only [touched, MontgomeryWrapperBlock.loadLowLeaf, State.fork] using hfork
        have touchedNp : Precompile.isPrecompileWithConfig touched.executionEnv.precompileConfig
            touched.executionEnv.fork touched.executionEnv.codeAddr = false := by
          simpa [touched, MontgomeryWrapperBlock.loadLowLeaf] using hnp
        have inverseCall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          inverseCallPath (s := setupAt touched A n tail 2151)
          (by simpa only [setupAt, artifactCode] using touchedCode)
          (by simpa [setupAt, State.fork] using touchedFork)
          (run_inverseCall touched A n tail hcap touchedCode touchedHalt)
          (by simpa [setupAt] using touchedHalt)
          (by simpa [setupAt, State.fork] using touchedNp)
        have loadedCode : loaded.executionEnv.code = submissionBytecode := by
          simpa [loaded, touched, MontgomeryWrapperBlock.loadLowLeaf] using hcode
        have loadedHalt : loaded.halt = .Running := by
          simpa [loaded, touched, MontgomeryWrapperBlock.loadLowLeaf] using hrun
        have loadedFork : loaded.fork = .Osaka := by
          simpa only [loaded, touched, MontgomeryWrapperBlock.loadLowLeaf, State.fork] using hfork
        have loadedNp : Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig
            loaded.executionEnv.fork loaded.executionEnv.codeAddr = false := by
          simpa [loaded, touched, MontgomeryWrapperBlock.loadLowLeaf] using hnp
        have inverse := MontgomeryInverseBlock.gasSteps_inverse loaded low 2160
          (frame A n tail) (by rw [frame_length]; omega)
          loadedCode loadedFork inverseDest loadedHalt loadedNp
        have unitCall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          unitCallPath (s := MontgomeryInverseBlock.inverseReturned loaded low 2160
            (frame A n tail))
          (by simpa only [MontgomeryInverseBlock.inverseReturned, artifactCode] using loadedCode)
          (by simpa [MontgomeryInverseBlock.inverseReturned, State.fork] using loadedFork)
          (run_unitCall loaded A n low tail hcap loadedCode loadedHalt)
          (by simpa [MontgomeryInverseBlock.inverseReturned] using loadedHalt)
          (by simpa [MontgomeryInverseBlock.inverseReturned, State.fork] using loadedNp)
        let unit := MontgomeryWrapperBlock.unitSetupLeaf loaded n
        have unitCode : unit.executionEnv.code = submissionBytecode := by
          simpa [unit, MontgomeryWrapperBlock.unitSetupLeaf,
            MontgomerySetupBlock.flatLeaf] using loadedCode
        have unitHalt : unit.halt = .Running := by
          simpa [unit, MontgomeryWrapperBlock.unitSetupLeaf,
            MontgomerySetupBlock.flatLeaf] using loadedHalt
        have unitFork : unit.fork = .Osaka := by
          simpa only [unit, MontgomeryWrapperBlock.unitSetupLeaf,
            MontgomerySetupBlock.flatLeaf, State.fork] using loadedFork
        have unitNp : Precompile.isPrecompileWithConfig unit.executionEnv.precompileConfig
            unit.executionEnv.fork unit.executionEnv.codeAddr = false := by
          simpa [unit, MontgomeryWrapperBlock.unitSetupLeaf,
            MontgomerySetupBlock.flatLeaf] using loadedNp
        have unitRun := MontgomeryOneBlock.gasSteps_unit loaded n 2170 saved
          (by rw [saved_length]; omega) hn hN loadedCode loadedFork loadedHalt loadedNp
          unitDest
        have unitRun' : GasSteps
            (MontgomeryOneBlock.entry loaded n 2170 saved)
            ({unit with pc := 2170, stack := saved}) := by
          simpa only [unitReturned_frame, unit, saved, np] using unitRun
        have copyCall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          copyUnitPath (s := {unit with pc := 2170, stack := saved})
          (by simpa only [unit, artifactCode] using unitCode)
          (by simpa [unit, State.fork] using unitFork)
          (run_copyUnit loaded A n np tail hcap loadedCode loadedHalt)
          (by simpa [unit] using unitHalt) (by simpa [unit, State.fork] using unitNp)
        have copyRun := BigHelpers.gasSteps_copy unit 2048 7168 n 2186 saved
          (by rw [saved_length]; omega) hbound unitCode unitFork unitHalt unitNp
          (Artifact.isValidJumpDest_index 1581 (by rfl))
        let acc := MontgomerySetupBlock.flatLeaf unit
          (BigHelpers.copyReturned unit 2048 7168 n 0 [])
        have copyState : BigHelpers.copyReturned unit 2048 7168 n 2186 saved =
            {acc with pc := 2186, stack := saved} := by
          simpa [acc] using (copyReturned_frame unit 2048 7168 n 2186 saved)
        rw [copyState] at copyRun
        have accCode : acc.executionEnv.code = submissionBytecode := by
          simpa [acc, MontgomerySetupBlock.flatLeaf] using unitCode
        have accHalt : acc.halt = .Running := by
          simpa [acc, MontgomerySetupBlock.flatLeaf] using unitHalt
        have accFork : acc.fork = .Osaka := by
          simpa only [acc, MontgomerySetupBlock.flatLeaf, State.fork] using unitFork
        have accNp : Precompile.isPrecompileWithConfig acc.executionEnv.precompileConfig
            acc.executionEnv.fork acc.executionEnv.codeAddr = false := by
          simpa [acc, MontgomerySetupBlock.flatLeaf] using unitNp
        have r2Call := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          r2CallPath (s := {acc with pc := 2186, stack := saved})
          (by simpa only [acc, artifactCode] using accCode)
          (by simpa [acc, State.fork] using accFork)
          (run_r2Call acc A n np tail hcap accCode accHalt)
          (by simpa [acc] using accHalt) (by simpa [acc, State.fork] using accNp)
        let r2 := MontgomeryWrapperValue.r2Leaf acc n np
        have r2Env : r2.executionEnv = acc.executionEnv :=
          frame_env acc r2 (MontgomeryWrapperValue.r2Leaf_frame acc n np)
        have r2Code : r2.executionEnv.code = submissionBytecode := by
          rw [r2Env]
          exact accCode
        have r2Halt : r2.halt = .Running := by
          exact frame_halt acc r2 (MontgomeryWrapperValue.r2Leaf_frame acc n np) |>.trans accHalt
        have r2Fork : r2.fork = .Osaka := by
          simpa only [State.fork, r2Env] using accFork
        have r2Np : Precompile.isPrecompileWithConfig r2.executionEnv.precompileConfig
            r2.executionEnv.fork r2.executionEnv.codeAddr = false := by
          rw [r2Env]
          exact accNp
        have r2Run := MontgomeryWrapperBlock.gasSteps_r2 acc n np 2200 saved
          (by rw [saved_length]; omega) hN accCode accFork accHalt accNp
          (Artifact.isValidJumpDest_index 1591 (by rfl))
        let encoded := MontgomeryWrapperValue.coreLeaf r2 1024 8192 3072 n np
        have coreCall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          coreCallPath (s := {r2 with pc := 2200, stack := saved})
          (by simpa only [r2, artifactCode] using r2Code)
          (by simpa [r2, State.fork] using r2Fork)
          (run_coreCall r2 A n np tail hcap r2Code r2Halt)
          (by simpa [r2] using r2Halt) (by simpa [r2, State.fork] using r2Np)
        have coreRun := MontgomeryCoreBridge.gasSteps_coreLeaf r2 1024 8192 3072 n np 2222 saved
          hN (by decide) (by decide) (by rw [saved_length]; omega)
          r2Code r2Fork r2Halt r2Np
          (Artifact.isValidJumpDest_index 1603 (by rfl))
        have encodedEnv : encoded.executionEnv = r2.executionEnv :=
          frame_env r2 encoded (MontgomeryWrapperValue.coreLeaf_frame r2 1024 8192 3072 n np)
        have encodedCode : encoded.executionEnv.code = submissionBytecode := by
          rw [encodedEnv]
          exact r2Code
        have encodedHalt : encoded.halt = .Running := by
          exact frame_halt r2 encoded
            (MontgomeryWrapperValue.coreLeaf_frame r2 1024 8192 3072 n np) |>.trans r2Halt
        have encodedFork : encoded.fork = .Osaka := by
          simpa only [State.fork, encodedEnv] using r2Fork
        have encodedNp : Precompile.isPrecompileWithConfig encoded.executionEnv.precompileConfig
            encoded.executionEnv.fork encoded.executionEnv.codeAddr = false := by
          rw [encodedEnv]
          exact r2Np
        have baseCall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          copyBasePath (s := {encoded with pc := 2222, stack := saved})
          (by simpa only [encoded, artifactCode] using encodedCode)
          (by simpa [encoded, State.fork] using encodedFork)
          (run_copyBase encoded A n np tail hcap encodedCode encodedHalt)
          (by simpa [encoded] using encodedHalt)
          (by simpa [encoded, State.fork] using encodedNp)
        have baseRun := BigHelpers.gasSteps_copy encoded 1024 3072 n 2238 saved
          (by rw [saved_length]; omega) hbound encodedCode encodedFork encodedHalt encodedNp
          (Artifact.isValidJumpDest_index 1611 (by rfl))
        let base := MontgomerySetupBlock.flatLeaf encoded
          (BigHelpers.copyReturned encoded 1024 3072 n 0 [])
        have baseState : BigHelpers.copyReturned encoded 1024 3072 n 2238 saved =
            {base with pc := 2238, stack := saved} := by
          simpa [base] using (copyReturned_frame encoded 1024 3072 n 2238 saved)
        rw [baseState] at baseRun
        have finalCall := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          finalPath (s := {base with pc := 2238, stack := saved})
          (by simpa only [base, MontgomerySetupBlock.flatLeaf, artifactCode] using encodedCode)
          (by simpa [base, MontgomerySetupBlock.flatLeaf, State.fork] using encodedFork)
          (run_final base A n np tail hcap encodedCode encodedHalt)
          (by simpa [base, MontgomerySetupBlock.flatLeaf] using encodedHalt)
          (by simpa [base, MontgomerySetupBlock.flatLeaf, State.fork] using encodedNp)
        have path : GasSteps (setupEntry s A n tail)
            ({MontgomeryWrapperBlock.storeNpLeaf base np with
              pc := UInt256.ofNat 1343, stack := frame A n tail}) :=
          (let p0 := zero.trans large
           let p1 := p0.trans parity
           let p2 := p1.trans inverseCall
           let p3 := p2.trans inverse
           let p4 := p3.trans unitCall
           let p5 := p4.trans unitRun'
           let p6 := p5.trans copyCall
           let p7 := p6.trans copyRun
           let p8 := p7.trans r2Call
           let p9 := p8.trans r2Run
           let p10 := p9.trans coreCall
           let p11 := p10.trans coreRun
           let p12 := p11.trans baseCall
           let p13 := p12.trans baseRun
           p13.trans finalCall)
        have hprepared :
            MontgomeryWrapperBlock.eraseEffects
              (MontgomeryPrepareValue.prepare loaded n np) =
              MontgomeryWrapperBlock.eraseEffects s := by
          apply (prepare_erased loaded n np).trans
          have hframe := frame_trans s touched loaded
            (loadLow_frame s 0) (loadLow_frame touched 0)
          have h := congrArg MontgomeryWrapperBlock.eraseEffects hframe
          simpa only [MontgomeryWrapperBlock.eraseEffects] using h
        have hreturn := MontgomeryWrapperBlock.returnedState_of_erased s
          (MontgomeryPrepareValue.prepare loaded n np) 1343 (frame A n tail) hprepared.symm
        simp only [setupReturned, setupEffects,
          if_neg (show ¬(n = 0 ∨ 32 < n) by omega), if_neg heven]
        change GasSteps (setupEntry s A n tail)
          (MontgomeryWrapperBlock.returnedState s
            (MontgomeryWrapperBlock.effectsOf
              (MontgomeryPrepareValue.prepare loaded n np))
            1343 (frame A n tail))
        rw [hreturn]
        refine GasSteps.cast path rfl ?_
        simp only [MontgomeryPrepareValue.prepare, base, encoded, r2, acc, unit,
          saved, Word.literal_eq_ofNat]
