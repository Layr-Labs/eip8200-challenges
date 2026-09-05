import Challenge.EvmProof.Meter
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof

-- Frozen R2 control on the canonical2126-byte artifact. Core execution is not assumed.

def flatLeaf (s result : State) : State :=
  { s with memory := result.memory, activeWords := result.activeWords }

def r2Frame (k n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat n, np, modulus, ret] ++ saved

def r2EntryAt (pc : Nat) (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := [UInt256.ofNat n, np, modulus, ret] ++ saved }

def copyUnitLeaf (s : State) (n : Nat) : State :=
  flatLeaf s (BigHelpers.copyReturned s 0x2000 0x1c00 n 0 [])

def doubleLeaf (s : State) (modulus : UInt256) (n : Nat) : State :=
  flatLeaf s (BigHelpers.addReturned s 0x2000 0x2000 1 modulus n 0 [])

def doubleProgress (s : State) (modulus : UInt256) (n : Nat) : Nat → State
  | 0 => s
  | k + 1 => doubleLeaf (doubleProgress s modulus n k) modulus n

def r2DoubledLeaf (s : State) (modulus : UInt256) (n : Nat) : State :=
  doubleProgress (copyUnitLeaf s n) modulus n (2 * n)

theorem doubleProgress_other_fields (s : State) (modulus : UInt256) (n k : Nat) :
    { doubleProgress s modulus n k with memory := s.memory, activeWords := s.activeWords } = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [doubleProgress, doubleLeaf, flatLeaf] using ih

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

def copyUnitPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1408 .JUMPDEST,
   pushAt 1409 2 1919,
   opAt 1410 (.Dup ⟨1, by decide⟩),
   pushAt 1411 2 7168,
   pushAt 1412 2 8192,
   pushAt 1413 2 58,
   opAt 1414 .JUMP]

def doubleInitPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1415 .JUMPDEST,
   pushAt 1416 0 0]

def doubleGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1417 .JUMPDEST,
   pushAt 1418 1 2,
   opAt 1419 (.Dup ⟨2, by decide⟩),
   opAt 1420 .MUL,
   opAt 1421 (.Dup ⟨1, by decide⟩),
   opAt 1422 .LT,
   opAt 1423 .ISZERO,
   pushAt 1424 2 1958,
   opAt 1425 .JUMPI]

def doubleCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1426 2 1950,
   opAt 1427 (.Dup ⟨2, by decide⟩),
   opAt 1428 (.Dup ⟨5, by decide⟩),
   pushAt 1429 1 1,
   pushAt 1430 2 8192,
   pushAt 1431 2 8192,
   pushAt 1432 2 104,
   opAt 1433 .JUMP]

def doubleNextPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1434 .JUMPDEST,
   pushAt 1435 1 1,
   opAt 1436 .ADD,
   pushAt 1437 2 1921,
   opAt 1438 .JUMP]

def squareInitPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1439 .JUMPDEST,
   opAt 1440 .POP,
   pushAt 1441 0 0]

def squareGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1442 .JUMPDEST,
   pushAt 1443 1 7,
   opAt 1444 (.Dup ⟨1, by decide⟩),
   opAt 1445 .LT,
   opAt 1446 .ISZERO,
   pushAt 1447 2 2013,
   opAt 1448 .JUMPI]

def squareCorePath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1449 2 1990,
   opAt 1450 (.Dup ⟨3, by decide⟩),
   opAt 1451 (.Dup ⟨3, by decide⟩),
   opAt 1452 (.Dup ⟨6, by decide⟩),
   pushAt 1453 2 3072,
   pushAt 1454 2 8192,
   pushAt 1455 2 8192,
   pushAt 1456 2 1625,
   opAt 1457 .JUMP]

def squareCopyPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1458 .JUMPDEST,
   pushAt 1459 2 2005,
   opAt 1460 (.Dup ⟨2, by decide⟩),
   pushAt 1461 2 3072,
   pushAt 1462 2 8192,
   pushAt 1463 2 58,
   opAt 1464 .JUMP]

def squareNextPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1465 .JUMPDEST,
   pushAt 1466 1 1,
   opAt 1467 .ADD,
   pushAt 1468 2 1961,
   opAt 1469 .JUMP]

def r2DonePath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1470 .JUMPDEST,
   opAt 1471 .POP,
   opAt 1472 .POP,
   opAt 1473 .POP,
   opAt 1474 .POP,
   opAt 1475 .JUMP]

def r2At (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (pc : Nat) : State :=
  r2EntryAt pc s n np modulus ret saved

def loopAt (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (pc : Nat) : State :=
  { s with pc := UInt256.ofNat pc, stack := r2Frame i n np modulus ret saved }

def copyEntry (s : State) (dst src : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) : State :=
  { s with pc := 58, stack := [dst, src, UInt256.ofNat n, ret] ++ saved }

def addEntry (s : State) (dst src take modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) : State :=
  { s with pc := 104, stack := [dst, src, take, modulus, UInt256.ofNat n, ret] ++ saved }

def coreEntry (s : State) (a b out modulus : UInt256) (n : Nat) (np ret : UInt256)
    (saved : List UInt256) : State :=
  { s with pc := 1625, stack := [a, b, out, modulus, UInt256.ofNat n, np, ret] ++ saved }

@[simp] private theorem localPCs (i : Nat) (hi : 1408 ≤ i) (hii : i ≤ 1544) :
    Artifact.submissionArtifact.instructionPC i =
      [1904,1905,1908,1909,1912,1915,1918,1919,1920,1921,1922,1924,1925,1926,1927,1928,1929,1932,1933,1936,1937,1938,1940,1943,1946,1949,1950,1951,1953,1954,1957,1958,1959,1960,1961,1962,1964,1965,1966,1967,1970,1971,1974,1975,1976,1977,1980,1983,1986,1989,1990,1991,1994,1995,1998,2001,2004,2005,2006,2008,2009,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2025,2026,2028,2029,2030,2033,2034,2035,2036,2038,2039,2040,2043,2044,2047,2048,2049,2052,2053,2054,2055,2058,2059,2062,2063,2064,2067,2068,2069,2072,2073,2074,2075,2078,2079,2080,2083,2084,2085,2086,2089,2092,2093,2096,2097,2098,2101,2102,2103,2104,2105,2108,2109,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2125][i - 1408]! := by
  interval_cases i <;> decide

@[simp] private theorem copyDest :
    Decode.isValidJumpDest submissionBytecode 58 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)

@[simp] private theorem addDest :
    Decode.isValidJumpDest submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

@[simp] private theorem coreDest :
    Decode.isValidJumpDest submissionBytecode 1625 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

@[simp] private theorem pc1904Dest :
    Decode.isValidJumpDest submissionBytecode 1904 = true :=
  Artifact.isValidJumpDest_index 1408 (by rfl)

@[simp] private theorem pc1919Dest :
    Decode.isValidJumpDest submissionBytecode 1919 = true :=
  Artifact.isValidJumpDest_index 1415 (by rfl)

@[simp] private theorem pc1921Dest :
    Decode.isValidJumpDest submissionBytecode 1921 = true :=
  Artifact.isValidJumpDest_index 1417 (by rfl)

@[simp] private theorem pc1950Dest :
    Decode.isValidJumpDest submissionBytecode 1950 = true :=
  Artifact.isValidJumpDest_index 1434 (by rfl)

@[simp] private theorem pc1958Dest :
    Decode.isValidJumpDest submissionBytecode 1958 = true :=
  Artifact.isValidJumpDest_index 1439 (by rfl)

@[simp] private theorem pc1961Dest :
    Decode.isValidJumpDest submissionBytecode 1961 = true :=
  Artifact.isValidJumpDest_index 1442 (by rfl)

@[simp] private theorem pc1990Dest :
    Decode.isValidJumpDest submissionBytecode 1990 = true :=
  Artifact.isValidJumpDest_index 1458 (by rfl)

@[simp] private theorem pc2005Dest :
    Decode.isValidJumpDest submissionBytecode 2005 = true :=
  Artifact.isValidJumpDest_index 1465 (by rfl)

@[simp] private theorem pc2013Dest :
    Decode.isValidJumpDest submissionBytecode 2013 = true :=
  Artifact.isValidJumpDest_index 1470 (by rfl)

theorem run_copyUnit (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock copyUnitPath (r2At s n np modulus ret saved 1904) =
      some (copyEntry s 8192 7168 n 1919 ([UInt256.ofNat n, np, modulus, ret] ++ saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [copyUnitPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_doubleInit (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock doubleInitPath (r2At s n np modulus ret saved 1919) =
      some (loopAt s n 0 np modulus ret saved 1921) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [doubleInitPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun]
  rfl

theorem run_doubleCall (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock doubleCallPath (loopAt s n i np modulus ret saved 1933) =
      some (addEntry s 8192 8192 1 modulus n 1950 (r2Frame i n np modulus ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [doubleCallPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_doubleNext (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock doubleNextPath (loopAt s n i np modulus ret saved 1950) =
      some (loopAt s n (i+1) np modulus ret saved 1921) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [doubleNextPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, Word.word_add_comm]

theorem run_squareInit (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock squareInitPath (loopAt s n i np modulus ret saved 1958) =
      some (loopAt s n 0 np modulus ret saved 1961) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [squareInitPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun]
  rfl

theorem run_squareCore (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock squareCorePath (loopAt s n i np modulus ret saved 1971) =
      some (coreEntry s 8192 8192 3072 modulus n np 1990 (r2Frame i n np modulus ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [squareCorePath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_squareCopy (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock squareCopyPath (loopAt s n i np modulus ret saved 1990) =
      some (copyEntry s 8192 3072 n 2005 (r2Frame i n np modulus ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [squareCopyPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_squareNext (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock squareNextPath (loopAt s n i np modulus ret saved 2005) =
      some (loopAt s n (i+1) np modulus ret saved 1961) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [squareNextPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, Word.word_add_comm]

theorem run_r2Done (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    Stepper.runLocatedBlock r2DonePath (loopAt s n i np modulus ret saved 2013) =
      some { s with pc := ret, stack := saved } := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [r2DonePath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, copyEntry, addEntry, coreEntry, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hret]

private theorem twoMul (n : Nat) :
    UInt256.ofNat n * UInt256.ofNat 2 = UInt256.ofNat (2*n) := by
  apply Word.word_ext
  change ((UInt256.ofNat n).val * (UInt256.ofNat 2).val).val = _
  rw [Fin.val_mul]
  change (n % 2^256 * (2 % 2^256)) % 2^256 = (2*n) % 2^256
  rw [← Nat.mul_mod, Nat.mul_comm]

theorem run_doubleGuard (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hN : n ≤ 32) (hi : i < 2*n)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock doubleGuardPath (loopAt s n i np modulus ret saved 1921) =
      some (loopAt s n i np modulus ret saved 1933) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.isZero (UInt256.lt (UInt256.ofNat i) (UInt256.ofNat (2*n)))) := by
    simp only [UInt256.lt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^256 by omega),
      Nat.mod_eq_of_lt (show 2*n < 2^256 by omega), if_pos hi]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [doubleGuardPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, twoMul]

theorem run_doubleGuard_finish (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock doubleGuardPath (loopAt s n (2*n) np modulus ret saved 1921) =
      some (loopAt s n (2*n) np modulus ret saved 1958) := by
  have hc : UInt256.isTrue
      (UInt256.isZero (UInt256.lt (UInt256.ofNat (2*n)) (UInt256.ofNat (2*n)))) := by
    simp [UInt256.isTrue, UInt256.isZero, UInt256.lt]
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [doubleGuardPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, twoMul, hcode]

theorem run_squareGuard (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hi : i < 7)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock squareGuardPath (loopAt s n i np modulus ret saved 1961) =
      some (loopAt s n i np modulus ret saved 1971) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.isZero (UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 7))) := by
    simp only [UInt256.lt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^256 by omega)]
    norm_num [hi, UInt256.isTrue, UInt256.isZero]
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [squareGuardPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_squareGuard_finish (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock squareGuardPath (loopAt s n 7 np modulus ret saved 1961) =
      some (loopAt s n 7 np modulus ret saved 2013) := by
  have hc : UInt256.isTrue
      (UInt256.isZero (UInt256.lt (UInt256.ofNat 7) (UInt256.ofNat 7))) := by decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [squareGuardPath, opAt, pushAt, wfOp, r2At, loopAt, r2EntryAt, r2Frame, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

def gasSteps_copyUnit (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (r2At s n np modulus ret saved 1904) ((copyEntry s 8192 7168 n 1919 ([UInt256.ofNat n, np, modulus, ret] ++ saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka copyUnitPath
    hcode hfork (run_copyUnit s n np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_doubleInit (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (r2At s n np modulus ret saved 1919) ((loopAt s n 0 np modulus ret saved 1921)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka doubleInitPath
    hcode hfork (run_doubleInit s n np modulus ret saved hcap hrun) hrun hnp

def gasSteps_doubleCall (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1933) ((addEntry s 8192 8192 1 modulus n 1950 (r2Frame i n np modulus ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka doubleCallPath
    hcode hfork (run_doubleCall s n i np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_doubleNext (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1950) ((loopAt s n (i+1) np modulus ret saved 1921)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka doubleNextPath
    hcode hfork (run_doubleNext s n i np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_squareInit (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1958) ((loopAt s n 0 np modulus ret saved 1961)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka squareInitPath
    hcode hfork (run_squareInit s n i np modulus ret saved hcap hrun) hrun hnp

def gasSteps_squareCore (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1971) ((coreEntry s 8192 8192 3072 modulus n np 1990 (r2Frame i n np modulus ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka squareCorePath
    hcode hfork (run_squareCore s n i np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_squareCopy (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1990) ((copyEntry s 8192 3072 n 2005 (r2Frame i n np modulus ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka squareCopyPath
    hcode hfork (run_squareCopy s n i np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_squareNext (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 2005) ((loopAt s n (i+1) np modulus ret saved 1961)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka squareNextPath
    hcode hfork (run_squareNext s n i np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_r2Done (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 2013) ({ s with pc := ret, stack := saved }) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka r2DonePath
    hcode hfork (run_r2Done s n i np modulus ret saved hcap hcode hrun hret) hrun hnp

def gasSteps_doubleGuard (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hN : n ≤ 32) (hi : i < 2*n)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1921) ((loopAt s n i np modulus ret saved 1933)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka doubleGuardPath
    hcode hfork (run_doubleGuard s n i np modulus ret saved hcap hN hi hrun) hrun hnp

def gasSteps_doubleGuard_finish (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n (2*n) np modulus ret saved 1921) ((loopAt s n (2*n) np modulus ret saved 1958)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka doubleGuardPath
    hcode hfork (run_doubleGuard_finish s n np modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_squareGuard (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hi : i < 7)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1961) ((loopAt s n i np modulus ret saved 1971)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka squareGuardPath
    hcode hfork (run_squareGuard s n i np modulus ret saved hcap hi hrun) hrun hnp

def gasSteps_squareGuard_finish (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n 7 np modulus ret saved 1961) ((loopAt s n 7 np modulus ret saved 2013)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka squareGuardPath
    hcode hfork (run_squareGuard_finish s n np modulus ret saved hcap hcode hrun) hrun hnp

@[simp] theorem progress_env (s : State) (modulus : UInt256) (n i : Nat) :
    (doubleProgress s modulus n i).executionEnv = s.executionEnv := by
  have h := congrArg (fun t : State => t.executionEnv)
    (doubleProgress_other_fields s modulus n i)
  exact h

@[simp] theorem progress_halt (s : State) (modulus : UInt256) (n i : Nat) :
    (doubleProgress s modulus n i).halt = s.halt := by
  have h := congrArg State.halt (doubleProgress_other_fields s modulus n i)
  exact h

@[simp] theorem progress_fork (s : State) (modulus : UInt256) (n i : Nat) :
    (doubleProgress s modulus n i).fork = s.fork := by
  simp [State.fork]

def doubleLoop (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) : State :=
  loopAt (doubleProgress s modulus n i) n i np modulus ret saved 1921

def gasSteps_copyHelper (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (copyEntry s 8192 7168 n 1919 ([UInt256.ofNat n, np, modulus, ret] ++ saved))
      (r2At (copyUnitLeaf s n) n np modulus ret saved 1919) := by
  exact BigHelpers.gasSteps_copy s 8192 7168 n 1919
    ([UInt256.ofNat n, np, modulus, ret] ++ saved)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hcode hfork hrun hnp
    (Artifact.isValidJumpDest_index 1415 (by rfl))

def gasSteps_doubleHelper (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (addEntry s 8192 8192 1 modulus n 1950 (r2Frame i n np modulus ret saved))
      (loopAt (doubleLeaf s modulus n) n i np modulus ret saved 1950) := by
  exact BigHelpers.gasSteps_addMaskedMod s 8192 8192 1 modulus n 1950
    (r2Frame i n np modulus ret saved)
    (by simp only [r2Frame, List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hcode hfork hrun hnp
    (Artifact.isValidJumpDest_index 1434 (by rfl))

def gasSteps_doubleIteration (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32) (hi : i < 2*n)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (doubleLoop s n i np modulus ret saved)
      (doubleLoop s n (i+1) np modulus ret saved) := by
  let p := doubleProgress s modulus n i
  have hc : p.executionEnv.code = submissionBytecode := by simpa [p] using hcode
  have hf : p.fork = .Osaka := by simpa [p] using hfork
  have hr : p.halt = .Running := by simpa [p] using hrun
  have hp : Precompile.isPrecompileWithConfig p.executionEnv.precompileConfig
      p.executionEnv.fork p.executionEnv.codeAddr = false := by simpa [p] using hnp
  exact (gasSteps_doubleGuard p n i np modulus ret saved (by omega) hN hi hr hc hf hp).trans <|
    (gasSteps_doubleCall p n i np modulus ret saved (by omega) hc hr hf hp).trans <|
    (gasSteps_doubleHelper p n i np modulus ret saved hcap hN hc hf hr hp).trans
      (gasSteps_doubleNext (doubleLeaf p modulus n) n i np modulus ret saved
        (by omega) hc hr hf hp)

def gasSteps_doublesToSquares (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (r2At s n np modulus ret saved 1919)
      (loopAt (doubleProgress s modulus n (2*n)) n 0 np modulus ret saved 1961) := by
  let p := doubleProgress s modulus n (2*n)
  have hc : p.executionEnv.code = submissionBytecode := by simpa [p] using hcode
  have hf : p.fork = .Osaka := by simpa [p] using hfork
  have hr : p.halt = .Running := by simpa [p] using hrun
  have hp : Precompile.isPrecompileWithConfig p.executionEnv.precompileConfig
      p.executionEnv.fork p.executionEnv.codeAddr = false := by simpa [p] using hnp
  exact (gasSteps_doubleInit s n np modulus ret saved (by omega) hrun hcode hfork hnp).trans <|
    (GasSteps.iterateBounded (2*n) (fun i hi =>
      gasSteps_doubleIteration s n i np modulus ret saved hcap hN hi
        hcode hfork hrun hnp)).trans <|
    (gasSteps_doubleGuard_finish p n np modulus ret saved (by omega) hc hr hf hp).trans
      (gasSteps_squareInit p n (2*n) np modulus ret saved (by omega) hr hc hf hp)

def gasSteps_r2DoublesToSquares (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (r2At s n np modulus ret saved 1904)
      (loopAt (r2DoubledLeaf s modulus n) n 0 np modulus ret saved 1961) :=
  (gasSteps_copyUnit s n np modulus ret saved (by omega) hcode hrun hfork hnp).trans <|
  (gasSteps_copyHelper s n np modulus ret saved hcap hN hcode hfork hrun hnp).trans
    (gasSteps_doublesToSquares (copyUnitLeaf s n) n np modulus ret saved hcap hN
      hcode hfork hrun hnp)

def squareCopyLeaf (s : State) (n : Nat) : State :=
  flatLeaf s (BigHelpers.copyReturned s 8192 3072 n 0 [])

def gasSteps_squareToCore (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hi : i < 7)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1961)
      (coreEntry s 8192 8192 3072 modulus n np 1990 (r2Frame i n np modulus ret saved)) :=
  (gasSteps_squareGuard s n i np modulus ret saved (by omega) hi hrun hcode hfork hnp).trans
    (gasSteps_squareCore s n i np modulus ret saved (by omega) hcode hrun hfork hnp)

def gasSteps_squareResume (s : State) (n i : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np modulus ret saved 1990)
      (loopAt (squareCopyLeaf s n) n (i+1) np modulus ret saved 1961) := by
  have copy : GasSteps (copyEntry s 8192 3072 n 2005 (r2Frame i n np modulus ret saved))
      (loopAt (squareCopyLeaf s n) n i np modulus ret saved 2005) :=
    BigHelpers.gasSteps_copy s 8192 3072 n 2005 (r2Frame i n np modulus ret saved)
      (by simp only [r2Frame, List.length_append, List.length_cons, List.length_nil]; omega)
      (by omega) hcode hfork hrun hnp
      (Artifact.isValidJumpDest_index 1465 (by rfl))
  exact (gasSteps_squareCopy s n i np modulus ret saved (by omega) hcode hrun hfork hnp).trans <|
    copy.trans (gasSteps_squareNext (squareCopyLeaf s n) n i np modulus ret saved
      (by omega) hcode hrun hfork hnp)

def gasSteps_squareExit (s : State) (n : Nat) (np modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n 7 np modulus ret saved 1961) { s with pc := ret, stack := saved } :=
  (gasSteps_squareGuard_finish s n np modulus ret saved (by omega) hcode hrun hfork hnp).trans
    (gasSteps_r2Done s n 7 np modulus ret saved (by omega) hcode hrun hret hfork hnp)

theorem squareCopy_represents (s : State) (n value : Nat) (hN : n ≤ 32)
    (hwork : Limbs.Represents s.memory 3072 n value) :
    Limbs.Represents (squareCopyLeaf s n).memory 8192 n value :=
  BigHelpers.copyMemory_represents s.memory 8192 3072 n value hwork
    (by omega) (by omega) (Or.inr (by omega))

theorem squareCopy_preserves_low (s : State) (n p value : Nat) (hN : n ≤ 32)
    (hp : p + 32*n ≤ 3072) (hrep : Limbs.Represents s.memory p n value) :
    Limbs.Represents (squareCopyLeaf s n).memory p n value :=
  BigHelpers.represents_copyMemory_disjoint_region s.memory 8192 3072 p n value
    (by omega) (Or.inr (by omega)) hrep

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock
