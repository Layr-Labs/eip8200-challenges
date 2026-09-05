import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInverseBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreBridge
import Challenge.Modexp.Submission.Proofs.Bytecode.BigMul

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open MontgomerySetupBlock
open Challenge.Modexp.Submission.Proofs.Montgomery

-- Frozen wrapper control. Fallback starts from the actual touched state.

structure Effects where
  memory : ByteArray
  activeWords : UInt256

def effectsOf (s : State) : Effects := ⟨s.memory, s.activeWords⟩

def returnedState (s : State) (effects : Effects) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := ret
    stack := rest
    memory := effects.memory
    activeWords := effects.activeWords }

def oldFrame (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [a, b, out, modulus, UInt256.ofNat n, ret] ++ rest

def wrapperFrame (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  np :: oldFrame a b out modulus n ret rest

def wrapperEntryAt (pc : Nat) (s : State) (a b out modulus : UInt256)
    (n : Nat) (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := oldFrame a b out modulus n ret rest }

def loadLowLeaf (s : State) (modulus : UInt256) : State :=
  { s with
    activeWords := UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat modulus.toNat 32) }

def storeNpLeaf (s : State) (np : UInt256) : State :=
  { s with
    memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded np.toNat 32) 0x2c00
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0x2c00 32) }

def inverseSetupLeaf (s : State) (modulus : UInt256) : State :=
  let loaded := loadLowLeaf (loadLowLeaf s modulus) modulus
  let low := MachineState.readWord loaded.memory modulus.toNat
  let inverted := MontgomeryInverseBlock.inverseReturned loaded low 0 []
  storeNpLeaf (flatLeaf loaded inverted)
    (Challenge.Modexp.Submission.Proofs.Montgomery.InverseArithmetic.nprime low)

theorem inverseSetupLeaf_np (s : State) (modulus : UInt256) :
    MachineState.readWord (inverseSetupLeaf s modulus).memory 0x2c00 =
      Challenge.Modexp.Submission.Proofs.Montgomery.InverseArithmetic.nprime
        (MachineState.readWord s.memory modulus.toNat) := by
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem inverseSetupLeaf_congruence (s : State) (modulus : UInt256)
    (hodd : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 1) :
    ((MachineState.readWord s.memory modulus.toNat).toNat *
      (MachineState.readWord (inverseSetupLeaf s modulus).memory 0x2c00).toNat + 1) % (2^256) = 0 := by
  rw [inverseSetupLeaf_np]
  exact Challenge.Modexp.Submission.Proofs.Montgomery.InverseArithmetic.nprime_correct _ hodd

theorem inverseSetupLeaf_preserves_padded (s : State) (modulus : UInt256)
    (start size : Nat) (hdisjoint : start + size ≤ 0x2c00 ∨ 0x2c00 + 32 ≤ start) :
    MachineState.readPadded (inverseSetupLeaf s modulus).memory start size =
      MachineState.readPadded s.memory start size := by
  apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
  simpa [Data.Bytes.natToBytesPadded, ByteArray.size] using hdisjoint

def fallbackEffects (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) : Effects :=
  let copied := BigMul.mulAfterCopy s a b out modulus n ret rest
  let progress := BigMul.mulOuterProgress copied a b out modulus n ret rest n
  effectsOf (BigMul.mulReturned progress ret rest)

def eraseEffects (s : State) : State :=
  { s with pc := 0, stack := [], memory := ByteArray.empty, activeWords := 0 }

theorem oldWordProgress_erased (s : State) (word a b out modulus : UInt256)
    (n i j : Nat) (ret : UInt256) (rest : List UInt256) :
    eraseEffects (BigMul.mulWordProgress s word a b out modulus n i ret rest j) =
      eraseEffects s := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change eraseEffects (BigMul.mulWordProgress s word a b out modulus n i ret rest j) = _
      exact ih

theorem oldOuterProgress_erased (s : State) (a b out modulus : UInt256)
    (n i : Nat) (ret : UInt256) (rest : List UInt256) :
    eraseEffects (BigMul.mulOuterProgress s a b out modulus n ret rest i) = eraseEffects s := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [BigMul.mulOuterProgress, oldWordProgress_erased]
      exact ih

theorem returnedState_of_erased (s t : State) (ret : UInt256) (rest : List UInt256)
    (h : eraseEffects s = eraseEffects t) :
    returnedState s (effectsOf t) ret rest = { t with pc := ret, stack := rest } := by
  have hgas := congrArg (fun s : State => s.gasAvailable) h
  have hdata := congrArg (fun s : State => s.returnData) h
  have hreturn := congrArg (fun s : State => s.hReturn) h
  have hacct := congrArg (fun s : State => s.accountMap) h
  have hsub := congrArg (fun s : State => s.substate) h
  have henv := congrArg (fun s : State => s.executionEnv) h
  have hlen := congrArg State.execLength h
  have hhalt := congrArg State.halt h
  have hcalls := congrArg State.callStack h
  simp only [eraseEffects] at hgas hdata hreturn hacct hsub henv hlen hhalt hcalls
  cases s
  cases t
  simp_all [returnedState, effectsOf]

theorem fallbackEffects_actual_return (s : State) (a b out modulus : UInt256)
    (n : Nat) (ret : UInt256) (rest : List UInt256) :
    let copied := BigMul.mulAfterCopy s a b out modulus n ret rest
    let progress := BigMul.mulOuterProgress copied a b out modulus n ret rest n
    returnedState s (fallbackEffects s a b out modulus n ret rest) ret rest =
      BigMul.mulReturned progress ret rest := by
  dsimp only [fallbackEffects]
  apply returnedState_of_erased
  symm
  exact oldOuterProgress_erased _ a b out modulus n n ret rest

theorem returnedState_pc (s : State) (e : Effects) (ret : UInt256) (rest : List UInt256) :
    (returnedState s e ret rest).pc = ret := rfl

theorem returnedState_stack (s : State) (e : Effects) (ret : UInt256) (rest : List UInt256) :
    (returnedState s e ret rest).stack = rest := rfl

theorem returnedState_other_fields (s : State) (e : Effects) (ret : UInt256)
    (rest : List UInt256) :
    { returnedState s e ret rest with
      pc := s.pc
      stack := s.stack
      memory := s.memory
      activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem wrapperFrame_length (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) :
    (wrapperFrame np a b out modulus n ret rest).length = rest.length + 7 := by
  simp [wrapperFrame, oldFrame]

theorem r2_core_helper_cap (np a b out modulus ret r2ret : UInt256)
    (n k : Nat) (rest : List UInt256) (hcap : rest.length < 980) :
    (r2Frame k n np modulus r2ret
      (wrapperFrame np a b out modulus n ret rest)).length + 8 < 1000 := by
  simp only [r2Frame, List.length_append, List.length_cons, List.length_nil,
    wrapperFrame_length]
  omega

theorem r2_double_helper_cap (np a b out modulus ret r2ret : UInt256)
    (n k : Nat) (rest : List UInt256) (hcap : rest.length < 980) :
    (r2Frame k n np modulus r2ret
      (wrapperFrame np a b out modulus n ret rest)).length < 1000 := by
  have := r2_core_helper_cap np a b out modulus ret r2ret n k rest hcap
  omega

theorem unit_saved_cap (np a b out modulus ret : UInt256) (n : Nat)
    (rest : List UInt256) (hcap : rest.length < 980) :
    (wrapperFrame np a b out modulus n ret rest).length < 996 := by
  rw [wrapperFrame_length]
  omega

theorem fixed_regions (n : Nat) (hn : n ≤ 32) :
    32 * n ≤ 1024 ∧ 1024 + 32 * n ≤ 2048 ∧ 2048 + 32 * n ≤ 3072 ∧
    3072 + 32 * n ≤ 4096 ∧ 5120 + 32 * n ≤ 7168 ∧
    7168 + 32 * n ≤ 8192 ∧ 8192 + 32 * n ≤ 9216 ∧
    9216 + 32 * (n + 2) ≤ 11264 := by omega

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
  [opAt 1476 .JUMPDEST,
   opAt 1477 (.Dup ⟨4, by decide⟩),
   opAt 1478 .ISZERO,
   pushAt 1479 2 2121,
   opAt 1480 .JUMPI]

def largeGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1481 1 32,
   opAt 1482 (.Dup ⟨5, by decide⟩),
   opAt 1483 .GT,
   pushAt 1484 2 2121,
   opAt 1485 .JUMPI]

def parityGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1486 (.Dup ⟨3, by decide⟩),
   opAt 1487 .MLOAD,
   pushAt 1488 1 1,
   opAt 1489 .AND,
   opAt 1490 .ISZERO,
   pushAt 1491 2 2121,
   opAt 1492 .JUMPI]

def inverseCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1493 2 2053,
   opAt 1494 (.Dup ⟨4, by decide⟩),
   opAt 1495 .MLOAD,
   pushAt 1496 2 1447,
   opAt 1497 .JUMP]

def unitCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1498 .JUMPDEST,
   opAt 1499 (.Dup ⟨0, by decide⟩),
   pushAt 1500 2 11264,
   opAt 1501 .MSTORE,
   pushAt 1502 2 2068,
   opAt 1503 (.Dup ⟨5, by decide⟩),
   opAt 1504 (.Dup ⟨7, by decide⟩),
   pushAt 1505 2 1786,
   opAt 1506 .JUMP]

def r2CallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1507 .JUMPDEST,
   pushAt 1508 2 2079,
   opAt 1509 (.Dup ⟨5, by decide⟩),
   opAt 1510 (.Dup ⟨2, by decide⟩),
   opAt 1511 (.Dup ⟨8, by decide⟩),
   pushAt 1512 2 1904,
   opAt 1513 .JUMP]

def encodeCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1514 .JUMPDEST,
   pushAt 1515 2 2097,
   opAt 1516 (.Dup ⟨1, by decide⟩),
   opAt 1517 (.Dup ⟨7, by decide⟩),
   opAt 1518 (.Dup ⟨7, by decide⟩),
   pushAt 1519 2 7168,
   pushAt 1520 2 8192,
   opAt 1521 (.Dup ⟨7, by decide⟩),
   pushAt 1522 2 1625,
   opAt 1523 .JUMP]

def productCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1524 .JUMPDEST,
   pushAt 1525 2 2113,
   opAt 1526 (.Dup ⟨1, by decide⟩),
   opAt 1527 (.Dup ⟨7, by decide⟩),
   opAt 1528 (.Dup ⟨7, by decide⟩),
   opAt 1529 (.Dup ⟨7, by decide⟩),
   pushAt 1530 2 7168,
   opAt 1531 (.Dup ⟨8, by decide⟩),
   pushAt 1532 2 1625,
   opAt 1533 .JUMP]

def wrapperDonePath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1534 .JUMPDEST,
   opAt 1535 .POP,
   opAt 1536 .POP,
   opAt 1537 .POP,
   opAt 1538 .POP,
   opAt 1539 .POP,
   opAt 1540 .POP,
   opAt 1541 .JUMP]

def fallbackPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1542 .JUMPDEST,
   pushAt 1543 2 310,
   opAt 1544 .JUMP]

def oldAt (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (pc : Nat) : State :=
  wrapperEntryAt pc s a b out modulus n ret rest

def wrapperAt (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (pc : Nat) : State :=
  { s with pc := UInt256.ofNat pc, stack := wrapperFrame np a b out modulus n ret rest }

def unitEntry (s : State) (n : Nat) (modulus ret : UInt256)
    (saved : List UInt256) : State :=
  { s with pc := 1786, stack := [UInt256.ofNat n, modulus, ret] ++ saved }

def inverseEntry (s : State) (low ret : UInt256) (saved : List UInt256) : State :=
  { s with pc := 1447, stack := [low, ret] ++ saved }

set_option linter.unusedSimpArgs false

@[simp] private theorem localPCs (i : Nat) (hi : 1408 ≤ i) (hii : i ≤ 1544) :
    Artifact.submissionArtifact.instructionPC i =
      [1904,1905,1908,1909,1912,1915,1918,1919,1920,1921,1922,1924,1925,1926,1927,1928,1929,1932,1933,1936,1937,1938,1940,1943,1946,1949,1950,1951,1953,1954,1957,1958,1959,1960,1961,1962,1964,1965,1966,1967,1970,1971,1974,1975,1976,1977,1980,1983,1986,1989,1990,1991,1994,1995,1998,2001,2004,2005,2006,2008,2009,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2025,2026,2028,2029,2030,2033,2034,2035,2036,2038,2039,2040,2043,2044,2047,2048,2049,2052,2053,2054,2055,2058,2059,2062,2063,2064,2067,2068,2069,2072,2073,2074,2075,2078,2079,2080,2083,2084,2085,2086,2089,2092,2093,2096,2097,2098,2101,2102,2103,2104,2105,2108,2109,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2125][i - 1408]! := by
  interval_cases i <;> decide

@[simp] private theorem legacyDest :
    Decode.isValidJumpDest submissionBytecode 310 = true :=
  Artifact.isValidJumpDest_index 265 (by rfl)

@[simp] private theorem inverseDest :
    Decode.isValidJumpDest submissionBytecode 1447 = true :=
  Artifact.isValidJumpDest_index 1072 (by rfl)

@[simp] private theorem coreDest :
    Decode.isValidJumpDest submissionBytecode 1625 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

@[simp] private theorem unitDest :
    Decode.isValidJumpDest submissionBytecode 1786 = true :=
  Artifact.isValidJumpDest_index 1331 (by rfl)

@[simp] private theorem pc1904Dest :
    Decode.isValidJumpDest submissionBytecode 1904 = true :=
  Artifact.isValidJumpDest_index 1408 (by rfl)

@[simp] private theorem pc2019Dest :
    Decode.isValidJumpDest submissionBytecode 2019 = true :=
  Artifact.isValidJumpDest_index 1476 (by rfl)

@[simp] private theorem pc2053Dest :
    Decode.isValidJumpDest submissionBytecode 2053 = true :=
  Artifact.isValidJumpDest_index 1498 (by rfl)

@[simp] private theorem pc2068Dest :
    Decode.isValidJumpDest submissionBytecode 2068 = true :=
  Artifact.isValidJumpDest_index 1507 (by rfl)

@[simp] private theorem pc2079Dest :
    Decode.isValidJumpDest submissionBytecode 2079 = true :=
  Artifact.isValidJumpDest_index 1514 (by rfl)

@[simp] private theorem pc2097Dest :
    Decode.isValidJumpDest submissionBytecode 2097 = true :=
  Artifact.isValidJumpDest_index 1524 (by rfl)

@[simp] private theorem pc2113Dest :
    Decode.isValidJumpDest submissionBytecode 2113 = true :=
  Artifact.isValidJumpDest_index 1534 (by rfl)

@[simp] private theorem pc2121Dest :
    Decode.isValidJumpDest submissionBytecode 2121 = true :=
  Artifact.isValidJumpDest_index 1542 (by rfl)

private theorem lowBit (w : UInt256) :
    (UInt256.land (UInt256.ofNat 1) w).toNat = w.toNat % 2 := by
  rw [Word.word_toNat_land, Word.word_toNat_ofNat]
  change 1 &&& w.toNat = w.toNat % 2
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem run_unitCall (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock unitCallPath (wrapperAt s np a b out modulus n ret saved 2053) =
      some (unitEntry (storeNpLeaf s np) n modulus 2068
        (wrapperFrame np a b out modulus n ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [unitCallPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, storeNpLeaf, State.activeWordsAfterUInt256]

theorem run_r2Call (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock r2CallPath (wrapperAt s np a b out modulus n ret saved 2068) =
      some (r2At s n np modulus 2079 (wrapperFrame np a b out modulus n ret saved) 1904) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [r2CallPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_encodeCall (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock encodeCallPath (wrapperAt s np a b out modulus n ret saved 2079) =
      some (coreEntry s a 8192 7168 modulus n np 2097
        (wrapperFrame np a b out modulus n ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [encodeCallPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_productCall (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock productCallPath (wrapperAt s np a b out modulus n ret saved 2097) =
      some (coreEntry s b 7168 out modulus n np 2113
        (wrapperFrame np a b out modulus n ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [productCallPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_wrapperDone (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    Stepper.runLocatedBlock wrapperDonePath (wrapperAt s np a b out modulus n ret saved 2113) =
      some { s with pc := ret, stack := saved } := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [wrapperDonePath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hret]

theorem run_fallback (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fallbackPath (oldAt s a b out modulus n ret saved 2121) =
      some (oldAt s a b out modulus n ret saved 310) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [fallbackPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

theorem run_inverseCall (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock inverseCallPath (oldAt s a b out modulus n ret saved 2044) =
      some (inverseEntry (loadLowLeaf s modulus)
        (MachineState.readWord s.memory modulus.toNat) 2053
        (oldFrame a b out modulus n ret saved)) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [inverseCallPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, copyEntry, addEntry, coreEntry, unitEntry, inverseEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_zeroPass (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hn : 1 ≤ n) (hbound : n < 2^256)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath (oldAt s a b out modulus n ret saved 2019) =
      some (oldAt s a b out modulus n ret saved 2026) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero (UInt256.ofNat n)) := by
    simp only [UInt256.isZero, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound,
      if_neg (show n ≠ 0 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [zeroGuardPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, loadLowLeaf, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_zeroFallback (s : State) (a b out modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath (oldAt s a b out modulus 0 ret saved 2019) =
      some (oldAt s a b out modulus 0 ret saved 2121) := by
  have hc : UInt256.isTrue (UInt256.isZero (UInt256.ofNat 0)) := by decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [zeroGuardPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, loadLowLeaf, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_largePass (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hN : n ≤ 32)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath (oldAt s a b out modulus n ret saved 2026) =
      some (oldAt s a b out modulus n ret saved 2034) := by
  have hc : ¬ UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (show n < 2^256 by omega),
      Nat.mod_eq_of_lt (show 32 < 2^256 by decide), if_neg (show ¬ n > 32 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, loadLowLeaf, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_largeFallback (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hlarge : 32 < n) (hbound : n < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath (oldAt s a b out modulus n ret saved 2026) =
      some (oldAt s a b out modulus n ret saved 2121) := by
  have hc : UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (show 32 < 2^256 by decide), if_pos hlarge]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, loadLowLeaf, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_parityOdd (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hodd : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 1)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath (oldAt s a b out modulus n ret saved 2034) =
      some (oldAt (loadLowLeaf s modulus) a b out modulus n ret saved 2044) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory modulus.toNat))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, hodd]
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, loadLowLeaf, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_parityEven (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (heven : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath (oldAt s a b out modulus n ret saved 2034) =
      some (oldAt (loadLowLeaf s modulus) a b out modulus n ret saved 2121) := by
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory modulus.toNat))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, heven]
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, r2At, loopAt, oldAt, wrapperAt,
    r2EntryAt, wrapperEntryAt,
    oldFrame, wrapperFrame, r2Frame, loadLowLeaf, State.activeWordsAfterUInt256,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

def gasSteps_unitCall (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (wrapperAt s np a b out modulus n ret saved 2053) ((unitEntry (storeNpLeaf s np) n modulus 2068
        (wrapperFrame np a b out modulus n ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka unitCallPath
    hcode hfork (run_unitCall s np a b out modulus n ret saved hcap hcode hrun) hrun hnp

def gasSteps_r2Call (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (wrapperAt s np a b out modulus n ret saved 2068) ((r2At s n np modulus 2079 (wrapperFrame np a b out modulus n ret saved) 1904)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka r2CallPath
    hcode hfork (run_r2Call s np a b out modulus n ret saved hcap hcode hrun) hrun hnp

def gasSteps_encodeCall (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (wrapperAt s np a b out modulus n ret saved 2079) ((coreEntry s a 8192 7168 modulus n np 2097
        (wrapperFrame np a b out modulus n ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka encodeCallPath
    hcode hfork (run_encodeCall s np a b out modulus n ret saved hcap hcode hrun) hrun hnp

def gasSteps_productCall (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (wrapperAt s np a b out modulus n ret saved 2097) ((coreEntry s b 7168 out modulus n np 2113
        (wrapperFrame np a b out modulus n ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka productCallPath
    hcode hfork (run_productCall s np a b out modulus n ret saved hcap hcode hrun) hrun hnp

def gasSteps_wrapperDone (s : State) (np a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (wrapperAt s np a b out modulus n ret saved 2113) ({ s with pc := ret, stack := saved }) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka wrapperDonePath
    hcode hfork (run_wrapperDone s np a b out modulus n ret saved hcap hcode hrun hret) hrun hnp

def gasSteps_fallback (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2121) ((oldAt s a b out modulus n ret saved 310)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka fallbackPath
    hcode hfork (run_fallback s a b out modulus n ret saved hcap hcode hrun) hrun hnp

def gasSteps_inverseCall (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2044) ((inverseEntry (loadLowLeaf s modulus)
        (MachineState.readWord s.memory modulus.toNat) 2053
        (oldFrame a b out modulus n ret saved))) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka inverseCallPath
    hcode hfork (run_inverseCall s a b out modulus n ret saved hcap hcode hrun) hrun hnp

def gasSteps_zeroPass (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hn : 1 ≤ n) (hbound : n < 2^256)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2019) ((oldAt s a b out modulus n ret saved 2026)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka zeroGuardPath
    hcode hfork (run_zeroPass s a b out modulus n ret saved hcap hn hbound hrun) hrun hnp

def gasSteps_zeroFallback (s : State) (a b out modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus 0 ret saved 2019) ((oldAt s a b out modulus 0 ret saved 2121)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka zeroGuardPath
    hcode hfork (run_zeroFallback s a b out modulus ret saved hcap hcode hrun) hrun hnp

def gasSteps_largePass (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hN : n ≤ 32)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2026) ((oldAt s a b out modulus n ret saved 2034)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka largeGuardPath
    hcode hfork (run_largePass s a b out modulus n ret saved hcap hN hrun) hrun hnp

def gasSteps_largeFallback (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hlarge : 32 < n) (hbound : n < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2026) ((oldAt s a b out modulus n ret saved 2121)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka largeGuardPath
    hcode hfork (run_largeFallback s a b out modulus n ret saved hcap hlarge hbound hcode hrun) hrun hnp

def gasSteps_parityOdd (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hodd : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 1)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2034) ((oldAt (loadLowLeaf s modulus) a b out modulus n ret saved 2044)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka parityGuardPath
    hcode hfork (run_parityOdd s a b out modulus n ret saved hcap hodd hrun) hrun hnp

def gasSteps_parityEven (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (heven : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2034) ((oldAt (loadLowLeaf s modulus) a b out modulus n ret saved 2121)) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka parityGuardPath
    hcode hfork (run_parityEven s a b out modulus n ret saved hcap heven hcode hrun) hrun hnp

def evenFallbackEffects (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) : Effects :=
  fallbackEffects (loadLowLeaf s modulus) a b out modulus n ret saved

theorem evenFallbackEffects_actual_return (s : State) (a b out modulus : UInt256)
    (n : Nat) (ret : UInt256) (saved : List UInt256) :
    let touched := loadLowLeaf s modulus
    let copied := Challenge.Modexp.Submission.Proofs.Bytecode.BigMul.mulAfterCopy
      touched a b out modulus n ret saved
    let progress := Challenge.Modexp.Submission.Proofs.Bytecode.BigMul.mulOuterProgress
      copied a b out modulus n ret saved n
    returnedState s (evenFallbackEffects s a b out modulus n ret saved)
      ret saved =
      Challenge.Modexp.Submission.Proofs.Bytecode.BigMul.mulReturned progress ret saved := by
  exact fallbackEffects_actual_return
    (loadLowLeaf s modulus) a b out modulus n ret saved

theorem storeNpLeaf_words (s : State) (np : UInt256) :
    (storeNpLeaf s np).activeWords =
      UInt256.ofNat (max s.activeWords.toNat 353) := by
  simp [storeNpLeaf, MachineState.activeWordsAfter]

def gasSteps_zeroTail (s : State) (a b out modulus ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus 0 ret saved 2019)
      (oldAt s a b out modulus 0 ret saved 310) :=
  (gasSteps_zeroFallback s a b out modulus ret saved hcap hcode hrun hfork hnp).trans
    (gasSteps_fallback s a b out modulus 0 ret saved hcap hcode hrun hfork hnp)

def gasSteps_largeTail (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hlarge : 32 < n) (hbound : n < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2019)
      (oldAt s a b out modulus n ret saved 310) :=
  (gasSteps_zeroPass s a b out modulus n ret saved hcap (by omega) hbound
    hrun hcode hfork hnp).trans <|
  (gasSteps_largeFallback s a b out modulus n ret saved hcap hlarge hbound
    hcode hrun hfork hnp).trans
    (gasSteps_fallback s a b out modulus n ret saved hcap hcode hrun hfork hnp)

def gasSteps_evenTail (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980) (hn : 1 ≤ n) (hN : n ≤ 32)
    (heven : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2019)
      (oldAt (loadLowLeaf s modulus) a b out modulus n ret saved 310) :=
  (gasSteps_zeroPass s a b out modulus n ret saved hcap hn (by omega)
    hrun hcode hfork hnp).trans <|
  (gasSteps_largePass s a b out modulus n ret saved hcap hN hrun hcode hfork hnp).trans <|
  (gasSteps_parityEven s a b out modulus n ret saved hcap heven hcode hrun hfork hnp).trans
    (gasSteps_fallback (loadLowLeaf s modulus) a b out modulus n ret saved hcap
      hcode hrun hfork hnp)

def gasSteps_toInverse (s : State) (a b out modulus : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hodd : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 1)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret saved 2019)
      (inverseEntry (loadLowLeaf (loadLowLeaf s modulus) modulus)
        (MachineState.readWord s.memory modulus.toNat) 2053
        (oldFrame a b out modulus n ret saved)) :=
  (gasSteps_zeroPass s a b out modulus n ret saved hcap hn (by omega)
    hrun hcode hfork hnp).trans <|
  (gasSteps_largePass s a b out modulus n ret saved hcap hN hrun hcode hfork hnp).trans <|
  (gasSteps_parityOdd s a b out modulus n ret saved hcap hodd hrun hcode hfork hnp).trans
    (gasSteps_inverseCall (loadLowLeaf s modulus) a b out modulus n ret saved hcap
      hcode hrun hfork hnp)

def gasSteps_inverseHelper (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (inverseEntry s (MachineState.readWord s.memory modulus.toNat)
        2053 (oldFrame a b out modulus n ret rest))
      (wrapperAt s (InverseArithmetic.nprime (MachineState.readWord s.memory modulus.toNat))
        a b out modulus n ret rest 2053) :=
  MontgomeryInverseBlock.gasSteps_inverse s (MachineState.readWord s.memory modulus.toNat)
    2053 (oldFrame a b out modulus n ret rest)
    (by simp only [oldFrame, List.length_append, List.length_cons, List.length_nil]; omega)
    hcode hfork (Artifact.isValidJumpDest_index 1498 (by rfl)) hrun hnp

def gasSteps_toUnit (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hn : 1 ≤ n) (hN : n ≤ 32)
    (hodd : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 1)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out modulus n ret rest 2019)
      (unitEntry (inverseSetupLeaf s modulus) n modulus 2068
        (wrapperFrame (InverseArithmetic.nprime (MachineState.readWord s.memory modulus.toNat))
          a b out modulus n ret rest)) := by
  let loaded := loadLowLeaf (loadLowLeaf s modulus) modulus
  exact (gasSteps_toInverse s a b out modulus n ret rest hcap hn hN
    hodd hcode hrun hfork hnp).trans <|
    (gasSteps_inverseHelper loaded a b out modulus n ret rest hcap hcode hfork hrun hnp).trans
      (gasSteps_unitCall loaded
        (InverseArithmetic.nprime (MachineState.readWord s.memory modulus.toNat))
        a b out modulus n ret rest hcap hcode hrun hfork hnp)

theorem setup_frame (s : State) (modulus : UInt256) :
    { inverseSetupLeaf s modulus with
      memory := s.memory, activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem setup_words_zero (s : State) :
    (inverseSetupLeaf s 0).activeWords =
      UInt256.ofNat (max s.activeWords.toNat 353) := by
  have touch (t : State) :
      (loadLowLeaf t 0).activeWords.toNat = max t.activeWords.toNat 1 := by
    change (max t.activeWords.toNat 1) % 2^256 = max t.activeWords.toNat 1
    exact Nat.mod_eq_of_lt (max_lt t.activeWords.val.isLt (by decide))
  change (storeNpLeaf (loadLowLeaf (loadLowLeaf s 0) 0)
    (InverseArithmetic.nprime (MachineState.readWord s.memory 0))).activeWords = _
  rw [storeNpLeaf_words, touch, touch]
  simp [Nat.max_assoc]

theorem setup_np_correct (s : State) (modulus : UInt256)
    (hodd : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 1) :
    ((MachineState.readWord s.memory modulus.toNat).toNat *
      (MachineState.readWord (inverseSetupLeaf s modulus).memory 11264).toNat + 1) %
        (2^256) = 0 :=
  inverseSetupLeaf_congruence s modulus hodd

theorem setup_preserves_low (s : State) (modulus : UInt256) (p size : Nat)
    (hlow : p + size ≤ 3072) :
    MachineState.readPadded (inverseSetupLeaf s modulus).memory p size =
      MachineState.readPadded s.memory p size :=
  inverseSetupLeaf_preserves_padded s modulus p size (Or.inl (by omega))


def unitSetupLeaf (s : State) (n : Nat) : State :=
  flatLeaf s (MontgomeryOneBlock.returned s n 0 [])

private theorem inverse_env (s : State) :
    (inverseSetupLeaf s 0).executionEnv = s.executionEnv := rfl

private theorem inverse_halt (s : State) :
    (inverseSetupLeaf s 0).halt = s.halt := rfl

private theorem unit_env (s : State) (n : Nat) :
    (unitSetupLeaf s n).executionEnv = s.executionEnv := rfl

private theorem unit_halt (s : State) (n : Nat) :
    (unitSetupLeaf s n).halt = s.halt := rfl

/-- The accepted UNIT body, at the actual saved wrapper frame. -/
def gasSteps_unitHelper (s : State) (np a b out : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hn : 1 ≤ n) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (unitEntry s n 0 2068 (wrapperFrame np a b out 0 n ret rest))
      (wrapperAt (unitSetupLeaf s n) np a b out 0 n ret rest 2068) :=
  MontgomeryOneBlock.gasSteps_unit s n 2068 (wrapperFrame np a b out 0 n ret rest)
    (unit_saved_cap np a b out 0 ret n rest hcap) hn hN hcode hfork hrun hnp
    (Artifact.isValidJumpDest_index 1507 (by rfl))

/-- Actual guards, inverse, np store, and UNIT setup through R2 entry. -/
def gasSteps_toR2 (s : State) (a b out : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (oldAt s a b out 0 n ret rest 2019)
      (r2At (unitSetupLeaf (inverseSetupLeaf s 0) n) n
        (InverseArithmetic.nprime (MachineState.readWord s.memory 0)) 0 2079
        (wrapperFrame (InverseArithmetic.nprime (MachineState.readWord s.memory 0))
          a b out 0 n ret rest) 1904) := by
  let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
  let prepared := inverseSetupLeaf s 0
  let unit := unitSetupLeaf prepared n
  have preparedEnv : prepared.executionEnv = s.executionEnv := inverse_env s
  have preparedHalt : prepared.halt = s.halt := inverse_halt s
  have unitEnv : unit.executionEnv = s.executionEnv := (unit_env prepared n).trans preparedEnv
  have unitHalt : unit.halt = s.halt := (unit_halt prepared n).trans preparedHalt
  have first : GasSteps (oldAt s a b out 0 n ret rest 2019)
      (unitEntry prepared n 0 2068 (wrapperFrame np a b out 0 n ret rest)) :=
    gasSteps_toUnit s a b out 0 n ret rest hcap hn hN hodd hcode hfork hrun hnp
  have middle : GasSteps (unitEntry prepared n 0 2068 (wrapperFrame np a b out 0 n ret rest))
      (wrapperAt unit np a b out 0 n ret rest 2068) :=
    gasSteps_unitHelper prepared np a b out n ret rest hcap hn hN
      (by rw [preparedEnv]; exact hcode) (by simpa only [State.fork, preparedEnv] using hfork)
      (by rw [preparedHalt]; exact hrun) (by rw [preparedEnv]; exact hnp)
  have last : GasSteps (wrapperAt unit np a b out 0 n ret rest 2068)
      (r2At unit n np 0 2079 (wrapperFrame np a b out 0 n ret rest) 1904) :=
    gasSteps_r2Call unit np a b out 0 n ret rest hcap
      (by rw [unitEnv]; exact hcode) (by rw [unitHalt]; exact hrun)
      (by simpa only [State.fork, unitEnv] using hfork) (by rw [unitEnv]; exact hnp)
  exact first.trans (middle.trans last)

-- The legacy execution theorem retains every word-sized count and pointer.
def gasSteps_legacyReturn (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hbound : n < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (oldAt s a b out modulus n ret rest 310)
      (returnedState s (fallbackEffects s a b out modulus n ret rest) ret rest) := by
  rw [fallbackEffects_actual_return]
  exact BigMul.gasSteps_mulModBig s a b out modulus n ret rest
    hcap hbound hcode hfork hrun hnp hret

def gasSteps_zeroReturn (s : State) (a b out modulus ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (oldAt s a b out modulus 0 ret rest 2019)
      (returnedState s (fallbackEffects s a b out modulus 0 ret rest) ret rest) :=
  (gasSteps_zeroTail s a b out modulus ret rest hcap hcode hrun hfork hnp).trans
    (gasSteps_legacyReturn s a b out modulus 0 ret rest hcap (by decide)
      hcode hfork hrun hnp hret)

def gasSteps_largeReturn (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hlarge : 32 < n) (hbound : n < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (oldAt s a b out modulus n ret rest 2019)
      (returnedState s (fallbackEffects s a b out modulus n ret rest) ret rest) :=
  (gasSteps_largeTail s a b out modulus n ret rest hcap hlarge hbound
    hcode hrun hfork hnp).trans
    (gasSteps_legacyReturn s a b out modulus n ret rest hcap hbound
      hcode hfork hrun hnp hret)

def gasSteps_evenReturn (s : State) (a b out modulus : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hn : 1 ≤ n) (hN : n ≤ 32)
    (heven : (MachineState.readWord s.memory modulus.toNat).toNat % 2 = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (oldAt s a b out modulus n ret rest 2019)
      (returnedState s (evenFallbackEffects s a b out modulus n ret rest) ret rest) :=
  (gasSteps_evenTail s a b out modulus n ret rest hcap hn hN heven
    hcode hrun hfork hnp).trans
    (gasSteps_legacyReturn (loadLowLeaf s modulus) a b out modulus n ret rest
      hcap (by omega) hcode hfork hrun hnp hret)

/-- Exact prefix through the first square call, before any core execution. -/
def gasSteps_toFirstSquare (s : State) (a b out : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
    let ready := unitSetupLeaf (inverseSetupLeaf s 0) n
    let saved := wrapperFrame np a b out 0 n ret rest
    GasSteps (oldAt s a b out 0 n ret rest 2019)
      (coreEntry (r2DoubledLeaf ready 0 n) 8192 8192 3072 0 n np 1990
        (r2Frame 0 n np 0 2079 saved)) := by
  let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
  let ready := unitSetupLeaf (inverseSetupLeaf s 0) n
  let saved := wrapperFrame np a b out 0 n ret rest
  let doubled := r2DoubledLeaf ready 0 n
  have hsaved : saved.length < 987 := by
    dsimp only [saved]
    rw [wrapperFrame_length]
    omega
  have readyEnv : ready.executionEnv = s.executionEnv :=
    (unit_env (inverseSetupLeaf s 0) n).trans (inverse_env s)
  have readyHalt : ready.halt = s.halt :=
    (unit_halt (inverseSetupLeaf s 0) n).trans (inverse_halt s)
  have doubledEnv : doubled.executionEnv = s.executionEnv := by
    change (doubleProgress (copyUnitLeaf ready n) 0 n (2*n)).executionEnv = _
    rw [progress_env]
    exact readyEnv
  have doubledHalt : doubled.halt = s.halt := by
    change (doubleProgress (copyUnitLeaf ready n) 0 n (2*n)).halt = _
    rw [progress_halt]
    exact readyHalt
  have first : GasSteps (oldAt s a b out 0 n ret rest 2019)
      (r2At ready n np 0 2079 saved 1904) :=
    gasSteps_toR2 s a b out n ret rest hcap hn hN hodd hcode hfork hrun hnp
  have middle : GasSteps (r2At ready n np 0 2079 saved 1904)
      (loopAt doubled n 0 np 0 2079 saved 1961) :=
    gasSteps_r2DoublesToSquares ready n np 0 2079 saved hsaved hN
      (by rw [readyEnv]; exact hcode) (by simpa only [State.fork, readyEnv] using hfork)
      (by rw [readyHalt]; exact hrun) (by rw [readyEnv]; exact hnp)
  have last : GasSteps (loopAt doubled n 0 np 0 2079 saved 1961)
      (coreEntry doubled 8192 8192 3072 0 n np 1990 (r2Frame 0 n np 0 2079 saved)) :=
    gasSteps_squareToCore doubled n 0 np 0 2079 saved hsaved (by decide)
      (by rw [doubledEnv]; exact hcode) (by simpa only [State.fork, doubledEnv] using hfork)
      (by rw [doubledHalt]; exact hrun) (by rw [doubledEnv]; exact hnp)
  exact first.trans (middle.trans last)

theorem modulusLow_eq (s : State) (n m : Nat) (hn : 1 ≤ n)
    (hmod : Limbs.Represents s.memory 0 n m) :
    (MachineState.readWord s.memory 0).toNat = m % (2^256) := by
  simpa only [Nat.mul_zero, Nat.add_zero, pow_zero, Nat.div_one,
    CoreMemory.B, Limbs.radix] using
    (CoreMemory.represented_digit (i := 0) hmod (by omega))

theorem modulusLow_odd (s : State) (n m : Nat) (hn : 1 ≤ n) (hodd : m % 2 = 1)
    (hmod : Limbs.Represents s.memory 0 n m) :
    (MachineState.readWord s.memory 0).toNat % 2 = 1 := by
  rw [modulusLow_eq s n m hn hmod,
    Nat.mod_mod_of_dvd m (by decide : 2 ∣ 2^256)]
  exact hodd

theorem modulusInverse_correct (s : State) (n m : Nat) (hn : 1 ≤ n)
    (hodd : m % 2 = 1) (hmod : Limbs.Represents s.memory 0 n m) :
    (m * (InverseArithmetic.nprime (MachineState.readWord s.memory 0)).toNat + 1) %
      (2^256) = 0 := by
  have h := InverseArithmetic.nprime_correct (MachineState.readWord s.memory 0)
    (modulusLow_odd s n m hn hodd hmod)
  rw [modulusLow_eq s n m hn hmod] at h
  exact Domain.inverse_lift m _ h

private theorem inverse_preserves_low (s : State) (n p value : Nat)
    (hp : p + 32*n ≤ 3072) (hrep : Limbs.Represents s.memory p n value) :
    Limbs.Represents (inverseSetupLeaf s 0).memory p n value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt := List.mem_range.mp hj
  apply congrArg UInt256.toNat
  unfold MachineState.readWord
  rw [setup_preserves_low s 0 (p + 32*j) 32 (by omega)]

/-- Actual inverse/store and accepted UNIT effects, ready for the R2 helper. -/
theorem preparedUnit_correct (s : State) (n m : Nat) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hm : 0 < m) (hodd : m % 2 = 1) (hmod : Limbs.Represents s.memory 0 n m) :
    let ready := unitSetupLeaf (inverseSetupLeaf s 0) n
    let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
    Limbs.Represents ready.memory 7168 n (Domain.R n % m) ∧
      Limbs.Represents ready.memory 0 n m ∧
      (m * np.toNat + 1) % (2^256) = 0 ∧
      (∀ p value, p + 32*n ≤ 3072 → Limbs.Represents s.memory p n value →
        Limbs.Represents ready.memory p n value) := by
  let prepared := inverseSetupLeaf s 0
  have hmodPrepared : Limbs.Represents prepared.memory 0 n m :=
    inverse_preserves_low s n 0 m (by omega) hmod
  have unit := MontgomeryOneCorrect.returned_correct prepared n m 0 []
    hn hN hm hmod.1 hodd hmodPrepared
  refine ⟨unit.1, unit.2, modulusInverse_correct s n m hn hodd hmod, ?_⟩
  intro p value hp hrep
  exact MontgomeryOneCorrect.returned_preserves_region prepared n m p value 0 []
    hn hN hm hmod.1 hodd hmodPrepared
    ⟨Or.inr (by change p + 32*n ≤ 7168; omega),
      Or.inl (by change p + 32*n ≤ 5120; omega)⟩
    (inverse_preserves_low s n p value hp hrep)

@[simp] theorem returnedState_halt (s : State) (e : Effects) (ret : UInt256)
    (rest : List UInt256) : (returnedState s e ret rest).halt = s.halt := rfl

@[simp] theorem returnedState_executionEnv (s : State) (e : Effects) (ret : UInt256)
    (rest : List UInt256) :
    (returnedState s e ret rest).executionEnv = s.executionEnv := rfl

@[simp] theorem returnedState_fork (s : State) (e : Effects) (ret : UInt256)
    (rest : List UInt256) : (returnedState s e ret rest).fork = s.fork := rfl

/-- The represented low word has exactly the whole modulus parity. -/
theorem modulusLow_parity (s : State) (n m : Nat) (hn : 1 ≤ n)
    (hmod : Limbs.Represents s.memory 0 n m) :
    (MachineState.readWord s.memory 0).toNat % 2 = m % 2 := by
  rw [modulusLow_eq s n m hn hmod]
  exact Nat.mod_mod_of_dvd m (by decide : 2 ∣ 2^256)

private theorem outer_preserves_low (current : State) (a b : UInt256)
    (count steps p value : Nat) (ret : UInt256) (rest : List UInt256)
    (hsteps : steps ≤ count) (hcount : count ≤ 32) (hp : p + 32*count ≤ 3072)
    (hrep : Limbs.Represents current.memory p count value) :
    Limbs.Represents
      (BigMul.mulOuterProgress current a b (UInt256.ofNat 3072) (UInt256.ofNat 0)
        count ret rest steps).memory p count value := by
  induction steps with
  | zero => simpa [BigMul.mulOuterProgress] using hrep
  | succ steps ih =>
      let before := BigMul.mulOuterProgress current a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count ret rest steps
      let loaded := BigMul.mulLoadedState before b steps
      let word := BigMul.mulLoadedWord before b steps
      have hbefore : Limbs.Represents before.memory p count value := ih (by omega)
      have hloaded : Limbs.Represents loaded.memory p count value := by
        simpa [loaded, BigMul.mulLoadedState] using hbefore
      simpa [BigMul.mulOuterProgress, before, loaded, word] using
        BigMul.mulWordProgress_preserves_region loaded word a b count steps 256
          p value ret rest (by omega) hcount (Or.inr hp) (Or.inr (by omega))
          (Or.inl (by omega)) hloaded

private theorem legacy_preserves_low (s : State) (bPtr : UInt256)
    (count p value : Nat) (ret : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32) (hp : p + 32*count ≤ 3072)
    (hrep : Limbs.Represents s.memory p count value) :
    Limbs.Represents
      (returnedState s (fallbackEffects s 2048 bPtr 3072 0 count ret rest) ret rest).memory
      p count value := by
  let cleared := BigMul.mulAfterClear s 2048 bPtr 3072 0 count ret rest
  let copied := BigMul.mulAfterCopy s 2048 bPtr 3072 0 count ret rest
  have hcleared : Limbs.Represents cleared.memory p count value := by
    simpa [cleared, BigMul.mulAfterClear, Word.literal_eq_ofNat] using
      BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 p count value
        (by omega) (Or.inr hp) hrep
  have hcopied : Limbs.Represents copied.memory p count value := by
    simpa [copied, BigMul.mulAfterCopy, cleared, Word.literal_eq_ofNat] using
      BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096 2048 p
        count value (by omega) (Or.inr (by omega)) hcleared
  have hprogress := outer_preserves_low copied 2048 bPtr count count p value ret rest
    (by omega) hcount hp hcopied
  simpa [returnedState, fallbackEffects, effectsOf, copied, BigMul.mulReturned,
    Word.literal_eq_ofNat] using hprogress

theorem legacyReturn_correct (s : State) (bPtr : UInt256) (count a b m : Nat)
    (ret : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr.toNat ≤ 2048) (hm : 0 < m) (ha : a < m)
    (hacc : Limbs.Represents s.memory 2048 count a)
    (hbase : Limbs.Represents s.memory bPtr.toNat count b)
    (hmod : Limbs.Represents s.memory 0 count m) :
    Limbs.Represents
        (returnedState s (fallbackEffects s 2048 bPtr 3072 0 count ret rest) ret rest).memory
        3072 count ((a*b)%m) ∧
      (a*b)%m < m ∧
      (∀ p value, p + 32*count ≤ 3072 → Limbs.Represents s.memory p count value →
        Limbs.Represents
          (returnedState s (fallbackEffects s 2048 bPtr 3072 0 count ret rest) ret rest).memory
          p count value) := by
  refine ⟨?_, Nat.mod_lt _ hm, ?_⟩
  · have h := BigMul.mulReturned_represents_product s bPtr.toNat count a b m ret rest
      hcount (by omega) hm ha hacc hbase hmod
    simpa [returnedState, fallbackEffects, effectsOf,
      ← Word.word_eq_ofNat_toNat bPtr, Word.literal_eq_ofNat] using h
  · intro p value hp hrep
    exact legacy_preserves_low s bPtr count p value ret rest hcount hp hrep

theorem evenReturn_correct (s : State) (bPtr : UInt256) (count a b m : Nat)
    (ret : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr.toNat ≤ 2048) (hm : 0 < m) (ha : a < m)
    (hacc : Limbs.Represents s.memory 2048 count a)
    (hbase : Limbs.Represents s.memory bPtr.toNat count b)
    (hmod : Limbs.Represents s.memory 0 count m) :
    Limbs.Represents
        (returnedState s (evenFallbackEffects s 2048 bPtr 3072 0 count ret rest) ret rest).memory
        3072 count ((a*b)%m) ∧
      (a*b)%m < m ∧
      (∀ p value, p + 32*count ≤ 3072 → Limbs.Represents s.memory p count value →
        Limbs.Represents
          (returnedState s (evenFallbackEffects s 2048 bPtr 3072 0 count ret rest) ret rest).memory
          p count value) := by
  simpa only [returnedState, evenFallbackEffects, loadLowLeaf] using
    legacyReturn_correct (loadLowLeaf s 0) bPtr count a b m ret rest hcount hbPtr hm ha
      hacc hbase hmod

/-- Frozen fixed-layout wrapper effects. Even fallback includes the actual MLOAD. -/
def normalEffects (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) : Effects :=
  if count = 0 then fallbackEffects s 2048 b 3072 0 count ret rest
  else if 32 < count then fallbackEffects s 2048 b 3072 0 count ret rest
  else if (MachineState.readWord s.memory 0).toNat % 2 = 0 then
    evenFallbackEffects s 2048 b 3072 0 count ret rest
  else
    let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
    let ready := unitSetupLeaf (inverseSetupLeaf s 0) count
    effectsOf (MontgomeryWrapperValue.productLeaf ready b.toNat count np)

/-- One flat State update; callers do not unfold the effects to read control fields. -/
def normalReturned (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  returnedState s (normalEffects s b count ret rest) ret rest

def normalEntry (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  oldAt s 2048 b 3072 0 count ret rest 2019

@[simp] theorem normalReturned_pc (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (normalReturned s b count ret rest).pc = ret := rfl

@[simp] theorem normalReturned_stack (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (normalReturned s b count ret rest).stack = rest := rfl

@[simp] theorem normalReturned_halt (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (normalReturned s b count ret rest).halt = s.halt := rfl

@[simp] theorem normalReturned_executionEnv (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (normalReturned s b count ret rest).executionEnv = s.executionEnv := rfl

@[simp] theorem normalReturned_fork (s : State) (b : UInt256) (count : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (normalReturned s b count ret rest).fork = s.fork := rfl

/-- Normal product for every positive represented modulus, including the even fallback.
Only a is reduced. The represented b need only fit R; the two inputs may alias. -/
theorem normalReturned_correct (s : State) (bPtr : UInt256) (count a b m : Nat)
    (ret : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr.toNat ≤ 2048) (hm : 0 < m) (ha : a < m)
    (hacc : Limbs.Represents s.memory 2048 count a)
    (hbase : Limbs.Represents s.memory bPtr.toNat count b)
    (hmod : Limbs.Represents s.memory 0 count m) :
    Limbs.Represents (normalReturned s bPtr count ret rest).memory 3072 count ((a*b)%m) ∧
      (a*b)%m < m ∧
      (∀ p value, p + 32*count ≤ 3072 → Limbs.Represents s.memory p count value →
        Limbs.Represents (normalReturned s bPtr count ret rest).memory p count value) := by
  have hn : 1 ≤ count := by
    by_contra h
    have hc : count = 0 := by omega
    have hmBound := hmod.1
    rw [hc, pow_zero] at hmBound
    omega
  unfold normalReturned normalEffects
  rw [if_neg (by omega : count ≠ 0), if_neg (by omega : ¬32 < count)]
  by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
  · rw [if_pos heven]
    exact evenReturn_correct s bPtr count a b m ret rest hcount hbPtr hm ha hacc hbase hmod
  · rw [if_neg heven]
    have hparity := modulusLow_parity s count m hn hmod
    have hodd : m % 2 = 1 := by omega
    let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
    let ready := unitSetupLeaf (inverseSetupLeaf s 0) count
    have prepared := preparedUnit_correct s count m hn hcount hm hodd hmod
    have haccReady : Limbs.Represents ready.memory 2048 count a :=
      prepared.2.2.2 2048 a (by omega) hacc
    have hbaseReady : Limbs.Represents ready.memory bPtr.toNat count b :=
      prepared.2.2.2 bPtr.toNat b (by omega) hbase
    have product := MontgomeryWrapperValue.productLeaf_correct ready bPtr.toNat count a b m np
      hbPtr hn hcount hm hodd ha hbase.1 prepared.2.2.1 prepared.1 prepared.2.1
      haccReady hbaseReady
    refine ⟨product.1, product.2.1, ?_⟩
    intro p value hp hrep
    exact product.2.2 p value hp (prepared.2.2.2 p value hp hrep)

theorem prepared_frame (s : State) (n : Nat) :
    { unitSetupLeaf (inverseSetupLeaf s 0) n with
        memory := s.memory, activeWords := s.activeWords } = s := by
  cases s
  rfl

private theorem returned_of_frame (s t : State) (ret : UInt256) (rest : List UInt256)
    (hframe : { t with memory := s.memory, activeWords := s.activeWords } = s) :
    returnedState s (effectsOf t) ret rest =
      { t with pc := ret, stack := rest } := by
  have h := congrArg (fun u : State =>
    returnedState u (effectsOf t) ret rest) hframe
  exact h.symm

theorem fastReturned_eq (s : State) (b : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1) :
    let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
    let ready := unitSetupLeaf (inverseSetupLeaf s 0) n
    { MontgomeryWrapperValue.productLeaf ready b.toNat n np with pc := ret, stack := rest } =
      normalReturned s b n ret rest := by
  let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
  let ready := unitSetupLeaf (inverseSetupLeaf s 0) n
  let product := MontgomeryWrapperValue.productLeaf ready b.toNat n np
  have hp := MontgomeryWrapperValue.productLeaf_frame ready b.toNat n np
  have hframe : { product with memory := s.memory, activeWords := s.activeWords } = s := by
    have h := congrArg (fun u : State => { u with memory := s.memory, activeWords := s.activeWords }) hp
    exact h.trans (prepared_frame s n)
  have hreturned := returned_of_frame s product ret rest hframe
  simpa only [normalReturned, normalEffects,
    if_neg (by omega : n ≠ 0), if_neg (by omega : ¬32 < n), hodd,
    if_neg (by decide : ¬(1 : Nat) = 0)] using hreturned.symm

private theorem frame_env (s t : State)
    (h : { t with memory := s.memory, activeWords := s.activeWords } = s) :
    t.executionEnv = s.executionEnv := by
  have he := congrArg (fun u : State => u.executionEnv) h
  exact he

private theorem frame_halt (s t : State)
    (h : { t with memory := s.memory, activeWords := s.activeWords } = s) :
    t.halt = s.halt := by
  have hr := congrArg (fun u : State => u.halt) h
  exact hr

def gasSteps_squareBody (s : State) (n i : Nat) (np ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 987) (hN : n ≤ 32) (hi : i < 7)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n i np 0 ret saved 1961)
      (loopAt (MontgomeryWrapperValue.squareStep s n np) n (i+1) np 0 ret saved 1961) := by
  let core := MontgomeryWrapperValue.coreLeaf s 8192 8192 3072 n np
  have he := frame_env s core (MontgomeryWrapperValue.coreLeaf_frame s 8192 8192 3072 n np)
  have hr := frame_halt s core (MontgomeryWrapperValue.coreLeaf_frame s 8192 8192 3072 n np)
  have call := gasSteps_squareToCore s n i np 0 ret saved hcap hi hcode hfork hrun hnp
  have run : GasSteps (coreEntry s 8192 8192 3072 0 n np 1990 (r2Frame i n np 0 ret saved))
      (loopAt core n i np 0 ret saved 1990) := by
    simpa only [loopAt, Word.literal_eq_ofNat] using
      MontgomeryCoreBridge.gasSteps_coreLeaf s 8192 8192 3072 n np 1990 (r2Frame i n np 0 ret saved)
        hN (by decide) (by decide)
        (by simp only [r2Frame, List.length_append, List.length_cons, List.length_nil]; omega)
        hcode hfork hrun hnp (Artifact.isValidJumpDest_index 1458 (by rfl))
  have resume := gasSteps_squareResume core n i np 0 ret saved hcap hN
    (by rw [he]; exact hcode) (by simpa only [State.fork, he] using hfork)
    (by rw [hr]; exact hrun) (by rw [he]; exact hnp)
  exact call.trans (run.trans resume)

def gasSteps_squares (s : State) (n : Nat) (np ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopAt s n 0 np 0 ret saved 1961)
      (loopAt (MontgomeryWrapperValue.squareProgress s n np 7) n 7 np 0 ret saved 1961) := by
  exact GasSteps.iterateBounded
    (I := fun i => loopAt (MontgomeryWrapperValue.squareProgress s n np i) n i np 0 ret saved 1961)
    7 (fun i hi => by
      let current := MontgomeryWrapperValue.squareProgress s n np i
      have he := frame_env s current (MontgomeryWrapperValue.squareProgress_frame s n np i)
      have hr := frame_halt s current (MontgomeryWrapperValue.squareProgress_frame s n np i)
      exact gasSteps_squareBody current n i np ret saved hcap hN hi
        (by rw [he]; exact hcode) (by simpa only [State.fork, he] using hfork)
        (by rw [hr]; exact hrun) (by rw [he]; exact hnp))

/-- Actual copy, 2*n doubles, seven core/copy squares, and R2 return. -/
def gasSteps_r2 (s : State) (n : Nat) (np ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 987) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (r2At s n np 0 ret saved 1904)
      { MontgomeryWrapperValue.r2Leaf s n np with pc := ret, stack := saved } := by
  let doubled := r2DoubledLeaf s 0 n
  let squared := MontgomeryWrapperValue.r2Leaf s n np
  have doubledEnv : doubled.executionEnv = s.executionEnv := by
    simp only [doubled, r2DoubledLeaf, progress_env, copyUnitLeaf, flatLeaf]
  have doubledHalt : doubled.halt = s.halt := by
    simp only [doubled, r2DoubledLeaf, progress_halt, copyUnitLeaf, flatLeaf]
  have squaredEnv := frame_env s squared (MontgomeryWrapperValue.r2Leaf_frame s n np)
  have squaredHalt := frame_halt s squared (MontgomeryWrapperValue.r2Leaf_frame s n np)
  have first := gasSteps_r2DoublesToSquares s n np 0 ret saved hcap hN hcode hfork hrun hnp
  have middle := gasSteps_squares doubled n np ret saved hcap hN
    (by rw [doubledEnv]; exact hcode)
    (by simpa only [State.fork, doubledEnv] using hfork)
    (by rw [doubledHalt]; exact hrun) (by rw [doubledEnv]; exact hnp)
  have last := gasSteps_squareExit squared n np 0 ret saved hcap
    (by rw [squaredEnv]; exact hcode)
    (by simpa only [State.fork, squaredEnv] using hfork) hret
    (by rw [squaredHalt]; exact hrun) (by rw [squaredEnv]; exact hnp)
  exact first.trans (middle.trans last)


/-- R2 setup and the two ordered core calls, ending with actual wrapper cleanup. -/
def gasSteps_product (s : State) (b : UInt256) (n : Nat) (np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980) (hN : n ≤ 32)
    (hbPtr : b.toNat ≤ 2048)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (r2At s n np 0 2079 (wrapperFrame np 2048 b 3072 0 n ret rest) 1904)
      { MontgomeryWrapperValue.productLeaf s b.toNat n np with pc := ret, stack := rest } := by
  let saved := wrapperFrame np 2048 b 3072 0 n ret rest
  let r2 := MontgomeryWrapperValue.r2Leaf s n np
  let encoded := MontgomeryWrapperValue.coreLeaf r2 2048 8192 7168 n np
  let product := MontgomeryWrapperValue.coreLeaf encoded b.toNat 7168 3072 n np
  have savedCap : saved.length + 8 < 1000 := by
    dsimp only [saved]
    rw [wrapperFrame_length]
    omega
  have r2Env := frame_env s r2 (MontgomeryWrapperValue.r2Leaf_frame s n np)
  have r2Halt := frame_halt s r2 (MontgomeryWrapperValue.r2Leaf_frame s n np)
  have encodedEnv : encoded.executionEnv = s.executionEnv :=
    (frame_env r2 encoded (MontgomeryWrapperValue.coreLeaf_frame r2 2048 8192 7168 n np)).trans r2Env
  have encodedHalt : encoded.halt = s.halt :=
    (frame_halt r2 encoded (MontgomeryWrapperValue.coreLeaf_frame r2 2048 8192 7168 n np)).trans r2Halt
  have productEnv : product.executionEnv = s.executionEnv :=
    (frame_env encoded product (MontgomeryWrapperValue.coreLeaf_frame encoded b.toNat 7168 3072 n np)).trans encodedEnv
  have productHalt : product.halt = s.halt :=
    (frame_halt encoded product (MontgomeryWrapperValue.coreLeaf_frame encoded b.toNat 7168 3072 n np)).trans encodedHalt
  have setup : GasSteps (r2At s n np 0 2079 saved 1904)
      (wrapperAt r2 np 2048 b 3072 0 n ret rest 2079) := by
    simpa only [wrapperAt, saved, Word.literal_eq_ofNat] using
      gasSteps_r2 s n np 2079 saved
        (by dsimp only [saved]; rw [wrapperFrame_length]; omega)
        hN hcode hfork hrun hnp (Artifact.isValidJumpDest_index 1514 (by rfl))
  have encodeCall := gasSteps_encodeCall r2 np 2048 b 3072 0 n ret rest hcap
    (by rw [r2Env]; exact hcode) (by rw [r2Halt]; exact hrun)
    (by simpa only [State.fork, r2Env] using hfork) (by rw [r2Env]; exact hnp)
  have encodeRun : GasSteps (coreEntry r2 2048 8192 7168 0 n np 2097 saved)
      (wrapperAt encoded np 2048 b 3072 0 n ret rest 2097) := by
    simpa only [wrapperAt, saved, Word.literal_eq_ofNat] using
      MontgomeryCoreBridge.gasSteps_coreLeaf r2 2048 8192 7168 n np 2097 saved hN (by decide) (by decide)
        savedCap (by rw [r2Env]; exact hcode)
        (by simpa only [State.fork, r2Env] using hfork)
        (by rw [r2Halt]; exact hrun) (by rw [r2Env]; exact hnp)
        (Artifact.isValidJumpDest_index 1524 (by rfl))
  have productCall := gasSteps_productCall encoded np 2048 b 3072 0 n ret rest hcap
    (by rw [encodedEnv]; exact hcode) (by rw [encodedHalt]; exact hrun)
    (by simpa only [State.fork, encodedEnv] using hfork) (by rw [encodedEnv]; exact hnp)
  have productRun : GasSteps (coreEntry encoded b 7168 3072 0 n np 2113 saved)
      (wrapperAt product np 2048 b 3072 0 n ret rest 2113) := by
    simpa only [wrapperAt, saved, ← Word.word_eq_ofNat_toNat b, Word.literal_eq_ofNat] using
      MontgomeryCoreBridge.gasSteps_coreLeaf encoded b.toNat 7168 3072 n np 2113 saved hN (by omega) (by decide)
        savedCap (by rw [encodedEnv]; exact hcode)
        (by simpa only [State.fork, encodedEnv] using hfork)
        (by rw [encodedHalt]; exact hrun) (by rw [encodedEnv]; exact hnp)
        (Artifact.isValidJumpDest_index 1534 (by rfl))
  have done := gasSteps_wrapperDone product np 2048 b 3072 0 n ret rest hcap
    (by rw [productEnv]; exact hcode) (by rw [productHalt]; exact hrun) hret
    (by simpa only [State.fork, productEnv] using hfork) (by rw [productEnv]; exact hnp)
  exact setup.trans (encodeCall.trans (encodeRun.trans (productCall.trans (productRun.trans done))))

def gasSteps_fast (s : State) (b : UInt256) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hbPtr : b.toNat ≤ 2048) (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (normalEntry s b n ret rest) (normalReturned s b n ret rest) := by
  let np := InverseArithmetic.nprime (MachineState.readWord s.memory 0)
  let ready := unitSetupLeaf (inverseSetupLeaf s 0) n
  have readyEnv := frame_env s ready (prepared_frame s n)
  have readyHalt := frame_halt s ready (prepared_frame s n)
  have prep := gasSteps_toR2 s 2048 b 3072 n ret rest hcap hn hN hodd hcode hfork hrun hnp
  have product := gasSteps_product ready b n np ret rest hcap hN hbPtr
    (by rw [readyEnv]; exact hcode) (by simpa only [State.fork, readyEnv] using hfork)
    (by rw [readyHalt]; exact hrun) (by rw [readyEnv]; exact hnp) hret
  rw [← fastReturned_eq s b n ret rest hn hN hodd]
  exact prep.trans product

/-- Total wrapper execution for every word-sized count. No value assumptions. -/
def gasSteps_normal (s : State) (b : UInt256) (count : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980) (hcount : count < 2^256)
    (hbPtr : b.toNat ≤ 2048)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (normalEntry s b count ret rest) (normalReturned s b count ret rest) := by
  by_cases hzero : count = 0
  · subst count
    change GasSteps (oldAt s 2048 b 3072 0 0 ret rest 2019)
      (returnedState s (fallbackEffects s 2048 b 3072 0 0 ret rest) ret rest)
    exact gasSteps_zeroReturn s 2048 b 3072 0 ret rest hcap hcode hfork hrun hnp hret
  · by_cases hlarge : 32 < count
    · simpa only [normalEntry, normalReturned, normalEffects, if_neg hzero, if_pos hlarge] using
        gasSteps_largeReturn s 2048 b 3072 0 count ret rest hcap hlarge hcount hcode hfork hrun hnp hret
    · have hn : 1 ≤ count := by omega
      have hN : count ≤ 32 := by omega
      by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
      · simpa only [normalEntry, normalReturned, normalEffects, if_neg hzero, if_neg hlarge,
          if_pos heven] using
          gasSteps_evenReturn s 2048 b 3072 0 count ret rest hcap hn hN heven
            hcode hfork hrun hnp hret
      · exact gasSteps_fast s b count ret rest hcap hn hN hbPtr (by omega) hcode hfork hrun hnp hret

-- Preserve the runtime name in the first frozen caller handoff.
def gasSteps_wrapper (s : State) (b : UInt256) (count : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980) (hcount : count < 2^256)
    (hbPtr : b.toNat ≤ 2048)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (normalEntry s b count ret rest) (normalReturned s b count ret rest) :=
  gasSteps_normal s b count ret rest hcap hcount hbPtr hcode hfork hrun hnp hret

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock
