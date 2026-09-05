import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

-- Frozen UNIT118 control, rebound to the canonical1904-byte artifact.
namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneBlock


open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp (submissionBytecode)

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

def clearPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1331 .JUMPDEST,
   pushAt 1332 2 1798,
   opAt 1333 (.Dup ⟨1, by decide⟩),
   pushAt 1334 2 7168,
   pushAt 1335 2 19,
   opAt 1336 .JUMP]

def testPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1337 .JUMPDEST,
   pushAt 1338 1 1,
   opAt 1339 (.Dup ⟨1, by decide⟩),
   opAt 1340 .SUB,
   pushAt 1341 1 5,
   opAt 1342 .SHL,
   opAt 1343 (.Dup ⟨2, by decide⟩),
   opAt 1344 .ADD,
   opAt 1345 .MLOAD,
   pushAt 1346 1 255,
   opAt 1347 .SHR,
   pushAt 1348 2 1840,
   opAt 1349 .JUMPI]

def seedPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1350 1 1,
   pushAt 1351 2 7168,
   opAt 1352 .MSTORE,
   pushAt 1353 2 1860,
   opAt 1354 (.Dup ⟨1, by decide⟩),
   opAt 1355 (.Dup ⟨3, by decide⟩),
   pushAt 1356 0 0,
   pushAt 1357 0 0,
   pushAt 1358 2 7168,
   pushAt 1359 0 0,
   pushAt 1360 0 0,
   pushAt 1361 0 0,
   pushAt 1362 0 0,
   pushAt 1363 2 174,
   opAt 1364 .JUMP]

def fastPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1365 .JUMPDEST,
   pushAt 1366 2 1900,
   opAt 1367 (.Dup ⟨1, by decide⟩),
   opAt 1368 (.Dup ⟨3, by decide⟩),
   pushAt 1369 0 0,
   pushAt 1370 0 0,
   pushAt 1371 2 7168,
   pushAt 1372 0 0,
   pushAt 1373 1 1,
   pushAt 1374 0 0,
   pushAt 1375 0 0,
   pushAt 1376 2 174,
   opAt 1377 .JUMP]

def loopSetupPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1378 .JUMPDEST,
   pushAt 1379 0 0]

def guardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1380 .JUMPDEST,
   opAt 1381 (.Dup ⟨1, by decide⟩),
   pushAt 1382 2 256,
   opAt 1383 .MUL,
   opAt 1384 (.Dup ⟨1, by decide⟩),
   opAt 1385 .LT,
   opAt 1386 .ISZERO,
   pushAt 1387 2 1898,
   opAt 1388 .JUMPI]

def bodyPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1389 2 1890,
   opAt 1390 (.Dup ⟨2, by decide⟩),
   opAt 1391 (.Dup ⟨4, by decide⟩),
   pushAt 1392 1 1,
   pushAt 1393 2 7168,
   opAt 1394 (.Dup ⟨0, by decide⟩),
   pushAt 1395 2 104,
   opAt 1396 .JUMP]

def nextPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1397 .JUMPDEST,
   pushAt 1398 1 1,
   opAt 1399 .ADD,
   pushAt 1400 2 1862,
   opAt 1401 .JUMP]

def exitPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1402 .JUMPDEST,
   opAt 1403 .POP]

def donePath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1404 .JUMPDEST,
   opAt 1405 .POP,
   opAt 1406 .POP,
   opAt 1407 .JUMP]

@[simp] private theorem unitPCs (i : Nat) (hi : 1331 ≤ i) (hii : i ≤ 1407) :
    Artifact.submissionArtifact.instructionPC i =
      [1786,1787,1790,1791,1794,1797,1798,1799,1801,1802,1803,1805,1806,1807,1808,1809,1811,1812,1815,1816,1818,1821,1822,1825,1826,1827,1828,1829,1832,1833,1834,1835,1836,1839,1840,1841,1844,1845,1846,1847,1848,1851,1852,1854,1855,1856,1859,1860,1861,1862,1863,1864,1867,1868,1869,1870,1871,1874,1875,1878,1879,1880,1882,1885,1886,1889,1890,1891,1893,1894,1897,1898,1899,1900,1901,1902,1903][i - 1331]! := by
  interval_cases i <;> decide

@[simp] private theorem clearDest :
    Decode.isValidJumpDest submissionBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

@[simp] private theorem addDest :
    Decode.isValidJumpDest submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

@[simp] private theorem reduceDest :
    Decode.isValidJumpDest submissionBytecode 174 = true :=
  Artifact.isValidJumpDest_index 147 (by rfl)

@[simp] private theorem unitEntryDest :
    Decode.isValidJumpDest submissionBytecode 1786 = true :=
  Artifact.isValidJumpDest_index 1331 (by rfl)

@[simp] private theorem unitClearedDest :
    Decode.isValidJumpDest submissionBytecode 1798 = true :=
  Artifact.isValidJumpDest_index 1337 (by rfl)

@[simp] private theorem unitFastDest :
    Decode.isValidJumpDest submissionBytecode 1840 = true :=
  Artifact.isValidJumpDest_index 1365 (by rfl)

@[simp] private theorem unitReducedDest :
    Decode.isValidJumpDest submissionBytecode 1860 = true :=
  Artifact.isValidJumpDest_index 1378 (by rfl)

@[simp] private theorem unitLoopDest :
    Decode.isValidJumpDest submissionBytecode 1862 = true :=
  Artifact.isValidJumpDest_index 1380 (by rfl)

@[simp] private theorem unitNextDest :
    Decode.isValidJumpDest submissionBytecode 1890 = true :=
  Artifact.isValidJumpDest_index 1397 (by rfl)

@[simp] private theorem unitExitDest :
    Decode.isValidJumpDest submissionBytecode 1898 = true :=
  Artifact.isValidJumpDest_index 1402 (by rfl)

@[simp] private theorem unitDoneDest :
    Decode.isValidJumpDest submissionBytecode 1900 = true :=
  Artifact.isValidJumpDest_index 1404 (by rfl)

def frame (n : Nat) (ret : UInt256) (saved : List UInt256) : List UInt256 :=
  [UInt256.ofNat n, 0, ret] ++ saved

def atFrame (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (pc : Nat) : State :=
  { s with pc := UInt256.ofNat pc, stack := frame n ret saved }

def atLoop (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (pc : Nat) : State :=
  { s with pc := UInt256.ofNat pc, stack := UInt256.ofNat i :: frame n ret saved }

def entry (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) : State :=
  atFrame s n ret saved 1786

def clearLeaf (s : State) (n : Nat) : State :=
  { s with memory := BigHelpers.clearMemory s.memory 7168 n
           activeWords := BigHelpers.clearWords s.activeWords 7168 n }

def top (s : State) (n : Nat) : UInt256 :=
  MachineState.readWord s.memory (32 * (n - 1))

def touched (s : State) (n : Nat) : State :=
  { s with
    activeWords := UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat (32 * (n - 1)) 32) }

def seedLeaf (s : State) : State :=
  { s with memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded 1 32) 7168
           activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 7168 32) }

def reduceLeaf (s : State) (n : Nat) (high : UInt256) : State :=
  let r := MontgomeryReduceBlock.reduceReturned s 7168 0 high n 0 []
  { s with memory := r.memory, activeWords := r.activeWords }

def doubleLeaf (s : State) (n : Nat) : State :=
  let r := BigHelpers.addReturned s 7168 7168 1 0 n 0 []
  { s with memory := r.memory, activeWords := r.activeWords }

def progress (s : State) (n : Nat) : Nat → State
  | 0 => s
  | i+1 => doubleLeaf (progress s n i) n

def loop (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256) : State :=
  atLoop (progress s n i) n i ret saved 1862

def returned (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) : State :=
  let c := clearLeaf s n
  let t := touched c n
  let result := if 2^255 ≤ (top c n).toNat then reduceLeaf t n 1
    else progress (reduceLeaf (seedLeaf t) n 0) n (256*n)
  { s with pc := ret
           stack := saved
           memory := result.memory
           activeWords := result.activeWords }

private theorem topAddress (n : Nat) (hn : 1 ≤ n) (hN : n ≤ 32) :
    UInt256.shiftLeft (UInt256.ofNat n - 1) 5 =
      UInt256.ofNat (32 * (n - 1)) := by
  rw [show (1 : UInt256) = UInt256.ofNat 1 from rfl,
    Word.ofNat_sub_ofNat hn (by omega),
    show (5 : UInt256) = UInt256.ofNat 5 from rfl,
    Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  simp [Nat.mul_comm]

private theorem topCondition (w : UInt256) :
    UInt256.isTrue (UInt256.shiftRight w (UInt256.ofNat 255)) ↔ 2^255 ≤ w.toNat := by
  change (UInt256.shiftRight w (UInt256.ofNat 255)).toNat ≠ 0 ↔ _
  rw [Word.shiftRight_toNat w (by decide), Nat.shiftRight_eq_div_pow]
  omega

set_option linter.unusedSimpArgs false in
theorem run_clear (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock clearPath (entry s n ret saved) =
      some (BigHelpers.clearEntry s 7168 n 1798 (frame n ret saved)) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [clearPath, opAt, pushAt, wfOp, entry, atFrame, frame, BigHelpers.clearEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

set_option linter.unusedSimpArgs false in
theorem run_test (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock testPath (atFrame s n ret saved 1798) =
      some (atFrame (touched s n) n ret saved
        (if 2^255 ≤ (top s n).toNat then 1840 else 1816)) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  have haddr := topAddress n hn hN
  simp only [Word.literal_eq_ofNat] at haddr
  have hfit : 32*(n-1) < 2^256 := by omega
  have hmod := Nat.mod_eq_of_lt hfit
  norm_num at hmod
  simp [testPath, opAt, pushAt, wfOp, atFrame, frame, touched,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    State.activeWordsAfterUInt256, Nat.add_assoc, cap, hrun, hcode,
    Word.word_add_comm, haddr, Nat.mod_eq_of_lt hmod, topCondition, top]
  split_ifs <;> rfl

set_option linter.unusedSimpArgs false in
theorem run_seed (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock seedPath (atFrame s n ret saved 1816) =
      some (MontgomeryReduceBlock.reduceEntry (seedLeaf s) 7168 0 0 n 1860 (frame n ret saved)) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [seedPath, opAt, pushAt, wfOp, atFrame, frame, seedLeaf, MontgomeryReduceBlock.reduceEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    State.activeWordsAfterUInt256, Nat.add_assoc, cap, hrun, hcode]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_fast (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastPath (atFrame s n ret saved 1840) =
      some (MontgomeryReduceBlock.reduceEntry s 7168 0 1 n 1900 (frame n ret saved)) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [fastPath, opAt, pushAt, wfOp, atFrame, frame, MontgomeryReduceBlock.reduceEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_loopSetup (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock loopSetupPath (atFrame s n ret saved 1860) =
      some (loop s n 0 ret saved) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [loopSetupPath, opAt, pushAt, wfOp, atFrame, atLoop, frame, loop, progress,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun]
  rfl

private theorem mulCount (n : Nat) :
    UInt256.ofNat 256 * UInt256.ofNat n = UInt256.ofNat (256*n) := by
  apply Word.word_ext
  change ((UInt256.ofNat 256).val * (UInt256.ofNat n).val).val = _
  rw [Fin.val_mul]
  change (256 % 2^256 * (n % 2^256)) % 2^256 = (256*n) % 2^256
  exact (Nat.mul_mod 256 n (2^256)).symm

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hN : n ≤ 32) (hi : i < 256*n)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock guardPath (atLoop s n i ret saved 1862) =
      some (atLoop s n i ret saved 1875) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  have hc : ¬ UInt256.isTrue
      (UInt256.isZero (UInt256.lt (UInt256.ofNat i) (UInt256.ofNat (256*n)))) := by
    simp only [UInt256.lt, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (show i<2^256 by omega),
      Nat.mod_eq_of_lt (show 256*n<2^256 by omega), if_pos hi]
    decide
  simp [guardPath, opAt, pushAt, wfOp, atLoop, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, mulCount, hc]

set_option linter.unusedSimpArgs false in
theorem run_guard_finish (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock guardPath (atLoop s n (256*n) ret saved 1862) =
      some (atLoop s n (256*n) ret saved 1898) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  have hc : UInt256.isTrue
      (UInt256.isZero (UInt256.lt (UInt256.ofNat (256*n)) (UInt256.ofNat (256*n)))) := by
    simp [UInt256.isTrue, UInt256.isZero, UInt256.lt]
  simp [guardPath, opAt, pushAt, wfOp, atLoop, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, mulCount, hc]

set_option linter.unusedSimpArgs false in
theorem run_body (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock bodyPath (atLoop s n i ret saved 1875) =
      some (BigHelpers.addEntry s 7168 7168 1 0 n 1890
        (UInt256.ofNat i :: frame n ret saved)) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [bodyPath, opAt, pushAt, wfOp, atLoop, frame, BigHelpers.addEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode]

set_option linter.unusedSimpArgs false in
theorem run_next (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock nextPath (atLoop s n i ret saved 1890) =
      some (atLoop s n (i+1) ret saved 1862) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [nextPath, opAt, pushAt, wfOp, atLoop, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, Word.word_add_comm]

set_option linter.unusedSimpArgs false in
theorem run_exit (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock exitPath (atLoop s n i ret saved 1898) =
      some (atFrame s n ret saved 1900) := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [exitPath, opAt, pushAt, wfOp, atLoop, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun]

set_option linter.unusedSimpArgs false in
theorem run_done (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    Stepper.runLocatedBlock donePath (atFrame s n ret saved 1900) =
      some { s with pc := ret, stack := saved } := by
  have cap : ∀ k, k ≤ 28 → saved.length + k < 1024 := by omega
  simp [donePath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode, hret]

namespace MemoryBounds


open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

theorem clearWords_eq (active : UInt256) (n : Nat) (hN : n ≤ 32) :
    BigHelpers.clearWords active 7168 n =
      if n = 0 then active else UInt256.ofNat (max active.toNat (224+n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n ≤ 32 := by omega
    have hoff := BigHelpers.clearOffset_toNat 7168 n (by omega)
    have hlast : (7168 + 32*n + 32 - 1) / 32 + 1 = 224+(n+1) := by omega
    rw [BigHelpers.clearWords]
    change UInt256.ofNat (MachineState.activeWordsAfter
      (BigHelpers.clearWords active 7168 n).toNat
      (BigHelpers.clearOffset (UInt256.ofNat 7168) n).toNat 32) = _
    rw [hoff]
    simp only [MachineState.activeWordsAfter, show (32 : Nat) ≠ 0 by decide,
      if_false, hlast, ih hn, Nat.succ_ne_zero]
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hmax : max active.toNat (224+n) < 2^256 := by
        have ha : active.toNat < 2^256 := active.val.isLt
        omega
      simp only [hn0, if_false, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmax,
        Nat.max_assoc]
      rw [Nat.max_eq_right (show 224+n ≤ 224+(n+1) by omega)]

theorem clearWords_toNat (active : UInt256) (n : Nat) (hn : 1 ≤ n) (hN : n ≤ 32) :
    (BigHelpers.clearWords active 7168 n).toNat = max active.toNat (224+n) := by
  rw [clearWords_eq active n hN, if_neg (by omega), Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have ha : active.toNat < 2^256 := active.val.isLt
  omega

theorem topTouch_clearWords (active : UInt256) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) :
    UInt256.ofNat (MachineState.activeWordsAfter
      (BigHelpers.clearWords active 7168 n).toNat (32*(n-1)) 32) =
        BigHelpers.clearWords active 7168 n := by
  have hlast : (32*(n-1)+32-1)/32+1 = n := by omega
  rw [clearWords_toNat active n hn hN, clearWords_eq active n hN,
    if_neg (by omega)]
  simp only [MachineState.activeWordsAfter, show (32 : Nat) ≠ 0 by decide,
    if_false, hlast, Nat.max_assoc]
  rw [Nat.max_eq_left (show n ≤ 224+n by omega)]

end MemoryBounds


open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp (submissionBytecode)

theorem progress_flat (s : State) (n i : Nat) :
    progress s n i =
      { s with memory := (progress s n i).memory
               activeWords := (progress s n i).activeWords } := by
  induction i with
  | zero => cases s; rfl
  | succ i ih =>
    dsimp only [progress, doubleLeaf]
    conv_lhs => rw [ih]
    rfl

@[simp] theorem progress_env (s : State) (n i : Nat) :
    (progress s n i).executionEnv = s.executionEnv := by
  rw [progress_flat]
@[simp] theorem progress_halt (s : State) (n i : Nat) :
    (progress s n i).halt = s.halt := by
  rw [progress_flat]
@[simp] theorem progress_fork (s : State) (n i : Nat) :
    (progress s n i).fork = s.fork := by
  simp [State.fork]

theorem returned_frame (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) :
    { returned s n ret saved with
      pc := s.pc
      stack := s.stack
      memory := s.memory
      activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem touched_clear (s : State) (n : Nat) (hn : 1 ≤ n) (hN : n ≤ 32) :
    touched (clearLeaf s n) n = clearLeaf s n := by
  unfold touched clearLeaf
  rw [MemoryBounds.topTouch_clearWords s.activeWords n hn hN]

theorem returned_fast (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hfast : 2^255 ≤ (top (clearLeaf s n) n).toNat) :
    returned s n ret saved =
      { reduceLeaf (touched (clearLeaf s n) n) n 1 with pc := ret, stack := saved } := by
  simp only [returned, if_pos hfast]
  rfl

theorem returned_slow (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hslow : ¬ 2^255 ≤ (top (clearLeaf s n) n).toNat) :
    returned s n ret saved =
      { progress (reduceLeaf (seedLeaf (touched (clearLeaf s n) n)) n 0) n (256*n) with
        pc := ret, stack := saved } := by
  simp only [returned, if_neg hslow]
  conv_rhs => rw [progress_flat]
  rfl

def gasSteps_clearCall (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (BigHelpers.clearEntry s 7168 n 1798 (frame n ret saved))
      (atFrame (clearLeaf s n) n ret saved 1798) := by
  exact BigHelpers.gasSteps_clear s 7168 n 1798 (frame n ret saved)
    (by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hcode hfork hrun hnp
    (Artifact.isValidJumpDest_index 1337 (by rfl))

def gasSteps_reduceCall (s : State) (n : Nat) (high : UInt256) (k : Nat)
    (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hk : Decode.isValidJumpDest submissionBytecode (UInt256.ofNat k).toNat = true) :
    GasSteps (MontgomeryReduceBlock.reduceEntry s 7168 0 high n (UInt256.ofNat k) (frame n ret saved))
      (atFrame (reduceLeaf s n high) n ret saved k) := by
  exact MontgomeryReduceBlock.gasSteps_reduce s 7168 0 high n (UInt256.ofNat k) (frame n ret saved)
    (by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hcode hfork hrun hnp hk

def gasSteps_doubleCall (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (BigHelpers.addEntry s 7168 7168 1 0 n 1890
        (UInt256.ofNat i :: frame n ret saved))
      (atLoop (doubleLeaf s n) n i ret saved 1890) := by
  exact BigHelpers.gasSteps_addMaskedMod s 7168 7168 1 0 n 1890
    (UInt256.ofNat i :: frame n ret saved)
    (by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hcode hfork hrun hnp
    (Artifact.isValidJumpDest_index 1397 (by rfl))

def gasSteps_iteration (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hN : n ≤ 32) (hi : i < 256*n)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loop s n i ret saved) (loop s n (i+1) ret saved) := by
  let p := progress s n i
  have hc : p.executionEnv.code = submissionBytecode := by simpa [p] using hcode
  have hf : p.fork = .Osaka := by simpa [p] using hfork
  have hr : p.halt = .Running := by simpa [p] using hrun
  have hp : Precompile.isPrecompileWithConfig p.executionEnv.precompileConfig
      p.executionEnv.fork p.executionEnv.codeAddr = false := by simpa [p] using hnp
  exact (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    (s := atLoop p n i ret saved 1862) hc hf
    (run_guard p n i ret saved hcap hN hi hr) hr hp).trans <|
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka bodyPath
      (s := atLoop p n i ret saved 1875) hc hf
      (run_body p n i ret saved hcap hc hr) hr hp).trans <|
    (gasSteps_doubleCall p n i ret saved hcap hN hc hf hr hp).trans <|
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka nextPath
      (s := atLoop (doubleLeaf p n) n i ret saved 1890) hc hf
      (run_next (doubleLeaf p n) n i ret saved hcap hc hr) hr hp)

def gasSteps_slowFinish (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (atFrame s n ret saved 1860)
      { progress s n (256*n) with pc := ret, stack := saved } := by
  let p := progress s n (256*n)
  have hc : p.executionEnv.code = submissionBytecode := by simpa [p] using hcode
  have hf : p.fork = .Osaka := by simpa [p] using hfork
  have hr : p.halt = .Running := by simpa [p] using hrun
  have hp : Precompile.isPrecompileWithConfig p.executionEnv.precompileConfig
      p.executionEnv.fork p.executionEnv.codeAddr = false := by simpa [p] using hnp
  exact (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka loopSetupPath
    (s := atFrame s n ret saved 1860) hcode hfork
    (run_loopSetup s n ret saved hcap hrun) hrun hnp).trans <|
    (GasSteps.iterateBounded (256*n) (fun i hi =>
      gasSteps_iteration s n i ret saved hcap hN hi hcode hfork hrun hnp)).trans <|
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
      (s := atLoop p n (256*n) ret saved 1862) hc hf
      (run_guard_finish p n ret saved hcap hc hr) hr hp).trans <|
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka exitPath
      (s := atLoop p n (256*n) ret saved 1898) hc hf
      (run_exit p n (256*n) ret saved hcap hr) hr hp).trans <|
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka donePath
      (s := atFrame p n ret saved 1900) hc hf
      (run_done p n ret saved hcap hc hr hret) hr hp

def gasSteps_unit (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (entry s n ret saved) (returned s n ret saved) := by
  let c := clearLeaf s n
  let t := touched c n
  have start := (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka clearPath
    (s := entry s n ret saved) hcode hfork
    (run_clear s n ret saved hcap hcode hrun) hrun hnp).trans
    (gasSteps_clearCall s n ret saved hcap hN hcode hfork hrun hnp)
  have test := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka testPath
    (s := atFrame c n ret saved 1798) hcode hfork
    (run_test c n ret saved hcap hn hN hcode hrun) hrun hnp
  by_cases hfast : 2^255 ≤ (top c n).toNat
  · rw [returned_fast s n ret saved hfast]
    have tf : GasSteps (atFrame c n ret saved 1798) (atFrame t n ret saved 1840) := by
      simpa only [if_pos hfast] using test
    exact start.trans <| tf.trans <|
      (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka fastPath
        (s := atFrame t n ret saved 1840) hcode hfork
        (run_fast t n ret saved hcap hcode hrun) hrun hnp).trans <|
      (gasSteps_reduceCall t n 1 1900 ret saved hcap hN hcode hfork hrun hnp
        (Artifact.isValidJumpDest_index 1404 (by rfl))).trans <|
      Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka donePath
        (s := atFrame (reduceLeaf t n 1) n ret saved 1900) hcode hfork
        (run_done (reduceLeaf t n 1) n ret saved hcap hcode hrun hret) hrun hnp
  · rw [returned_slow s n ret saved hfast]
    have ts : GasSteps (atFrame c n ret saved 1798) (atFrame t n ret saved 1816) := by
      simpa only [if_neg hfast] using test
    exact start.trans <| ts.trans <|
      (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka seedPath
        (s := atFrame t n ret saved 1816) hcode hfork
        (run_seed t n ret saved hcap hcode hrun) hrun hnp).trans <|
      (gasSteps_reduceCall (seedLeaf t) n 0 1860 ret saved hcap hN hcode hfork hrun hnp
        (Artifact.isValidJumpDest_index 1378 (by rfl))).trans <|
      gasSteps_slowFinish (reduceLeaf (seedLeaf t) n 0) n ret saved
        hcap hN hcode hfork hrun hnp hret

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneBlock
