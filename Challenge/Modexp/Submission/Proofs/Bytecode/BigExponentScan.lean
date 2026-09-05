import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Leading-zero-bit scan before multi-limb exponentiation -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScan

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
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def startPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 990 .JUMPDEST, pushAt 991 0 0]

def byteGuardPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 992 .JUMPDEST, opAt 993 (.Dup ⟨4, by decide⟩),
   opAt 994 (.Dup ⟨1, by decide⟩), opAt 995 .EQ,
   pushAt 996 2 946, opAt 997 .JUMPI]

def loadBytePath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 998 (.Dup ⟨7, by decide⟩), opAt 999 (.Dup ⟨1, by decide⟩),
   opAt 1000 .ADD, opAt 1001 (.Dup ⟨0, by decide⟩),
   opAt 1002 .CALLDATALOAD, pushAt 1003 0 0, opAt 1004 .BYTE,
   opAt 1005 (.Dup ⟨0, by decide⟩), opAt 1006 .ISZERO,
   pushAt 1007 2 1385, opAt 1008 .JUMPI]

def startBitsPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) := [pushAt 1009 0 0]

def bitTestPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1010 .JUMPDEST, pushAt 1011 1 1,
   opAt 1012 (.Dup ⟨2, by decide⟩), opAt 1013 (.Dup ⟨2, by decide⟩),
   pushAt 1014 1 7, opAt 1015 .SUB, opAt 1016 .SHR, opAt 1017 .AND,
   pushAt 1018 2 1380, opAt 1019 .JUMPI]

def bitAdvancePath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [pushAt 1020 1 1, opAt 1021 .ADD, pushAt 1022 2 1359,
   opAt 1023 .JUMP]

def bitFoundPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1024 .JUMPDEST, pushAt 1025 2 1395, opAt 1026 .JUMP]

def zeroBytePath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1027 .JUMPDEST, opAt 1028 .POP, opAt 1029 .POP,
   pushAt 1030 1 1, opAt 1031 .ADD, pushAt 1032 2 1337,
   opAt 1033 .JUMP]

def copyCallPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1034 .JUMPDEST, pushAt 1035 2 1410,
   opAt 1036 (.Dup ⟨6, by decide⟩), pushAt 1037 2 1024,
   pushAt 1038 2 2048, pushAt 1039 2 58, opAt 1040 .JUMP]

def copyReturnPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1041 .JUMPDEST, pushAt 1042 1 1, opAt 1043 .ADD,
   pushAt 1044 2 963, opAt 1045 .JUMP]

def scanEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1335
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def byteLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 1337
           stack := [UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def byteBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { byteLoop s accumulatorWord count b e m baseOff expOff rest i with
      pc := UInt256.ofNat 1345 }

def loadedOffset (expOff i : Nat) : UInt256 := UInt256.ofNat (expOff + i)

def loadedByte (s : State) (expOff i : Nat) : UInt256 :=
  BigExponent.loadedExponentByte s expOff i

def bitStartEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1358
           stack := [loadedByte s expOff i, loadedOffset expOff i,
             UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def zeroByteEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256) : State :=
  { bitStartEntry s accumulatorWord count b e m baseOff expOff i rest with
      pc := UInt256.ofNat 1385 }

def bitLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1359
           stack := [UInt256.ofNat j, loadedByte s expOff i,
             loadedOffset expOff i, UInt256.ofNat i, accumulatorWord,
             UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e,
             UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def bitAdvanceEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  { bitLoop s accumulatorWord count b e m baseOff expOff i j rest with
      pc := UInt256.ofNat 1373 }

def bitFoundEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  { bitLoop s accumulatorWord count b e m baseOff expOff i j rest with
      pc := UInt256.ofNat 1380 }

def copyTailFrame (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
    UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest

def copyEntryState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  { bitLoop s accumulatorWord count b e m baseOff expOff i j rest with
      pc := UInt256.ofNat 1395 }

def copiedState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  BigHelpers.copyReturned
    (copyEntryState s accumulatorWord count b e m baseOff expOff i j rest)
    2048 1024 count 1410
    (copyTailFrame accumulatorWord count b e m baseOff expOff i j
      (loadedOffset expOff i) (loadedByte s expOff i) rest)

@[simp] private theorem scannerPCs (i : Nat) (hi : 990 ≤ i)
    (hii : i ≤ 1045) : Artifact.submissionArtifact.instructionPC i =
      ([1335,1336,1337,1338,1339,1340,1341,1344,1345,1346,1347,1348,
        1349,1350,1351,1352,1353,1354,1357,1358,1359,1360,1362,1363,
        1364,1366,1367,1368,1369,1372,1373,1375,1376,1379,1380,1381,
        1384,1385,1386,1387,1388,1390,1391,1394,1395,1396,1399,1400,
        1403,1406,1409,1410,1411,1413,1414,1417])[i - 990]! := by
  interval_cases i <;> decide

private theorem jump946 : Decode.isValidJumpDest submissionBytecode 946 = true :=
  Artifact.isValidJumpDest_index 719 (by rfl)
private theorem jump963 : Decode.isValidJumpDest submissionBytecode 963 = true :=
  Artifact.isValidJumpDest_index 734 (by rfl)
private theorem jump1337 : Decode.isValidJumpDest submissionBytecode 1337 = true :=
  Artifact.isValidJumpDest_index 992 (by rfl)
private theorem jump1359 : Decode.isValidJumpDest submissionBytecode 1359 = true :=
  Artifact.isValidJumpDest_index 1010 (by rfl)
private theorem jump1380 : Decode.isValidJumpDest submissionBytecode 1380 = true :=
  Artifact.isValidJumpDest_index 1024 (by rfl)
private theorem jump1385 : Decode.isValidJumpDest submissionBytecode 1385 = true :=
  Artifact.isValidJumpDest_index 1027 (by rfl)
private theorem jump1395 : Decode.isValidJumpDest submissionBytecode 1395 = true :=
  Artifact.isValidJumpDest_index 1034 (by rfl)
theorem jump1410 : Decode.isValidJumpDest submissionBytecode 1410 = true :=
  Artifact.isValidJumpDest_index 1041 (by rfl)
private theorem jump58 : Decode.isValidJumpDest submissionBytecode 58 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)

theorem run_start (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startPath
      (scanEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (byteLoop s accumulatorWord count b e m baseOff expOff rest 0) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [startPath, opAt, pushAt, wfOp, scanEntry, byteLoop, scannerPCs,
    hrun, hzero, hc7, hc8, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_byteGuardFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteGuardPath
      (byteLoop s accumulatorWord count b e m baseOff expOff rest e) =
      some (BigExponent.outerLoop s accumulatorWord count b e m baseOff expOff
        rest e) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have heNat : (UInt256.ofNat e).toNat = e := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt he]
  have heq : UInt256.eq (UInt256.ofNat e) (UInt256.ofNat e) = 1 := by
    rw [UInt256.eq, heNat, if_pos rfl]
    decide
  have h1Nat : (1 : UInt256).toNat = 1 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h946 : (946 : UInt256).toNat = 946 := by decide
  have h946Word : (946 : UInt256) = UInt256.ofNat 946 := by decide
  simp [byteGuardPath, opAt, pushAt, wfOp, byteLoop, BigExponent.outerLoop,
    scannerPCs, hcode, hrun, heq, heNat, h1Nat, h1Word, h946, h946Word,
    jump946,
    hc8, hc9, hc10, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_byteGuardContinue (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (he : e < 2 ^ 256) (hi : i < e)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteGuardPath
      (byteLoop s accumulatorWord count b e m baseOff expOff rest i) =
      some (byteBody s accumulatorWord count b e m baseOff expOff rest i) := by
  have hi256 : i < 2 ^ 256 := hi.trans he
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hne : UInt256.eq (UInt256.ofNat i) (UInt256.ofNat e) = 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt he, if_neg (by omega)]
    decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  simp [byteGuardPath, opAt, pushAt, wfOp, byteLoop, byteBody, scannerPCs,
    hrun, hne, hzeroNat, hc8, hc9, hc10, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_loadByteZero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1010) (hoff : expOff + i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) (hbyte : (loadedByte s expOff i).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadBytePath
      (byteBody s accumulatorWord count b e m baseOff expOff rest i) =
      some (zeroByteEntry s accumulatorWord count b e m baseOff expOff i
        rest) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := expOff) (by omega)
  have hoffNat : (UInt256.ofNat (expOff + i)).toNat = expOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hz : (UInt256.isZero (loadedByte s expOff i)).toNat = 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero, if_pos hbyte]
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have hbyteRaw :
      ((UInt256.ofNat 0).byteAt
        (MachineState.readWord s.executionEnv.calldata (expOff + i))).toNat = 0 := by
    simpa [loadedByte, BigExponent.loadedExponentByte, h0Word] using hbyte
  have h1385 : (1385 : UInt256).toNat = 1385 := by decide
  have h1385Word : (1385 : UInt256) = UInt256.ofNat 1385 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [loadBytePath, opAt, pushAt, wfOp, byteBody, byteLoop,
    zeroByteEntry, bitStartEntry, loadedByte, loadedOffset,
    BigExponent.loadedExponentByte, scannerPCs, hcode, hrun, hadd, hoffNat,
    hbyte, hbyteRaw, hz, h0Word, h1385, h1385Word, hzero, jump1385,
    hc8, hc9, hc10, hc11, hc12, hc13, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem run_loadByteNonzero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1010) (hoff : expOff + i < 2 ^ 256)
    (hrun : s.halt = .Running) (hbyte : (loadedByte s expOff i).toNat ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadBytePath
      (byteBody s accumulatorWord count b e m baseOff expOff rest i) =
      some (bitStartEntry s accumulatorWord count b e m baseOff expOff i
        rest) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := expOff) (by omega)
  have hoffNat : (UInt256.ofNat (expOff + i)).toNat = expOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hz : (UInt256.isZero (loadedByte s expOff i)).toNat = 0 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero, if_neg hbyte]
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have hbyteRaw :
      ((UInt256.ofNat 0).byteAt
        (MachineState.readWord s.executionEnv.calldata (expOff + i))).toNat ≠ 0 := by
    simpa [loadedByte, BigExponent.loadedExponentByte, h0Word] using hbyte
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [loadBytePath, opAt, pushAt, wfOp, byteBody, byteLoop,
    bitStartEntry, loadedByte, loadedOffset, BigExponent.loadedExponentByte,
    scannerPCs, hrun, hadd, hoffNat, hbyte, hbyteRaw, hz, h0Word, hzero,
    hc8, hc9, hc10, hc11, hc12, hc13, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem run_startBits (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1013) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startBitsPath
      (bitStartEntry s accumulatorWord count b e m baseOff expOff i rest) =
      some (bitLoop s accumulatorWord count b e m baseOff expOff i 0 rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [startBitsPath, opAt, pushAt, wfOp, bitStartEntry, bitLoop,
    scannerPCs, hrun, hzero, hc10, hc11,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_bitTestZero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 1008) (hj : j < 8) (hrun : s.halt = .Running)
    (hbit : (BigExponent.exponentBit (loadedByte s expOff i) j).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitTestPath
      (bitLoop s accumulatorWord count b e m baseOff expOff i j rest) =
      some (bitAdvanceEntry s accumulatorWord count b e m baseOff expOff i j
        rest) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (by omega : j ≤ 7) (by norm_num : 7 < 2 ^ 256)
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hbitRaw :
      ((BigExponent.loadedExponentByte s expOff i).shiftRight
        (UInt256.ofNat (7 - j))).toNat % 2 = 0 := by
    rw [BigExponent.exponentBit,
      Challenge.EvmProof.Word.word_toNat_land,
      show (1 : UInt256).toNat = 1 by decide,
      Nat.and_one_is_mod] at hbit
    simpa [loadedByte] using hbit
  simp [bitTestPath, opAt, pushAt, wfOp, bitLoop, bitAdvanceEntry,
    BigExponent.exponentBit, loadedByte, loadedOffset, scannerPCs, hrun,
    hsub, hbitRaw, hone, hseven, hzeroNat, hc11, hc12, hc13, hc14, hc15,
    UInt256.isTrue, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_bitTestSet (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 1008) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hbit : (BigExponent.exponentBit (loadedByte s expOff i) j).toNat ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitTestPath
      (bitLoop s accumulatorWord count b e m baseOff expOff i j rest) =
      some (bitFoundEntry s accumulatorWord count b e m baseOff expOff i j
        rest) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (by omega : j ≤ 7) (by norm_num : 7 < 2 ^ 256)
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  have h1380 : (1380 : UInt256).toNat = 1380 := by decide
  have h1380Word : (1380 : UInt256) = UInt256.ofNat 1380 := by decide
  have hbitRaw :
      ((BigExponent.loadedExponentByte s expOff i).shiftRight
        (UInt256.ofNat (7 - j))).toNat % 2 = 1 := by
    rw [BigExponent.exponentBit,
      Challenge.EvmProof.Word.word_toNat_land,
      show (1 : UInt256).toNat = 1 by decide,
      Nat.and_one_is_mod] at hbit
    simpa [loadedByte] using (show
      ((loadedByte s expOff i).shiftRight
        (UInt256.ofNat (7 - j))).toNat % 2 = 1 by omega)
  simp [bitTestPath, opAt, pushAt, wfOp, bitLoop, bitFoundEntry,
    BigExponent.exponentBit, loadedByte, loadedOffset, scannerPCs, hcode, hrun,
    hsub, hbitRaw, hone, hseven, h1380, h1380Word, jump1380,
    hc11, hc12, hc13, hc14, hc15, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_bitAdvance (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 1011) (hj : j + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath
      (bitAdvanceEntry s accumulatorWord count b e m baseOff expOff i j rest) =
      some (bitLoop s accumulatorWord count b e m baseOff expOff i (j + 1)
        rest) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := j) (b := 1) hj
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have h1359 : (1359 : UInt256).toNat = 1359 := by decide
  have h1359Word : (1359 : UInt256) = UInt256.ofNat 1359 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have haddComm : UInt256.ofNat (1 + j) = UInt256.ofNat (j + 1) := by
    rw [Nat.add_comm]
  simp [bitAdvancePath, opAt, pushAt, wfOp, bitAdvanceEntry, bitLoop,
    scannerPCs, hcode, hrun, hinc, haddComm, h1359, h1359Word, hone, jump1359,
    hc11, hc12, hc13, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_bitFound (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFoundPath
      (bitFoundEntry s accumulatorWord count b e m baseOff expOff i j rest) =
      some (copyEntryState s accumulatorWord count b e m baseOff expOff i j
        rest) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h1395 : (1395 : UInt256).toNat = 1395 := by decide
  have h1395Word : (1395 : UInt256) = UInt256.ofNat 1395 := by decide
  simp [bitFoundPath, opAt, pushAt, wfOp, bitFoundEntry, bitLoop,
    copyEntryState, scannerPCs, hcode, hrun, h1395, h1395Word, jump1395,
    hc11, hc12, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_copyCall (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyCallPath
      (copyEntryState s accumulatorWord count b e m baseOff expOff i j rest) =
      some (BigHelpers.copyEntry
        (copyEntryState s accumulatorWord count b e m baseOff expOff i j rest)
        2048 1024 count 1410
        (copyTailFrame accumulatorWord count b e m baseOff expOff i
          j (loadedOffset expOff i) (loadedByte s expOff i) rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h58 : (58 : UInt256).toNat = 58 := by decide
  have h58Word : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have hret : (1410 : UInt256) = UInt256.ofNat 1410 := by decide
  simp [copyCallPath, opAt, pushAt, wfOp, copyEntryState, bitLoop,
    BigHelpers.copyEntry, copyTailFrame, scannerPCs, hcode, hrun,
    jump58, h58, h58Word, hret, hc11, hc12, hc13, hc14, hc15, hc16,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_copyReturn (t : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005)
    (hpc : t.pc = UInt256.ofNat 1410)
    (hstack : t.stack = copyTailFrame accumulatorWord count b e m
      baseOff expOff i j offset byte rest)
    (hcode : t.executionEnv.code = submissionBytecode)
    (hrun : t.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyReturnPath t =
      some (BigExponent.innerLoop t accumulatorWord count b e m baseOff expOff
        i offset byte rest (j + 1)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hinc : (1 : UInt256) + UInt256.ofNat j = UInt256.ofNat (j + 1) := by
    rw [show (1 : UInt256) = UInt256.ofNat 1 from by decide,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_comm 1 j]
  have h963 : (963 : UInt256).toNat = 963 := by decide
  have h963Word : (963 : UInt256) = UInt256.ofNat 963 := by decide
  simp [copyReturnPath, opAt, pushAt, wfOp, copyTailFrame,
    BigExponent.innerLoop, scannerPCs, hpc, hstack, hcode, hrun, jump963,
    h963, h963Word, hinc, hc11, hc12,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_zeroByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1011) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroBytePath
      (zeroByteEntry s accumulatorWord count b e m baseOff expOff i rest) =
      some (byteLoop s accumulatorWord count b e m baseOff expOff rest
        (i + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := i) (b := 1) hi
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h1337 : (1337 : UInt256).toNat = 1337 := by decide
  have h1337Word : (1337 : UInt256) = UInt256.ofNat 1337 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have haddComm : UInt256.ofNat (1 + i) = UInt256.ofNat (i + 1) := by
    rw [Nat.add_comm]
  simp [zeroBytePath, opAt, pushAt, wfOp, zeroByteEntry, bitStartEntry,
    byteLoop, scannerPCs, hcode, hrun, hinc, h1337, h1337Word, hone,
    haddComm, jump1337, hc8, hc9, hc10, hc11, hc12,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScan
