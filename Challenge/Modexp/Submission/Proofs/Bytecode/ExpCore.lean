import Challenge.Modexp.Submission.Proofs.Bytecode.BitPrefix
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport.InitialState
import Challenge.Modexp.Submission.Proofs.Bytecode.BigMul
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 10000000

/-!
# Square-and-multiply exponent loop: paths, frames and block lemmas

The patched artifact routes the exponent loop out of the original region
(instructions 717..837, now a stub plus unreachable filler) into appended code
at instructions 961..1074. A `started` flag sits directly below the loop
counter `i`, so every frame below it is one slot deeper than in the reference.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ExpCore

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
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

/-! ## Paths -/

/-- The neutralized region's stub: jump straight to the appended loop. -/
def startExponentPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 717 .JUMPDEST, pushAt 718 2 1284, opAt 719 .JUMP]

def startExponentBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 961 .JUMPDEST,
   pushAt 962 0 0,
   pushAt 963 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 964 .JUMPDEST,
   opAt 965 (.Dup ⟨5, by decide⟩),
   opAt 966 (.Dup ⟨1, by decide⟩),
   opAt 967 .LT,
   opAt 968 .ISZERO,
   pushAt 969 2 1453,
   opAt 970 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 971 (.Dup ⟨0, by decide⟩),
   opAt 972 (.Dup ⟨9, by decide⟩),
   opAt 973 .ADD,
   opAt 974 (.Dup ⟨0, by decide⟩),
   opAt 975 .CALLDATALOAD,
   pushAt 976 0 0,
   opAt 977 .BYTE,
   pushAt 978 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 979 .JUMPDEST,
   pushAt 980 1 8,
   opAt 981 (.Dup ⟨1, by decide⟩),
   opAt 982 .LT,
   opAt 983 .ISZERO,
   pushAt 984 2 1442,
   opAt 985 .JUMPI]


def bitAndStartedTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 986 1 1,
   opAt 987 (.Dup ⟨2, by decide⟩),
   opAt 988 (.Dup ⟨2, by decide⟩),
   pushAt 989 1 7,
   opAt 990 .SUB,
   opAt 991 .SHR,
   opAt 992 .AND,
   opAt 993 (.Dup ⟨5, by decide⟩),
   opAt 994 .ISZERO,
   pushAt 995 2 1407,
   opAt 996 .JUMPI]

def bitTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1012 .JUMPDEST,
   opAt 1013 (.Dup ⟨0, by decide⟩),
   opAt 1014 .ISZERO,
   pushAt 1015 2 1433,
   opAt 1016 .JUMPI]

def notStartedBitTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1035 .JUMPDEST,
   opAt 1036 (.Dup ⟨0, by decide⟩),
   opAt 1037 .ISZERO,
   pushAt 1038 2 1433,
   opAt 1039 .JUMPI]

def setStartedPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1046 .JUMPDEST,
   pushAt 1047 1 1,
   opAt 1048 (.Swap ⟨5, by decide⟩),
   opAt 1049 .POP]

def incJPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1050 .JUMPDEST,
   opAt 1051 .POP,
   pushAt 1052 1 1,
   opAt 1053 .ADD,
   pushAt 1054 2 1304,
   opAt 1055 .JUMP]

def nextBytePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1056 .JUMPDEST,
   opAt 1057 .POP,
   opAt 1058 .POP,
   opAt 1059 .POP,
   pushAt 1060 1 1,
   opAt 1061 .ADD,
   pushAt 1062 2 1287,
   opAt 1063 .JUMP]

def exponentExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1064 .JUMPDEST,
   opAt 1065 (.Swap ⟨0, by decide⟩),
   opAt 1066 .POP,
   pushAt 1067 2 1118,
   opAt 1068 .JUMP]

def squareCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 997 2 1347,
   opAt 998 (.Dup ⟨8, by decide⟩),
   pushAt 999 0 0,
   pushAt 1000 2 3072,
   pushAt 1001 2 2048,
   pushAt 1002 2 2048,
   pushAt 1003 2 310,
   opAt 1004 .JUMP]

def squareToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1005 .JUMPDEST,
   pushAt 1006 2 1362,
   opAt 1007 (.Dup ⟨8, by decide⟩),
   pushAt 1008 2 3072,
   pushAt 1009 2 2048,
   pushAt 1010 2 58,
   opAt 1011 .JUMP]

def productCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1017 2 1387,
   opAt 1018 (.Dup ⟨8, by decide⟩),
   pushAt 1019 0 0,
   pushAt 1020 2 3072,
   pushAt 1021 2 1024,
   pushAt 1022 2 2048,
   pushAt 1023 2 310,
   opAt 1024 .JUMP]

def productToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1025 .JUMPDEST,
   pushAt 1026 2 1402,
   opAt 1027 (.Dup ⟨8, by decide⟩),
   pushAt 1028 2 3072,
   pushAt 1029 2 2048,
   pushAt 1030 2 58,
   opAt 1031 .JUMP]

def afterProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1032 .JUMPDEST,
   pushAt 1033 2 1433,
   opAt 1034 .JUMP]

def seedCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1040 2 1428,
   opAt 1041 (.Dup ⟨8, by decide⟩),
   pushAt 1042 2 1024,
   pushAt 1043 2 2048,
   pushAt 1044 2 58,
   opAt 1045 .JUMP]

/-! ## Instruction addresses -/

@[simp] private theorem stubPCs (i : Nat) (hi : 717 ≤ i) (hii : i ≤ 719) :
    Artifact.submissionArtifact.instructionPC i = ([944, 945, 948])[i - 717]! := by
  interval_cases i <;> decide

@[simp] private theorem appendedPCs (i : Nat) (hi : 961 ≤ i)
    (hii : i ≤ 1068) :
    Artifact.submissionArtifact.instructionPC i =
      ([1284,1285,1286,1287,1288,1289,1290,1291,1292,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1307,1308,1309,1310,1313,1314,1316,1317,1318,1320,1321,1322,1323,1324,1325,1328,1329,1332,1333,1334,1337,1340,1343,1346,1347,1348,1351,1352,1355,1358,1361,1362,1363,1364,1365,1368,1369,1372,1373,1374,1377,1380,1383,1386,1387,1388,1391,1392,1395,1398,1401,1402,1403,1406,1407,1408,1409,1410,1413,1414,1417,1418,1421,1424,1427,1428,1429,1431,1432,1433,1434,1435,1437,1438,1441,1442,1443,1444,1445,1446,1448,1449,1452,1453,1454,1455,1456,1459])[i - 961]! := by
  interval_cases i <;> decide

private theorem jump1284 :
    Decode.isValidJumpDest submissionBytecode 1284 = true :=
  Artifact.isValidJumpDest_index 961 (by rfl)

private theorem jump1453 :
    Decode.isValidJumpDest submissionBytecode 1453 = true :=
  Artifact.isValidJumpDest_index 1064 (by rfl)


private theorem jump1407 :
    Decode.isValidJumpDest submissionBytecode 1407 = true :=
  Artifact.isValidJumpDest_index 1035 (by rfl)

private theorem jump1433 :
    Decode.isValidJumpDest submissionBytecode 1433 = true :=
  Artifact.isValidJumpDest_index 1050 (by rfl)

private theorem jump1442 :
    Decode.isValidJumpDest submissionBytecode 1442 = true :=
  Artifact.isValidJumpDest_index 1056 (by rfl)

private theorem jump1304 :
    Decode.isValidJumpDest submissionBytecode 1304 = true :=
  Artifact.isValidJumpDest_index 979 (by rfl)

private theorem jump1287 :
    Decode.isValidJumpDest submissionBytecode 1287 = true :=
  Artifact.isValidJumpDest_index 964 (by rfl)

private theorem jump310 :
    Decode.isValidJumpDest submissionBytecode 310 = true :=
  Artifact.isValidJumpDest_index 262 (by rfl)

private theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 58 = true :=
  Artifact.isValidJumpDest_index 43 (by rfl)

private theorem jump1347 :
    Decode.isValidJumpDest submissionBytecode 1347 = true :=
  Artifact.isValidJumpDest_index 1005 (by rfl)

private theorem jump1362 :
    Decode.isValidJumpDest submissionBytecode 1362 = true :=
  Artifact.isValidJumpDest_index 1012 (by rfl)

private theorem jump1387 :
    Decode.isValidJumpDest submissionBytecode 1387 = true :=
  Artifact.isValidJumpDest_index 1025 (by rfl)

private theorem jump1402 :
    Decode.isValidJumpDest submissionBytecode 1402 = true :=
  Artifact.isValidJumpDest_index 1032 (by rfl)

private theorem jump1428 :
    Decode.isValidJumpDest submissionBytecode 1428 = true :=
  Artifact.isValidJumpDest_index 1046 (by rfl)

private theorem jump1118 :
    Decode.isValidJumpDest submissionBytecode 1118 = true :=
  Artifact.isValidJumpDest_index 838 (by rfl)

/-! ## Frames

`accumulatorWord`, `count`, `b`, `e`, `m`, `baseOff`, `expOff` are the seven
named slots the reference already carries; `rest` is the enclosing frame.
`started` is new and sits directly below `i`. -/

def exponentEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 944
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

/-- Same frame, now at the head of the appended loop. -/
def appendedEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { exponentEntry s accumulatorWord count b e m baseOff expOff rest with
      pc := UInt256.ofNat 1284 }

/-- Top of the outer loop. -/
def outerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) : State :=
  { s with pc := UInt256.ofNat 1287
           stack := [UInt256.ofNat i, UInt256.ofNat started, accumulatorWord,
             UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e,
             UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

/-- Outer loop, guard passed. -/
def outerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest started i with
      pc := UInt256.ofNat 1296 }

/-! ## Block lemmas -/

set_option linter.unusedSimpArgs false in
theorem run_startExponent (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startExponentPath
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (appendedEntry s accumulatorWord count b e m baseOff expOff rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hdest : (1284 : UInt256).toNat = 1284 := by decide
  have hdestWord : (1284 : UInt256) = UInt256.ofNat 1284 := by decide
  simp [startExponentPath, opAt, pushAt, wfOp, exponentEntry, appendedEntry,
    stubPCs, hcode, hrun, hc7, hc8, hdest, hdestWord, jump1284,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_startExponentBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1015) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startExponentBodyPath
      (appendedEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (outerLoop s accumulatorWord count b e m baseOff expOff rest 0 0) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [startExponentBodyPath, opAt, pushAt, wfOp, appendedEntry, exponentEntry,
    outerLoop, appendedPCs, hrun, hzero, hc7, hc8, hc9,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (hcap : rest.length < 1012) (he : e < 2 ^ 256) (hi : i < e)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulatorWord count b e m baseOff expOff rest started i) =
      some (outerBody s accumulatorWord count b e m baseOff expOff rest started i) := by
  have hi256 : i < 2 ^ 256 := hi.trans he
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat e) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt he, if_pos hi]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerBody,
    appendedPCs, hrun, hlt, honeNat, hc9, hc10, hc11, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def loadedExponentByte (s : State) (expOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (expOff + i))

/-- Top of the inner (bit) loop. -/
def innerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 1304
           stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i,
             UInt256.ofNat started, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_outerToInner (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (hcap : rest.length < 1010) (hoff : expOff + i < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerToInnerPath
      (outerBody s accumulatorWord count b e m baseOff expOff rest started i) =
      some (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
        (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) 0) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := expOff) (by omega)
  have hoffNat : (UInt256.ofNat (expOff + i)).toNat = expOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [outerToInnerPath, opAt, pushAt, wfOp, outerBody, outerLoop,
    innerLoop, loadedExponentByte, appendedPCs, hrun, hadd, hoffNat,
    hzero, h0Word, hc9, hc10, hc11, hc12,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

/-- Inner loop, guard passed: `j < 8`. -/
def innerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j with pc := UInt256.ofNat 1314 }

set_option linter.unusedSimpArgs false in
theorem run_innerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 1008) (hj : j < 8) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
        offset byte j) =
      some (innerBody s accumulatorWord count b e m baseOff expOff rest started i
        offset byte j) := by
  have hj256 : j < 2 ^ 256 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have height : (8 : UInt256) = UInt256.ofNat 8 := by decide
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 8) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hj256, Nat.mod_eq_of_lt (by norm_num : 8 < 2 ^ 256),
      if_pos hj]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerBody,
    appendedPCs, hrun, hlt, height, honeNat, hc12, hc13, hc14, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]


/-- The bit currently being consumed, most significant first. -/
def exponentBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) 1

/-- Stack once the bit has been computed: `bit` on top of the inner frame. -/
def bitFrame (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (rest : List UInt256) : List UInt256 :=
  [bit, UInt256.ofNat j, byte, offset, UInt256.ofNat i, UInt256.ofNat started,
    accumulatorWord, UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e,
    UInt256.ofNat m, UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest

/-- Head of the shared bit-increment tail (`INCJ`). -/
def incJEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 1433
           stack := bitFrame accumulatorWord count b e m baseOff expOff started i
             offset byte bit j rest }

/-- The seed copy has returned; `started` is about to be set. -/
def afterSeedCopy (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1428 }

/-- Inner loop exhausted; the exponent byte is about to be dropped. -/
def nextByteEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff rest started i
      offset byte 8 with pc := UInt256.ofNat 1442 }

/-- Outer loop exhausted. -/
def exponentDone (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest started e with
      pc := UInt256.ofNat 1453 }

/-- Hand-back to the untouched serializer at pc 1118: `started` is dropped, so
the frame is exactly the one the reference's `serializerEntry` expects. -/
def serializerHandoff (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1118
           stack := [UInt256.ofNat e, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_setStarted (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setStartedPath
      (afterSeedCopy s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (incJEntry s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte bit j) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [setStartedPath, opAt, pushAt, wfOp, afterSeedCopy, incJEntry, bitFrame,
    appendedPCs, hrun, honeWord, hc13, hc14,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_incJ (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hj : j + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock incJPath
      (incJEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
        offset byte (j + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := j) (b := 1) (by omega)
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hdest : (1304 : UInt256).toNat = 1304 := by decide
  have hdestWord : (1304 : UInt256) = UInt256.ofNat 1304 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [incJPath, opAt, pushAt, wfOp, incJEntry, innerLoop, bitFrame,
    appendedPCs, hcode, hrun, hinc, hdest, hdestWord, honeWord, jump1304,
    hc12, hc13, hc14,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_nextByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256)
    (hcap : rest.length < 1008) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock nextBytePath
      (nextByteEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte) =
      some (outerLoop s accumulatorWord count b e m baseOff expOff rest started
        (i + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := i) (b := 1) (by omega)
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hdest : (1287 : UInt256).toNat = 1287 := by decide
  have hdestWord : (1287 : UInt256) = UInt256.ofNat 1287 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [nextBytePath, opAt, pushAt, wfOp, nextByteEntry, innerLoop, outerLoop,
    appendedPCs, hcode, hrun, hinc, hdest, hdestWord, honeWord, jump1287,
    hc9, hc10, hc11, hc12,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_exponentExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started : Nat)
    (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock exponentExitPath
      (exponentDone s accumulatorWord count b e m baseOff expOff rest started) =
      some (serializerHandoff s accumulatorWord count b e m baseOff expOff rest) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hdest : (1118 : UInt256).toNat = 1118 := by decide
  have hdestWord : (1118 : UInt256) = UInt256.ofNat 1118 := by decide
  simp [exponentExitPath, opAt, pushAt, wfOp, exponentDone, outerLoop,
    serializerHandoff, appendedPCs, hcode, hrun, hdest, hdestWord, jump1118,
    hc8, hc9, hc10,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]


/-- Bit computed, `started` nonzero: fall through to the squaring. -/
def startedBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1329 }

/-- Bit computed, `started` zero: the accumulator is still 1. -/
def notStartedEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1407 }

/-- Square and copy have returned; about to test the bit. -/
def afterSquareCopy (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1362 }

/-- Bit set: multiply by the base. -/
def productEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1369 }

/-- First set bit: seed the accumulator with the base. -/
def seedEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1414 }

set_option linter.unusedSimpArgs false in
theorem run_outerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started : Nat)
    (hcap : rest.length < 1012) (he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulatorWord count b e m baseOff expOff rest started e) =
      some (exponentDone s accumulatorWord count b e m baseOff expOff rest started) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat e) (UInt256.ofNat e) = UInt256.ofNat 0 := by
    simp [UInt256.lt]
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (1453 : UInt256).toNat = 1453 := by decide
  have hdestWord : (1453 : UInt256) = UInt256.ofNat 1453 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, exponentDone,
    appendedPCs, hcode, hrun, hlt, hzeroFalse, hdest, hdestWord, jump1453,
    hc9, hc10, hc11, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256)
    (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
        offset byte 8) =
      some (nextByteEntry s accumulatorWord count b e m baseOff expOff rest
        started i offset byte) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h8Nat : (8 : UInt256).toNat = 8 := by decide
  have hdest : (1442 : UInt256).toNat = 1442 := by decide
  have hdestWord : (1442 : UInt256) = UInt256.ofNat 1442 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, nextByteEntry,
    appendedPCs, hcode, hrun, hzeroFalse, h8Nat, hdest, hdestWord, jump1442,
    hc12, hc13, hc14, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]


set_option linter.unusedSimpArgs false in
theorem run_bitAndStartedTest_started (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hj : j < 8) (hstarted : started = 1)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAndStartedTestPath
      (innerBody s accumulatorWord count b e m baseOff expOff rest started i
        offset byte j) =
      some (startedBody s accumulatorWord count b e m baseOff expOff rest started i
        offset byte (exponentBit byte j) j) := by
  subst hstarted
  have hj7 : j ≤ 7 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj7 (by norm_num : 7 < 2 ^ 256)
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [bitAndStartedTestPath, opAt, pushAt, wfOp, innerBody, innerLoop,
    startedBody, incJEntry, bitFrame, exponentBit, appendedPCs, hrun, hsub,
    hone, hseven, honeIsZero, hc12, hc13, hc14, hc15, hc16, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_bitAndStartedTest_notStarted (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hj : j < 8) (hstarted : started = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAndStartedTestPath
      (innerBody s accumulatorWord count b e m baseOff expOff rest started i
        offset byte j) =
      some (notStartedEntry s accumulatorWord count b e m baseOff expOff rest
        started i offset byte (exponentBit byte j) j) := by
  subst hstarted
  have hj7 : j ≤ 7 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj7 (by norm_num : 7 < 2 ^ 256)
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (1407 : UInt256).toNat = 1407 := by decide
  have hdestWord : (1407 : UInt256) = UInt256.ofNat 1407 := by decide
  simp [bitAndStartedTestPath, opAt, pushAt, wfOp, innerBody, innerLoop,
    notStartedEntry, incJEntry, bitFrame, exponentBit, appendedPCs, hcode, hrun,
    hsub, hone, hseven, hzeroFalse, hdest, hdestWord, jump1407,
    hc12, hc13, hc14, hc15, hc16, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_bitTest_zero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hbit : bit = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitTestPath
      (afterSquareCopy s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (incJEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) := by
  subst hbit
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (1433 : UInt256).toNat = 1433 := by decide
  have hdestWord : (1433 : UInt256) = UInt256.ofNat 1433 := by decide
  simp [bitTestPath, opAt, pushAt, wfOp, afterSquareCopy, incJEntry, incJEntry, bitFrame,
    appendedPCs, hcode, hrun, hzeroFalse, hdest, hdestWord, jump1433, hc13, hc14, hc15, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_bitTest_one (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hbit : bit = UInt256.ofNat 1)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitTestPath
      (afterSquareCopy s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (productEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) := by
  subst hbit
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [bitTestPath, opAt, pushAt, wfOp, afterSquareCopy, productEntry, incJEntry, bitFrame,
    appendedPCs, hrun, hIsZero, hc13, hc14, hc15, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_notStartedBitTest_zero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hbit : bit = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock notStartedBitTestPath
      (notStartedEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (incJEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) := by
  subst hbit
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (1433 : UInt256).toNat = 1433 := by decide
  have hdestWord : (1433 : UInt256) = UInt256.ofNat 1433 := by decide
  simp [notStartedBitTestPath, opAt, pushAt, wfOp, notStartedEntry, incJEntry, incJEntry, bitFrame,
    appendedPCs, hcode, hrun, hzeroFalse, hdest, hdestWord, jump1433, hc13, hc14, hc15, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_notStartedBitTest_one (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1005) (hbit : bit = UInt256.ofNat 1)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock notStartedBitTestPath
      (notStartedEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (seedEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) := by
  subst hbit
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [notStartedBitTestPath, opAt, pushAt, wfOp, notStartedEntry, seedEntry, incJEntry, bitFrame,
    appendedPCs, hrun, hIsZero, hc13, hc14, hc15, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-! ## Call blocks

Each of these hands control to the shared `mulModBig` (pc 310) or `copyLimbs`
(pc 58) with the return address of the following block, leaving the bit frame
untouched underneath the call arguments. -/

/-- `mulModBig(acc, acc, 0x0c00, modulus, n)` — the squaring. -/
def squareEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  BigMul.mulEntry
    (startedBody s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j)
    2048 2048 3072 0 count 1347
    (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
      bit j rest)

/-- `copyLimbs(acc, 0x0c00, n)` after the squaring. -/
def squareCopyEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  BigHelpers.copyEntry
    (afterSquareCopy s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j)
    2048 3072 count 1362
    (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
      bit j rest)

set_option linter.unusedSimpArgs false in
theorem run_squareCall (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock squareCallPath
      (startedBody s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (squareEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdest : (310 : UInt256).toNat = 310 := by decide
  have hdestWord : (310 : UInt256) = UInt256.ofNat 310 := by decide
  have h1347 : (1347 : UInt256) = UInt256.ofNat 1347 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [squareCallPath, opAt, pushAt, wfOp, startedBody, squareEntry,
    BigMul.mulEntry, BigMul.mulFrame, incJEntry, bitFrame, appendedPCs, hcode, hrun,
    hdest, hdestWord, h1347, h2048, h3072, hzero, jump310,
    hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The squaring has returned; about to copy the result into the accumulator. -/
def squareReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1347 }

/-- The multiply has returned. -/
def productReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1387 }

/-- Multiply copy done; jump to the shared increment tail. -/
def afterProductState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  { incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j with pc := UInt256.ofNat 1402 }

set_option linter.unusedSimpArgs false in
theorem run_squareToCopy (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock squareToCopyPath
      (squareReturned s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (BigHelpers.copyEntry
        (squareReturned s accumulatorWord count b e m baseOff expOff rest started i
          offset byte bit j) 2048 3072 count 1362
        (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest)) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdest : (58 : UInt256).toNat = 58 := by decide
  have hdestWord : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h1362 : (1362 : UInt256) = UInt256.ofNat 1362 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [squareToCopyPath, opAt, pushAt, wfOp, squareReturned, BigMul.mulEntry, BigMul.mulFrame,
    BigHelpers.copyEntry, incJEntry, bitFrame, appendedPCs, hcode, hrun,
    hdest, hdestWord, h1362, h2048, h3072, hzero, jump58,
    hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_productCall (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock productCallPath
      (productEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (BigMul.mulEntry
        (productEntry s accumulatorWord count b e m baseOff expOff rest started i
          offset byte bit j) 2048 1024 3072 0 count 1387
        (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest)) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdest : (310 : UInt256).toNat = 310 := by decide
  have hdestWord : (310 : UInt256) = UInt256.ofNat 310 := by decide
  have h1387 : (1387 : UInt256) = UInt256.ofNat 1387 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [productCallPath, opAt, pushAt, wfOp, productEntry, BigMul.mulEntry, BigMul.mulFrame,
    BigHelpers.copyEntry, incJEntry, bitFrame, appendedPCs, hcode, hrun,
    hdest, hdestWord, h1387, h1024, h2048, h3072, hzero, jump310,
    hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_productToCopy (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock productToCopyPath
      (productReturned s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (BigHelpers.copyEntry
        (productReturned s accumulatorWord count b e m baseOff expOff rest started i
          offset byte bit j) 2048 3072 count 1402
        (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest)) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdest : (58 : UInt256).toNat = 58 := by decide
  have hdestWord : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h1402 : (1402 : UInt256) = UInt256.ofNat 1402 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [productToCopyPath, opAt, pushAt, wfOp, productReturned, BigMul.mulEntry, BigMul.mulFrame,
    BigHelpers.copyEntry, incJEntry, bitFrame, appendedPCs, hcode, hrun,
    hdest, hdestWord, h1402, h2048, h3072, hzero, jump58,
    hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_seedCall (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock seedCallPath
      (seedEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (BigHelpers.copyEntry
        (seedEntry s accumulatorWord count b e m baseOff expOff rest started i
          offset byte bit j) 2048 1024 count 1428
        (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest)) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdest : (58 : UInt256).toNat = 58 := by decide
  have hdestWord : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h1428 : (1428 : UInt256) = UInt256.ofNat 1428 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [seedCallPath, opAt, pushAt, wfOp, seedEntry, BigMul.mulEntry, BigMul.mulFrame,
    BigHelpers.copyEntry, incJEntry, bitFrame, appendedPCs, hcode, hrun,
    hdest, hdestWord, h1428, h1024, h2048, hzero, jump58,
    hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_afterProduct (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock afterProductPath
      (afterProductState s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) =
      some (incJEntry s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdest : (1433 : UInt256).toNat = 1433 := by decide
  have hdestWord : (1433 : UInt256) = UInt256.ofNat 1433 := by decide

  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [afterProductPath, opAt, pushAt, wfOp, afterProductState, BigMul.mulEntry, BigMul.mulFrame,
    BigHelpers.copyEntry, incJEntry, bitFrame, appendedPCs, hcode, hrun,
    hdest, hdestWord, hzero, jump1433,
    hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-! ## One-bit composition

Four cases, on `started` and the exponent bit. This first one is the pure
skip: the accumulator is still 1 and the bit is 0, so the iteration does no
arithmetic at all — the whole point of the square-and-multiply rewrite. -/

private def sound (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka)) {s t : State}
    (hres : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hres hrun hnp

/-- `started = 0`, bit clear: the accumulator is untouched and `j` advances. -/
def gasSteps_bitSkip (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 1000) (hj : j < 8)
    (hbit : exponentBit byte j = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte j)
      (innerLoop s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte (j + 1)) := by
  have hj' : j + 1 < 2 ^ 256 := by omega
  exact
    (sound innerGuardPath
      (run_innerGuard s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte j (by omega) hj hrun) hcode hfork hrun hnp).trans <|
    (sound bitAndStartedTestPath
      (run_bitAndStartedTest_notStarted s accumulatorWord count b e m baseOff
        expOff rest 0 i offset byte j (by omega) hj rfl hcode hrun)
      hcode hfork hrun hnp).trans <|
    (sound notStartedBitTestPath
      (run_notStartedBitTest_zero s accumulatorWord count b e m baseOff expOff
        rest 0 i offset byte (exponentBit byte j) j (by omega) hbit hcode hrun)
      hcode hfork hrun hnp).trans
    (sound incJPath
      (run_incJ s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte (exponentBit byte j) j (by omega) hj' hcode hrun)
      hcode hfork hrun hnp)

/-- Memory effect of seeding the accumulator with the reduced base:
`copyLimbs(0x0800, 0x0400, n)`. -/
def seedApplied (s : State) (count : Nat) : State :=
  { s with memory := BigHelpers.copyMemory s.memory 2048 1024 count
           activeWords := BigHelpers.copyWords s.activeWords 2048 1024 count }

/-- The copy returns exactly into the frame `setStarted` expects. -/
private theorem seedCopy_eq (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte bit : UInt256) (j : Nat) :
    BigHelpers.copyReturned
      (seedEntry s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte bit j) 2048 1024 count 1428
      (bitFrame accumulatorWord count b e m baseOff expOff 0 i offset byte
        bit j rest) =
      afterSeedCopy (seedApplied s count) accumulatorWord count b e m baseOff
        expOff rest 0 i offset byte bit j := by
  rfl

/-- `started = 0`, bit set: the accumulator is seeded with the base by copy and
`started` becomes 1. This is the first set bit of the exponent. -/
def gasSteps_bitSeed (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 1000) (hj : j < 8) (hcount : count < 2 ^ 256)
    (hbit : exponentBit byte j = UInt256.ofNat 1)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte j)
      (innerLoop (seedApplied s count) accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (j + 1)) := by
  have hj' : j + 1 < 2 ^ 256 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff 0 i offset
      byte (exponentBit byte j) j rest).length < 1016 := by
    simp [bitFrame]; omega
  exact
    (sound innerGuardPath
      (run_innerGuard s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte j (by omega) hj hrun) hcode hfork hrun hnp).trans <|
    (sound bitAndStartedTestPath
      (run_bitAndStartedTest_notStarted s accumulatorWord count b e m baseOff
        expOff rest 0 i offset byte j (by omega) hj rfl hcode hrun)
      hcode hfork hrun hnp).trans <|
    (sound notStartedBitTestPath
      (run_notStartedBitTest_one s accumulatorWord count b e m baseOff expOff
        rest 0 i offset byte (exponentBit byte j) j (by omega) hbit hrun)
      hcode hfork hrun hnp).trans <|
    (sound seedCallPath
      (run_seedCall s accumulatorWord count b e m baseOff expOff rest 0 i
        offset byte (exponentBit byte j) j (by omega) hcode hrun)
      hcode hfork hrun hnp).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigHelpers.gasSteps_copy
        (seedEntry s accumulatorWord count b e m baseOff expOff rest 0 i
          offset byte (exponentBit byte j) j)
        2048 1024 count 1428
        (bitFrame accumulatorWord count b e m baseOff expOff 0 i offset byte
          (exponentBit byte j) j rest)
        hframe hcount hcode hfork hrun hnp
        (by rw [show ((1428 : UInt256)).toNat = 1428 from by decide]; exact jump1428))
      rfl (seedCopy_eq s accumulatorWord count b e m baseOff expOff rest i
        offset byte (exponentBit byte j) j)).trans <|
    (sound setStartedPath
      (run_setStarted (seedApplied s count) accumulatorWord count b e m baseOff
        expOff rest 0 i offset byte (exponentBit byte j) j (by omega) hrun)
      hcode hfork hrun hnp).trans
    (sound incJPath
      (run_incJ (seedApplied s count) accumulatorWord count b e m baseOff expOff
        rest 1 i offset byte (exponentBit byte j) j (by omega) hj' hcode hrun)
      hcode hfork hrun hnp)

/-- Memory effect of the squaring `mulModBig(acc, acc, 0x0c00, modulus, n)`. -/
def squareApplied (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  BigMul.mulApplied
    (startedBody s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j) 2048 2048 3072 0 count 1347
    (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
      bit j rest)

/-- Then `copyLimbs(acc, 0x0c00, n)` moves the square into the accumulator. -/
def squareCopied (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  let sq := squareApplied s accumulatorWord count b e m baseOff expOff rest
    started i offset byte bit j
  { sq with memory := BigHelpers.copyMemory sq.memory 2048 3072 count
            activeWords := BigHelpers.copyWords sq.activeWords 2048 3072 count }

private theorem squareMul_eq (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    BigMul.mulReturned
      (squareApplied s accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) 1347
      (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest) =
      squareReturned (squareApplied s accumulatorWord count b e m baseOff expOff
        rest started i offset byte bit j) accumulatorWord count b e m baseOff
        expOff rest started i offset byte bit j := by
  rfl

private theorem squareCopy_eq (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    BigHelpers.copyReturned
      (squareReturned (squareApplied s accumulatorWord count b e m baseOff expOff
        rest started i offset byte bit j) accumulatorWord count b e m baseOff
        expOff rest started i offset byte bit j) 2048 3072 count 1362
      (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest) =
      afterSquareCopy (squareCopied s accumulatorWord count b e m baseOff expOff
        rest started i offset byte bit j) accumulatorWord count b e m baseOff
        expOff rest started i offset byte bit j := by
  rfl


@[simp] theorem squareApplied_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareApplied s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [squareApplied, startedBody, incJEntry]

@[simp] theorem squareApplied_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareApplied s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [squareApplied, startedBody, incJEntry]

@[simp] theorem squareCopied_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareCopied s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [squareCopied]

@[simp] theorem squareCopied_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareCopied s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [squareCopied]

@[simp] theorem incJEntry_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [incJEntry, incJEntry]

@[simp] theorem incJEntry_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (incJEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [incJEntry, incJEntry]

@[simp] theorem afterSeedCopy_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (afterSeedCopy s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [afterSeedCopy, incJEntry]

@[simp] theorem afterSeedCopy_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (afterSeedCopy s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [afterSeedCopy, incJEntry]

@[simp] theorem startedBody_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (startedBody s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [startedBody, incJEntry]

@[simp] theorem startedBody_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (startedBody s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [startedBody, incJEntry]

@[simp] theorem notStartedEntry_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (notStartedEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [notStartedEntry, incJEntry]

@[simp] theorem notStartedEntry_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (notStartedEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [notStartedEntry, incJEntry]

@[simp] theorem afterSquareCopy_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (afterSquareCopy s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [afterSquareCopy, incJEntry]

@[simp] theorem afterSquareCopy_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (afterSquareCopy s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [afterSquareCopy, incJEntry]

@[simp] theorem productEntry_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [productEntry, incJEntry]

@[simp] theorem productEntry_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [productEntry, incJEntry]

@[simp] theorem seedEntry_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (seedEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [seedEntry, incJEntry]

@[simp] theorem seedEntry_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (seedEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [seedEntry, incJEntry]

@[simp] theorem productReturned_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productReturned s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [productReturned, incJEntry]

@[simp] theorem productReturned_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productReturned s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [productReturned, incJEntry]

@[simp] theorem afterProductState_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (afterProductState s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [afterProductState, incJEntry]

@[simp] theorem afterProductState_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (afterProductState s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [afterProductState, incJEntry]

@[simp] theorem squareReturned_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareReturned s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = s.executionEnv := by
  simp [squareReturned, incJEntry]

@[simp] theorem squareReturned_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareReturned s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = s.halt := by
  simp [squareReturned, incJEntry]

/-- `started = 1`, bit clear: one squaring, no multiply. -/
def gasSteps_bitSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 967) (hj : j < 8) (hcount : count < 2 ^ 256)
    (hbit : exponentBit byte j = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte j)
      (innerLoop (squareCopied s accumulatorWord count b e m baseOff expOff rest
          1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte (j + 1)) := by
  have hj' : j + 1 < 2 ^ 256 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset
      byte (exponentBit byte j) j rest).length < 980 := by
    simp [bitFrame]; omega
  have hframe' : (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset
      byte (exponentBit byte j) j rest).length < 1016 := by
    simp [bitFrame]; omega
  exact
    (sound innerGuardPath
      (run_innerGuard s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte j (by omega) hj hrun) hcode hfork hrun hnp).trans <|
    (sound bitAndStartedTestPath
      (run_bitAndStartedTest_started s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte j (by omega) hj rfl hrun)
      hcode hfork hrun hnp).trans <|
    (sound squareCallPath
      (run_squareCall s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j (by omega) hcode hrun)
      hcode hfork hrun hnp).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigMul.gasSteps_mulModBig
        (startedBody s accumulatorWord count b e m baseOff expOff rest 1 i
          offset byte (exponentBit byte j) j)
        2048 2048 3072 0 count 1347
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hframe hcount hcode hfork hrun hnp
        (by rw [show ((1347 : UInt256)).toNat = 1347 from by decide]; exact jump1347))
      rfl (squareMul_eq s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j)).trans <|
    (sound squareToCopyPath
      (run_squareToCopy (squareApplied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigHelpers.gasSteps_copy
        (squareReturned (squareApplied s accumulatorWord count b e m baseOff
          expOff rest 1 i offset byte (exponentBit byte j) j)
          accumulatorWord count b e m baseOff expOff rest 1 i offset byte
          (exponentBit byte j) j)
        2048 3072 count 1362
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hframe' hcount (by simpa using hcode) (by simpa [State.fork] using hfork)
        (by simpa using hrun) (by simpa [State.fork] using hnp)
        (by rw [show ((1362 : UInt256)).toNat = 1362 from by decide]; exact jump1362))
      rfl (squareCopy_eq s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j)).trans <|
    (sound bitTestPath
      (run_bitTest_zero (squareCopied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) hbit (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans
    (sound incJPath
      (run_incJ (squareCopied s accumulatorWord count b e m baseOff expOff rest
        1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) hj' (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp))

/-- Memory effect of the multiply `mulModBig(acc, base, 0x0c00, modulus, n)`,
taken from the already-squared state. -/
def productApplied (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  BigMul.mulApplied
    (productEntry sq accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j) 2048 1024 3072 0 count 1387
    (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
      bit j rest)

/-- Then `copyLimbs(acc, 0x0c00, n)` moves the product into the accumulator. -/
def productCopied (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) : State :=
  let pr := productApplied sq accumulatorWord count b e m baseOff expOff rest
    started i offset byte bit j
  { pr with memory := BigHelpers.copyMemory pr.memory 2048 3072 count
            activeWords := BigHelpers.copyWords pr.activeWords 2048 3072 count }

@[simp] theorem productApplied_executionEnv (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productApplied sq accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = sq.executionEnv := by
  simp [productApplied, productEntry, incJEntry]

@[simp] theorem productApplied_halt (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productApplied sq accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = sq.halt := by
  simp [productApplied, productEntry, incJEntry]

@[simp] theorem productCopied_executionEnv (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productCopied sq accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).executionEnv = sq.executionEnv := by
  simp [productCopied]

@[simp] theorem productCopied_halt (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productCopied sq accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).halt = sq.halt := by
  simp [productCopied]

private theorem productMul_eq (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    BigMul.mulReturned
      (productApplied sq accumulatorWord count b e m baseOff expOff rest started i
        offset byte bit j) 1387
      (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest) =
      productReturned (productApplied sq accumulatorWord count b e m baseOff
        expOff rest started i offset byte bit j) accumulatorWord count b e m
        baseOff expOff rest started i offset byte bit j := by
  rfl

private theorem productCopy_eq (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    BigHelpers.copyReturned
      (productReturned (productApplied sq accumulatorWord count b e m baseOff
        expOff rest started i offset byte bit j) accumulatorWord count b e m
        baseOff expOff rest started i offset byte bit j) 2048 3072 count 1402
      (bitFrame accumulatorWord count b e m baseOff expOff started i offset byte
        bit j rest) =
      afterProductState (productCopied sq accumulatorWord count b e m baseOff
        expOff rest started i offset byte bit j) accumulatorWord count b e m
        baseOff expOff rest started i offset byte bit j := by
  rfl

/-- `started = 1`, bit set: square then multiply by the base. -/
def gasSteps_bitSquareMul (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 967) (hj : j < 8) (hcount : count < 2 ^ 256)
    (hbit : exponentBit byte j = UInt256.ofNat 1)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte j)
      (innerLoop
        (productCopied
          (squareCopied s accumulatorWord count b e m baseOff expOff rest 1 i
            offset byte (exponentBit byte j) j)
          accumulatorWord count b e m baseOff expOff rest 1 i offset byte
          (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte (j + 1)) := by
  have hj' : j + 1 < 2 ^ 256 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset
      byte (exponentBit byte j) j rest).length < 980 := by
    simp [bitFrame]; omega
  have hframe' : (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset
      byte (exponentBit byte j) j rest).length < 1016 := by
    simp [bitFrame]; omega
  exact
    (sound innerGuardPath
      (run_innerGuard s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte j (by omega) hj hrun) hcode hfork hrun hnp).trans <|
    (sound bitAndStartedTestPath
      (run_bitAndStartedTest_started s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte j (by omega) hj rfl hrun)
      hcode hfork hrun hnp).trans <|
    (sound squareCallPath
      (run_squareCall s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j (by omega) hcode hrun)
      hcode hfork hrun hnp).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigMul.gasSteps_mulModBig
        (startedBody s accumulatorWord count b e m baseOff expOff rest 1 i
          offset byte (exponentBit byte j) j)
        2048 2048 3072 0 count 1347
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hframe hcount hcode hfork hrun hnp
        (by rw [show ((1347 : UInt256)).toNat = 1347 from by decide]; exact jump1347))
      rfl (squareMul_eq s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j)).trans <|
    (sound squareToCopyPath
      (run_squareToCopy (squareApplied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigHelpers.gasSteps_copy
        (squareReturned (squareApplied s accumulatorWord count b e m baseOff
          expOff rest 1 i offset byte (exponentBit byte j) j)
          accumulatorWord count b e m baseOff expOff rest 1 i offset byte
          (exponentBit byte j) j)
        2048 3072 count 1362
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hframe' hcount (by simpa using hcode) (by simpa [State.fork] using hfork)
        (by simpa using hrun) (by simpa [State.fork] using hnp)
        (by rw [show ((1362 : UInt256)).toNat = 1362 from by decide]; exact jump1362))
      rfl (squareCopy_eq s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j)).trans <|
    (sound bitTestPath
      (run_bitTest_one (squareCopied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) hbit (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans <|
    (sound productCallPath
      (run_productCall (squareCopied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigMul.gasSteps_mulModBig
        (productEntry (squareCopied s accumulatorWord count b e m baseOff expOff
          rest 1 i offset byte (exponentBit byte j) j)
          accumulatorWord count b e m baseOff expOff rest 1 i offset byte
          (exponentBit byte j) j)
        2048 1024 3072 0 count 1387
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hframe hcount (by simpa using hcode) (by simpa [State.fork] using hfork)
        (by simpa using hrun) (by simpa [State.fork] using hnp)
        (by rw [show ((1387 : UInt256)).toNat = 1387 from by decide]; exact jump1387))
      rfl (productMul_eq (squareCopied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j)).trans <|
    (sound productToCopyPath
      (run_productToCopy (productApplied (squareCopied s accumulatorWord count b
        e m baseOff expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans <|
    (Challenge.EvmProof.GasSteps.cast
      (BigHelpers.gasSteps_copy
        (productReturned (productApplied (squareCopied s accumulatorWord count b
          e m baseOff expOff rest 1 i offset byte (exponentBit byte j) j)
          accumulatorWord count b e m baseOff expOff rest 1 i offset byte
          (exponentBit byte j) j)
          accumulatorWord count b e m baseOff expOff rest 1 i offset byte
          (exponentBit byte j) j)
        2048 3072 count 1402
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hframe' hcount (by simpa using hcode) (by simpa [State.fork] using hfork)
        (by simpa using hrun) (by simpa [State.fork] using hnp)
        (by rw [show ((1402 : UInt256)).toNat = 1402 from by decide]; exact jump1402))
      rfl (productCopy_eq (squareCopied s accumulatorWord count b e m baseOff
        expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j)).trans <|
    (sound afterProductPath
      (run_afterProduct (productCopied (squareCopied s accumulatorWord count b e
        m baseOff expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans
    (sound incJPath
      (run_incJ (productCopied (squareCopied s accumulatorWord count b e m
        baseOff expOff rest 1 i offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j (by omega) hj' (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp))

theorem exponentBit_eq_zero_or_one (byte : UInt256) (j : Nat) :
    exponentBit byte j = UInt256.ofNat 0 ∨ exponentBit byte j = UInt256.ofNat 1 := by
  set x := UInt256.shiftRight byte (UInt256.ofNat (7 - j)) with hx
  have hval : (UInt256.land x 1).toNat = x.toNat &&& 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_land,
      show UInt256.toNat 1 = 1 from by decide]
  have hmod : x.toNat &&& 1 = x.toNat % 2 := Nat.and_one_is_mod _
  have hlt : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
  have hself : UInt256.land x 1 = UInt256.ofNat ((UInt256.land x 1).toNat) :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat _
  rcases hlt with h | h
  · left;  rw [show exponentBit byte j = UInt256.land x 1 from rfl, hself, hval, hmod, h]
  · right; rw [show exponentBit byte j = UInt256.land x 1 from rfl, hself, hval, hmod, h]

/-! ## Bit induction

`started` is not carried in the machine state — it is a stack slot, and its
value after any prefix of the exponent is a pure function of that prefix. So
the loop is indexed by `startedAfter`, and the state by `stateAfter`. -/

/-- `started` after consuming one more bit. -/
def nextStarted (started : Nat) (byte : UInt256) (j : Nat) : Nat :=
  if started = 1 then 1
  else if exponentBit byte j = UInt256.ofNat 1 then 1 else 0

/-- Machine state after consuming one more bit. -/
def bitStep (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) : State :=
  if started = 1 then
    if exponentBit byte j = UInt256.ofNat 1 then
      productCopied
        (squareCopied s accumulatorWord count b e m baseOff expOff rest 1 i
          offset byte (exponentBit byte j) j)
        accumulatorWord count b e m baseOff expOff rest 1 i offset byte
        (exponentBit byte j) j
    else
      squareCopied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j
  else
    if exponentBit byte j = UInt256.ofNat 1 then seedApplied s count else s

@[simp] theorem nextStarted_lt_two (started : Nat) (byte : UInt256) (j : Nat) :
    nextStarted started byte j = 0 ∨ nextStarted started byte j = 1 := by
  unfold nextStarted; split <;> [right; skip] <;> [rfl; split] <;> simp

@[simp] theorem bitStep_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (bitStep s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).executionEnv = s.executionEnv := by
  unfold bitStep; split <;> split <;> simp [seedApplied]

@[simp] theorem bitStep_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (bitStep s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).halt = s.halt := by
  unfold bitStep; split <;> split <;> simp [seedApplied]

/-- One bit iteration, for either value of `started`.

Case analysis is on the `Nat` directly rather than on a disjunction, because
this produces data (a `GasSteps`) and `Or` only eliminates into `Prop`. -/
def gasSteps_bit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat)
    (hcap : rest.length < 967) (hj : j < 8) (hcount : count < 2 ^ 256)
    (hstarted : started < 2)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
        offset byte j)
      (innerLoop (bitStep s accumulatorWord count b e m baseOff expOff rest
          started i offset byte j)
        accumulatorWord count b e m baseOff expOff rest
        (nextStarted started byte j) i offset byte (j + 1)) :=
  match started, hstarted with
  | 0, _ =>
      if hbit : exponentBit byte j = UInt256.ofNat 1 then
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_bitSeed s accumulatorWord count b e m baseOff expOff rest i
            offset byte j (by omega) hj hcount hbit hcode hfork hrun hnp)
          rfl (by simp [bitStep, nextStarted, hbit])
      else
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_bitSkip s accumulatorWord count b e m baseOff expOff rest i
            offset byte j (by omega)  hj
            ((exponentBit_eq_zero_or_one byte j).resolve_right hbit)
            hcode hfork hrun hnp)
          rfl (by simp [bitStep, nextStarted, hbit])
  | 1, _ =>
      if hbit : exponentBit byte j = UInt256.ofNat 1 then
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_bitSquareMul s accumulatorWord count b e m baseOff expOff
            rest i offset byte j hcap hj hcount hbit hcode hfork hrun hnp)
          rfl (by simp [bitStep, nextStarted, hbit])
      else
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_bitSquare s accumulatorWord count b e m baseOff expOff rest
            i offset byte j hcap hj hcount
            ((exponentBit_eq_zero_or_one byte j).resolve_right hbit)
            hcode hfork hrun hnp)
          rfl (by simp [bitStep, nextStarted, hbit])

/-- `started` after consuming `j` bits of this byte. -/
def startedAfter (started : Nat) (byte : UInt256) : Nat → Nat
  | 0 => started
  | j + 1 => nextStarted (startedAfter started byte j) byte j

/-- Machine state after consuming `j` bits of this byte. -/
def stateAfter (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) : Nat → State
  | 0 => s
  | j + 1 =>
      bitStep (stateAfter s accumulatorWord count b e m baseOff expOff rest
          started i offset byte j)
        accumulatorWord count b e m baseOff expOff rest
        (startedAfter started byte j) i offset byte j

theorem startedAfter_lt_two (started : Nat) (byte : UInt256) (j : Nat)
    (h : started < 2) : startedAfter started byte j < 2 := by
  induction j with
  | zero => exact h
  | succ j ih =>
      unfold startedAfter nextStarted
      split
      · omega
      · split <;> omega

@[simp] theorem stateAfter_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih => simp [stateAfter, ih]

@[simp] theorem stateAfter_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih => simp [stateAfter, ih]

/-- The inner loop's state at bit `j`. -/
def bitLoopState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) : State :=
  innerLoop (stateAfter s accumulatorWord count b e m baseOff expOff rest
      started i offset byte j)
    accumulatorWord count b e m baseOff expOff rest
    (startedAfter started byte j) i offset byte j

/-- **The bit induction.** All eight bits of one exponent byte. -/
def gasSteps_bitLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256)
    (hcap : rest.length < 967) (hcount : count < 2 ^ 256)
    (hstarted : started < 2)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitLoopState s accumulatorWord count b e m baseOff expOff rest started i
        offset byte 0)
      (bitLoopState s accumulatorWord count b e m baseOff expOff rest started i
        offset byte 8) :=
  Challenge.EvmProof.GasSteps.iterateBounded 8 (fun j hj =>
    gasSteps_bit
      (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
        offset byte j)
      accumulatorWord count b e m baseOff expOff rest
      (startedAfter started byte j) i offset byte j
      hcap hj hcount (startedAfter_lt_two started byte j hstarted)
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp))

@[simp] theorem innerLoop_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).executionEnv = s.executionEnv := by
  simp [innerLoop]

@[simp] theorem innerLoop_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (innerLoop s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).halt = s.halt := by
  simp [innerLoop]

@[simp] theorem outerLoop_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started i : Nat) :
    (outerLoop s accumulatorWord count b e m baseOff expOff rest started
      i).executionEnv = s.executionEnv := by
  simp [outerLoop]

@[simp] theorem outerLoop_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started i : Nat) :
    (outerLoop s accumulatorWord count b e m baseOff expOff rest started i).halt
      = s.halt := by
  simp [outerLoop]

@[simp] theorem nextByteEntry_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) :
    (nextByteEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte).executionEnv = s.executionEnv := by
  simp [nextByteEntry]

@[simp] theorem nextByteEntry_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) :
    (nextByteEntry s accumulatorWord count b e m baseOff expOff rest started i
      offset byte).halt = s.halt := by
  simp [nextByteEntry]

@[simp] theorem squareApplied_callStack (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (squareApplied s accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).callStack = s.callStack := by
  simp [squareApplied, startedBody, incJEntry]

@[simp] theorem productApplied_callStack (sq : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte bit : UInt256) (j : Nat) :
    (productApplied sq accumulatorWord count b e m baseOff expOff rest started i
      offset byte bit j).callStack = sq.callStack := by
  simp [productApplied, productEntry, incJEntry]

@[simp] theorem bitStep_callStack (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (bitStep s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).callStack = s.callStack := by
  unfold bitStep; split <;> split <;>
    simp [seedApplied, squareCopied, productCopied]

@[simp] theorem stateAfter_callStack (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat) :
    (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
      offset byte j).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih => simp [stateAfter, ih]

/-! ## Byte induction -/

/-- The exponent byte consumed at index `i`. -/
def byteAt (s : State) (expOff i : Nat) : UInt256 := loadedExponentByte s expOff i

/-- `started` after consuming the whole byte at index `i`. -/
def startedAfterByte (s : State) (expOff : Nat) (started i : Nat) : Nat :=
  startedAfter started (byteAt s expOff i) 8

/-- Machine state after consuming the whole byte at index `i`. -/
def byteStep (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) : State :=
  stateAfter s accumulatorWord count b e m baseOff expOff rest started i
    (UInt256.ofNat (expOff + i)) (byteAt s expOff i) 8

@[simp] theorem byteStep_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started i : Nat) :
    (byteStep s accumulatorWord count b e m baseOff expOff rest started i).executionEnv
      = s.executionEnv := by
  simp [byteStep]

@[simp] theorem byteStep_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started i : Nat) :
    (byteStep s accumulatorWord count b e m baseOff expOff rest started i).halt
      = s.halt := by
  simp [byteStep]

theorem startedAfterByte_lt_two (s : State) (expOff started i : Nat)
    (h : started < 2) : startedAfterByte s expOff started i < 2 :=
  startedAfter_lt_two started (byteAt s expOff i) 8 h

/-- One exponent byte: guard, load, eight bits, advance `i`. -/
def gasSteps_byte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (byte : UInt256) (hbyte : byteAt s expOff i = byte)
    (hcap : rest.length < 967) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hi : i < e) (hoff : expOff + i < 2 ^ 256)
    (hi' : i + 1 < 2 ^ 256) (hstarted : started < 2)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulatorWord count b e m baseOff expOff rest started i)
      (outerLoop
        (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
          (UInt256.ofNat (expOff + i)) byte 8)
        accumulatorWord count b e m baseOff expOff rest
        (startedAfter started byte 8) (i + 1)) := by
  subst hbyte
  exact
    (sound outerGuardPath
      (run_outerGuard s accumulatorWord count b e m baseOff expOff rest started i
        (by omega) he hi hrun) hcode hfork hrun hnp).trans <|
    (sound outerToInnerPath
      (run_outerToInner s accumulatorWord count b e m baseOff expOff rest started i
        (by omega) hoff hrun) hcode hfork hrun hnp).trans <|
    (gasSteps_bitLoop s accumulatorWord count b e m baseOff expOff rest started i
      (UInt256.ofNat (expOff + i)) (byteAt s expOff i)
      hcap hcount hstarted hcode hfork hrun hnp).trans <|
    (sound innerGuardPath
      (run_innerFinishGuard
        (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
          (UInt256.ofNat (expOff + i)) (byteAt s expOff i) 8)
        accumulatorWord count b e m baseOff expOff rest
        (startedAfter started (byteAt s expOff i) 8) i
        (UInt256.ofNat (expOff + i)) (byteAt s expOff i)
        (by omega) (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)).trans
    (sound nextBytePath
      (run_nextByte
        (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
          (UInt256.ofNat (expOff + i)) (byteAt s expOff i) 8)
        accumulatorWord count b e m baseOff expOff rest
        (startedAfter started (byteAt s expOff i) 8) i
        (UInt256.ofNat (expOff + i)) (byteAt s expOff i)
        (by omega) hi' (by simpa using hcode) (by simpa using hrun))
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp))


/-- `started` after consuming `i` whole exponent bytes. The exponent bytes are
read from `s`'s calldata, which every step preserves, so this needs no mutual
recursion with the state. -/
def startedAfterBytes (s : State) (expOff started : Nat) : Nat → Nat
  | 0 => started
  | i + 1 =>
      startedAfter (startedAfterBytes s expOff started i) (byteAt s expOff i) 8

/-- Machine state after consuming `i` whole exponent bytes. -/
def bytesState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started : Nat) : Nat → State
  | 0 => s
  | i + 1 =>
      stateAfter
        (bytesState s accumulatorWord count b e m baseOff expOff rest started i)
        accumulatorWord count b e m baseOff expOff rest
        (startedAfterBytes s expOff started i) i
        (UInt256.ofNat (expOff + i)) (byteAt s expOff i) 8

@[simp] theorem bytesState_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) :
    (bytesState s accumulatorWord count b e m baseOff expOff rest started
      i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [bytesState, ih]

@[simp] theorem bytesState_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) :
    (bytesState s accumulatorWord count b e m baseOff expOff rest started i).halt
      = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [bytesState, ih]

theorem startedAfterBytes_lt_two (s : State) (expOff started : Nat) (i : Nat)
    (h : started < 2) : startedAfterBytes s expOff started i < 2 := by
  induction i with
  | zero => exact h
  | succ i ih => exact startedAfter_lt_two _ _ 8 ih

/-- The outer loop's state after `i` exponent bytes. -/
def byteLoopState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) : State :=
  outerLoop (bytesState s accumulatorWord count b e m baseOff expOff rest
      started i)
    accumulatorWord count b e m baseOff expOff rest
    (startedAfterBytes s expOff started i) i

/-- **The byte induction.** Every exponent byte. -/
def gasSteps_byteLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started : Nat)
    (hcap : rest.length < 967) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hoff : expOff + e < 2 ^ 256) (hstarted : started < 2)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (byteLoopState s accumulatorWord count b e m baseOff expOff rest started 0)
      (byteLoopState s accumulatorWord count b e m baseOff expOff rest started e) :=
  Challenge.EvmProof.GasSteps.iterateBounded e (fun i hi =>
    gasSteps_byte
      (bytesState s accumulatorWord count b e m baseOff expOff rest started i)
      accumulatorWord count b e m baseOff expOff rest
      (startedAfterBytes s expOff started i) i (byteAt s expOff i)
      (by simp [byteAt, loadedExponentByte])
      hcap hcount he hi (by omega) (by omega)
      (startedAfterBytes_lt_two s expOff started i hstarted)
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp))

/-! ## Functional invariant

The accumulator holds `base ^ (exponent bits consumed so far) mod modulus`.
This is uniform across all four cases, because `started = 0` exactly while the
consumed prefix is zero and the accumulator is still `1 mod modulus`:

* not started, bit 0 — prefix `0 → 0`, accumulator unchanged (`base^0`);
* not started, bit 1 — prefix `0 → 1`, accumulator seeded with `base`;
* started, bit 0     — prefix `p → 2p`, accumulator squared;
* started, bit 1     — prefix `p → 2p+1`, accumulator squared then multiplied.

The `started` flag is therefore a pure optimization: it removes the redundant
squaring of 1 and multiplication by 1 that the reference performs. -/

/-- Numeric literals versus `UInt256.ofNat`. Proved through `toNat` because
`decide` on a 256-bit `Fin` is prohibitive. -/
theorem word_lit_eq (n : Nat) (h : (UInt256.ofNat n).toNat = n)
    (a : UInt256) (ha : a.toNat = n) : a = UInt256.ofNat n := by
  rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat a, ha]

@[simp] theorem word_2048 : (2048 : UInt256) = UInt256.ofNat 2048 :=
  word_lit_eq 2048 (by decide) _ (by decide)

@[simp] theorem word_1024 : (1024 : UInt256) = UInt256.ofNat 1024 :=
  word_lit_eq 1024 (by decide) _ (by decide)

@[simp] theorem word_3072 : (3072 : UInt256) = UInt256.ofNat 3072 :=
  word_lit_eq 3072 (by decide) _ (by decide)

@[simp] theorem word_0 : (0 : UInt256) = UInt256.ofNat 0 :=
  word_lit_eq 0 (by decide) _ (by decide)

/-- Cheap word disequality: `decide` on a 256-bit `Fin` blows up, so this is
proved through `toNat` instead. -/
@[simp] theorem word_zero_ne_one :
    ¬((UInt256.ofNat 0 : UInt256) = UInt256.ofNat 1) := by
  intro h
  have h2 := congrArg UInt256.toNat h
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat] at h2
  omega

/-- Accumulator value after consuming one more bit. -/
def bitValue (modulus base : Nat) (byte : UInt256) (started j acc : Nat) : Nat :=
  if started = 1 then
    let square := (acc * acc) % modulus
    if (exponentBit byte j).toNat = 0 then square else (square * base) % modulus
  else
    if (exponentBit byte j).toNat = 0 then acc else base

/-- Accumulator value after consuming `j` bits of this byte. -/
def accAfter (modulus base : Nat) (byte : UInt256) (started acc : Nat) :
    Nat → Nat
  | 0 => acc
  | j + 1 =>
      bitValue modulus base byte (startedAfter started byte j) j
        (accAfter modulus base byte started acc j)

/-- The skip case leaves memory untouched, so every region still represents
what it did. -/
theorem bitSkip_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hbit : exponentBit byte j = UInt256.ofNat 0)
    (acc base modulus : Nat)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 0 i offset
          byte j).memory 2048 count
        (bitValue modulus base byte 0 j acc) ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 0 i offset
          byte j).memory 1024 count base ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 0 i offset
          byte j).memory 0 count modulus := by
  have hzero : (exponentBit byte j).toNat = 0 := by
    rw [hbit]; simp [Challenge.EvmProof.Word.word_toNat_ofNat]
  simp only [bitStep, bitValue, if_neg (by decide : ¬ (0 : Nat) = 1), hbit,
    hzero, if_pos rfl]
  exact ⟨hacc, hbase, hmodulus⟩

/-- The seed case copies the reduced base into the accumulator. -/
theorem bitSeed_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hbit : exponentBit byte j = UInt256.ofNat 1) (hcount : count ≤ 32)
    (acc base modulus : Nat)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 0 i offset
          byte j).memory 2048 count
        (bitValue modulus base byte 0 j acc) ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 0 i offset
          byte j).memory 1024 count base ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 0 i offset
          byte j).memory 0 count modulus := by
  have hone : (exponentBit byte j).toNat = 1 := by
    rw [hbit]; simp [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hfit : 32 * count ≤ 1024 := by omega
  simp only [bitStep, bitValue, if_neg (by decide : ¬ (0 : Nat) = 1), hbit,
    hone, if_neg (by decide : ¬ (1 : Nat) = 0), seedApplied]
  refine ⟨?_, ?_, ?_⟩
  · exact BigHelpers.copyMemory_represents s.memory 2048 1024 count base hbase
      (by omega) (by omega) (Or.inr (by omega))
  · exact BigHelpers.represents_copyMemory_disjoint_region s.memory 2048 1024
      1024 count base (by omega) (Or.inr (by omega)) hbase
  · exact BigHelpers.represents_copyMemory_disjoint_region s.memory 2048 1024
      0 count modulus (by omega) (Or.inr (by omega)) hmodulus

/-- The square case: the accumulator becomes `acc^2 mod modulus`. -/
theorem bitSquare_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hbit : exponentBit byte j = UInt256.ofNat 0) (hcount : count ≤ 32)
    (acc base modulus : Nat) (hmodulusPos : 0 < modulus)
    (hmodulusBound : modulus < Limbs.radix ^ count) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 1 i offset
          byte j).memory 2048 count
        (bitValue modulus base byte 1 j acc) ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 1 i offset
          byte j).memory 1024 count base ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 1 i offset
          byte j).memory 0 count modulus := by
  have hzero : (exponentBit byte j).toNat = 0 := by
    rw [hbit]; simp [Challenge.EvmProof.Word.word_toNat_ofNat]
  have h32 : 32 * count ≤ 1024 := by omega
  set entry := startedBody s accumulatorWord count b e m baseOff expOff rest 1 i
    offset byte (exponentBit byte j) j with hentry
  have hmem : entry.memory = s.memory := by
    simp [hentry, startedBody, incJEntry]
  have hacc' : Limbs.Represents entry.memory 2048 count acc := by
    rw [hmem]; exact hacc
  have hbase' : Limbs.Represents entry.memory 1024 count base := by
    rw [hmem]; exact hbase
  have hmod' : Limbs.Represents entry.memory 0 count modulus := by
    rw [hmem]; exact hmodulus
  obtain ⟨hres, _, hmodAfter⟩ :=
    BigMul.mulApplied_represents_product entry 2048 count acc acc modulus 1347
      (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
        (exponentBit byte j) j rest)
      hcount (by omega) hmodulusPos hmodulusBound haccReduced hacc' hacc' hmod'
  have hbaseAfter : Limbs.Represents
      (squareApplied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 1024 count base := by
    simpa [squareApplied, ← hentry, word_2048, word_3072, word_0] using
      BigMul.mulApplied_preserves_region entry (UInt256.ofNat 2048) count 1024
        base 1347
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hcount (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        hbase'
  have hstep : bitStep s accumulatorWord count b e m baseOff expOff rest 1 i
      offset byte j =
      squareCopied s accumulatorWord count b e m baseOff expOff rest 1 i offset
        byte (exponentBit byte j) j := by
    unfold bitStep
    rw [if_pos rfl, if_neg (by rw [hbit]; exact word_zero_ne_one)]
  have hval : bitValue modulus base byte 1 j acc = (acc * acc) % modulus := by
    unfold bitValue
    rw [if_pos rfl, if_pos hzero]
  rw [hstep, hval]
  have hres' : Limbs.Represents
      (squareApplied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 3072 count
      (acc * acc % modulus) := by
    simpa [squareApplied, ← hentry, word_2048, word_3072, word_0] using hres
  have hmodAfter' : Limbs.Represents
      (squareApplied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 0 count modulus := by
    simpa [squareApplied, ← hentry, word_2048, word_3072, word_0] using hmodAfter
  simp only [squareCopied, word_2048, word_3072, word_0]
  refine ⟨?_, ?_, ?_⟩
  · exact BigHelpers.copyMemory_represents _ 2048 3072 count _ hres'
      (by omega) (by omega) (Or.inl (by omega))
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 2048 3072 1024
      count base (by omega) (Or.inr (by omega)) hbaseAfter
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 2048 3072 0
      count modulus (by omega) (Or.inr (by omega)) hmodAfter'

/-- The square-and-multiply case: `acc^2 * base mod modulus`. -/
theorem bitSquareMul_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (i : Nat) (offset byte : UInt256) (j : Nat)
    (hbit : exponentBit byte j = UInt256.ofNat 1) (hcount : count ≤ 32)
    (acc base modulus : Nat) (hmodulusPos : 0 < modulus)
    (hmodulusBound : modulus < Limbs.radix ^ count) (haccReduced : acc < modulus)
    (hbaseReduced : base < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 1 i offset
          byte j).memory 2048 count
        (bitValue modulus base byte 1 j acc) ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 1 i offset
          byte j).memory 1024 count base ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest 1 i offset
          byte j).memory 0 count modulus := by
  have hone : (exponentBit byte j).toNat = 1 := by
    rw [hbit]; simp [Challenge.EvmProof.Word.word_toNat_ofNat]
  have h32 : 32 * count ≤ 1024 := by omega
  set sq := squareCopied s accumulatorWord count b e m baseOff expOff rest 1 i
    offset byte (exponentBit byte j) j with hsq
  -- the squaring, reusing the square-case reasoning
  set entry := startedBody s accumulatorWord count b e m baseOff expOff rest 1 i
    offset byte (exponentBit byte j) j with hentry
  have hmem : entry.memory = s.memory := by
    simp [hentry, startedBody, incJEntry]
  have hacc' : Limbs.Represents entry.memory 2048 count acc := by
    rw [hmem]; exact hacc
  have hbase' : Limbs.Represents entry.memory 1024 count base := by
    rw [hmem]; exact hbase
  have hmod' : Limbs.Represents entry.memory 0 count modulus := by
    rw [hmem]; exact hmodulus
  obtain ⟨hres, _, hmodAfter⟩ :=
    BigMul.mulApplied_represents_product entry 2048 count acc acc modulus 1347
      (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
        (exponentBit byte j) j rest)
      hcount (by omega) hmodulusPos hmodulusBound haccReduced hacc' hacc' hmod'
  have hbaseAfter : Limbs.Represents
      (squareApplied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 1024 count base := by
    simpa [squareApplied, ← hentry, word_2048, word_3072, word_0] using
      BigMul.mulApplied_preserves_region entry (UInt256.ofNat 2048) count 1024
        base 1347
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hcount (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        hbase'
  have hres' : Limbs.Represents
      (squareApplied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 3072 count
      (acc * acc % modulus) := by
    simpa [squareApplied, ← hentry, word_2048, word_3072, word_0] using hres
  have hmodAfter' : Limbs.Represents
      (squareApplied s accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 0 count modulus := by
    simpa [squareApplied, ← hentry, word_2048, word_3072, word_0] using hmodAfter
  have hsqAcc : Limbs.Represents sq.memory 2048 count (acc * acc % modulus) := by
    rw [hsq]; simp only [squareCopied, word_2048, word_3072, word_0]
    exact BigHelpers.copyMemory_represents _ 2048 3072 count _ hres'
      (by omega) (by omega) (Or.inl (by omega))
  have hsqBase : Limbs.Represents sq.memory 1024 count base := by
    rw [hsq]; simp only [squareCopied, word_2048, word_3072, word_0]
    exact BigHelpers.represents_copyMemory_disjoint_region _ 2048 3072 1024
      count base (by omega) (Or.inr (by omega)) hbaseAfter
  have hsqMod : Limbs.Represents sq.memory 0 count modulus := by
    rw [hsq]; simp only [squareCopied, word_2048, word_3072, word_0]
    exact BigHelpers.represents_copyMemory_disjoint_region _ 2048 3072 0
      count modulus (by omega) (Or.inr (by omega)) hmodAfter'
  -- now the multiply
  set pentry := productEntry sq accumulatorWord count b e m baseOff expOff rest
    1 i offset byte (exponentBit byte j) j with hpentry
  have hpmem : pentry.memory = sq.memory := by
    simp [hpentry, productEntry, incJEntry]
  have hpacc : Limbs.Represents pentry.memory 2048 count (acc * acc % modulus) := by
    rw [hpmem]; exact hsqAcc
  have hpbase : Limbs.Represents pentry.memory 1024 count base := by
    rw [hpmem]; exact hsqBase
  have hpmod : Limbs.Represents pentry.memory 0 count modulus := by
    rw [hpmem]; exact hsqMod
  obtain ⟨pres, _, pmodAfter⟩ :=
    BigMul.mulApplied_represents_product pentry 1024 count (acc * acc % modulus)
      base modulus 1387
      (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
        (exponentBit byte j) j rest)
      hcount (by omega) hmodulusPos hmodulusBound (Nat.mod_lt _ hmodulusPos)
      hpacc hpbase hpmod
  have pbaseAfter : Limbs.Represents
      (productApplied sq accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 1024 count base := by
    simpa [productApplied, ← hpentry, word_2048, word_1024, word_3072, word_0]
      using BigMul.mulApplied_preserves_region pentry (UInt256.ofNat 1024) count
        1024 base 1387
        (bitFrame accumulatorWord count b e m baseOff expOff 1 i offset byte
          (exponentBit byte j) j rest)
        hcount (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        hpbase
  have pres' : Limbs.Represents
      (productApplied sq accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 3072 count
      ((acc * acc % modulus) * base % modulus) := by
    simpa [productApplied, ← hpentry, word_2048, word_1024, word_3072, word_0]
      using pres
  have pmodAfter' : Limbs.Represents
      (productApplied sq accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j).memory 0 count modulus := by
    simpa [productApplied, ← hpentry, word_2048, word_1024, word_3072, word_0]
      using pmodAfter
  have hstep : bitStep s accumulatorWord count b e m baseOff expOff rest 1 i
      offset byte j =
      productCopied sq accumulatorWord count b e m baseOff expOff rest 1 i
        offset byte (exponentBit byte j) j := by
    unfold bitStep
    rw [if_pos rfl, if_pos hbit]
  have hval : bitValue modulus base byte 1 j acc =
      (acc * acc % modulus) * base % modulus := by
    unfold bitValue
    rw [if_pos rfl, if_neg (by omega : ¬ (exponentBit byte j).toNat = 0)]
  rw [hstep, hval]
  simp only [productCopied, word_2048, word_1024, word_3072, word_0]
  refine ⟨?_, ?_, ?_⟩
  · exact BigHelpers.copyMemory_represents _ 2048 3072 count _ pres'
      (by omega) (by omega) (Or.inl (by omega))
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 2048 3072 1024
      count base (by omega) (Or.inr (by omega)) pbaseAfter
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 2048 3072 0
      count modulus (by omega) (Or.inr (by omega)) pmodAfter'

/-- The accumulator stays reduced. -/
theorem bitValue_lt (modulus base : Nat) (byte : UInt256) (started j acc : Nat)
    (hmod : 0 < modulus) (hacc : acc < modulus) (hbase : base < modulus) :
    bitValue modulus base byte started j acc < modulus := by
  unfold bitValue
  split
  · split <;> exact Nat.mod_lt _ hmod
  · split
    · exact hacc
    · exact hbase

/-- **Per-bit representation**, for either value of `started`. -/
theorem bitStep_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (j : Nat)
    (hstarted : started < 2) (hcount : count ≤ 32)
    (acc base modulus : Nat) (hmodulusPos : 0 < modulus)
    (hmodulusBound : modulus < Limbs.radix ^ count) (haccReduced : acc < modulus)
    (hbaseReduced : base < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest started i
          offset byte j).memory 2048 count
        (bitValue modulus base byte started j acc) ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest started i
          offset byte j).memory 1024 count base ∧
      Limbs.Represents
        (bitStep s accumulatorWord count b e m baseOff expOff rest started i
          offset byte j).memory 0 count modulus := by
  interval_cases started
  · rcases exponentBit_eq_zero_or_one byte j with hbit | hbit
    · exact bitSkip_represents s accumulatorWord count b e m baseOff expOff rest
        i offset byte j hbit acc base modulus hacc hbase hmodulus
    · exact bitSeed_represents s accumulatorWord count b e m baseOff expOff rest
        i offset byte j hbit hcount acc base modulus hbase hmodulus
  · rcases exponentBit_eq_zero_or_one byte j with hbit | hbit
    · exact bitSquare_represents s accumulatorWord count b e m baseOff expOff
        rest i offset byte j hbit hcount acc base modulus hmodulusPos
        hmodulusBound haccReduced hacc hbase hmodulus
    · exact bitSquareMul_represents s accumulatorWord count b e m baseOff expOff
        rest i offset byte j hbit hcount acc base modulus hmodulusPos
        hmodulusBound haccReduced hbaseReduced hacc hbase hmodulus

/-- **Representation through all eight bits of a byte.** -/
theorem stateAfter_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (offset byte : UInt256) (steps : Nat)
    (hstarted : started < 2) (hcount : count ≤ 32)
    (acc base modulus : Nat) (hmodulusPos : 0 < modulus)
    (hmodulusBound : modulus < Limbs.radix ^ count) (haccReduced : acc < modulus)
    (hbaseReduced : base < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
          offset byte steps).memory 2048 count
        (accAfter modulus base byte started acc steps) ∧
      Limbs.Represents
        (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
          offset byte steps).memory 1024 count base ∧
      Limbs.Represents
        (stateAfter s accumulatorWord count b e m baseOff expOff rest started i
          offset byte steps).memory 0 count modulus ∧
      accAfter modulus base byte started acc steps < modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus, haccReduced⟩
  | succ steps ih =>
      obtain ⟨ha, hb, hm, hlt⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (bitStep_represents _ accumulatorWord count b e m baseOff expOff
          rest (startedAfter started byte steps) i offset byte steps
          (startedAfter_lt_two started byte steps hstarted) hcount _ base modulus
          hmodulusPos hmodulusBound hlt hbaseReduced ha hb hm).1
      · exact (bitStep_represents _ accumulatorWord count b e m baseOff expOff
          rest (startedAfter started byte steps) i offset byte steps
          (startedAfter_lt_two started byte steps hstarted) hcount _ base modulus
          hmodulusPos hmodulusBound hlt hbaseReduced ha hb hm).2.1
      · exact (bitStep_represents _ accumulatorWord count b e m baseOff expOff
          rest (startedAfter started byte steps) i offset byte steps
          (startedAfter_lt_two started byte steps hstarted) hcount _ base modulus
          hmodulusPos hmodulusBound hlt hbaseReduced ha hb hm).2.2
      · exact bitValue_lt modulus base byte _ steps _ hmodulusPos hlt hbaseReduced

/-- Accumulator value after consuming `i` whole exponent bytes. -/
def accAfterBytes (s : State) (modulus base : Nat) (expOff started acc : Nat) :
    Nat → Nat
  | 0 => acc
  | i + 1 =>
      accAfter modulus base (byteAt s expOff i)
        (startedAfterBytes s expOff started i)
        (accAfterBytes s modulus base expOff started acc i) 8

/-- **Representation through every exponent byte.** -/
theorem bytesState_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) (hstarted : started < 2) (hcount : count ≤ 32)
    (acc base modulus : Nat) (hmodulusPos : 0 < modulus)
    (hmodulusBound : modulus < Limbs.radix ^ count) (haccReduced : acc < modulus)
    (hbaseReduced : base < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bytesState s accumulatorWord count b e m baseOff expOff rest started
          i).memory 2048 count
        (accAfterBytes s modulus base expOff started acc i) ∧
      Limbs.Represents
        (bytesState s accumulatorWord count b e m baseOff expOff rest started
          i).memory 1024 count base ∧
      Limbs.Represents
        (bytesState s accumulatorWord count b e m baseOff expOff rest started
          i).memory 0 count modulus ∧
      accAfterBytes s modulus base expOff started acc i < modulus := by
  induction i with
  | zero => exact ⟨hacc, hbase, hmodulus, haccReduced⟩
  | succ i ih =>
      obtain ⟨ha, hb, hm, hlt⟩ := ih
      exact stateAfter_represents _ accumulatorWord count b e m baseOff expOff
        rest (startedAfterBytes s expOff started i) i
        (UInt256.ofNat (expOff + i)) (byteAt s expOff i) 8
        (startedAfterBytes_lt_two s expOff started i hstarted) hcount _ base
        modulus hmodulusPos hmodulusBound hlt hbaseReduced ha hb hm

/-! ## Tying the accumulator to exponentiation

`accAfter` is defined operationally — square, or square-and-multiply, per bit.
It computes `base ^ v mod modulus`, where `v` is the numeric value of the
exponent bits consumed so far. The `started` flag is exactly the predicate
`v > 0`, which is what lets the optimized branches (skip and seed) agree with
the arithmetic ones. -/

/-- Numeric value of the exponent bits consumed so far. -/
def prefixAfter (byte : UInt256) (v0 : Nat) : Nat → Nat
  | 0 => v0
  | j + 1 => 2 * prefixAfter byte v0 j + (exponentBit byte j).toNat

theorem exponentBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (exponentBit byte j).toNat = 0 ∨ (exponentBit byte j).toNat = 1 := by
  rcases exponentBit_eq_zero_or_one byte j with h | h <;> rw [h] <;>
    simp [Challenge.EvmProof.Word.word_toNat_ofNat]

/-- **The core arithmetic fact.** The accumulator holds `base ^ v mod modulus`,
and `started` tracks `v > 0`, jointly maintained across the bits of a byte. -/
theorem accAfter_spec (modulus base : Nat) (hmod : 0 < modulus)
    (hbase : base < modulus) (byte : UInt256) (started v0 : Nat)
    (hinv : started = 1 ↔ 0 < v0) (hstarted : started < 2) (steps : Nat) :
    accAfter modulus base byte started (base ^ v0 % modulus) steps
        = base ^ prefixAfter byte v0 steps % modulus ∧
      (startedAfter started byte steps = 1 ↔ 0 < prefixAfter byte v0 steps) := by
  induction steps with
  | zero => exact ⟨rfl, hinv⟩
  | succ steps ih =>
      obtain ⟨hacc, hst⟩ := ih
      set st := startedAfter started byte steps with hstDef
      set v := prefixAfter byte v0 steps with hvDef
      have hstLt : st < 2 := startedAfter_lt_two started byte steps hstarted
      refine ⟨?_, ?_⟩
      · show bitValue modulus base byte st steps
            (accAfter modulus base byte started (base ^ v0 % modulus) steps)
          = base ^ (2 * v + (exponentBit byte steps).toNat) % modulus
        rw [hacc]
        unfold bitValue
        rcases exponentBit_toNat_le_one byte steps with hbit | hbit
        · -- bit clear
          by_cases hs : st = 1
          · rw [if_pos hs, if_pos hbit, hbit, Nat.add_zero]
            rw [← Nat.mul_mod, ← pow_add, show v + v = 2 * v from by omega]
          · rw [if_neg hs, if_pos hbit, hbit, Nat.add_zero]
            have hv : v = 0 := by
              by_contra hne
              exact hs (hst.mpr (Nat.pos_of_ne_zero hne))
            rw [hv]
        · -- bit set
          by_cases hs : st = 1
          · rw [if_pos hs, if_neg (by omega : ¬ (exponentBit byte steps).toNat = 0),
              hbit]
            rw [← Nat.mul_mod, Nat.mod_mul_mod, ← pow_add, ← pow_succ,
              show v + v + 1 = 2 * v + 1 from by omega]
          · rw [if_neg hs, if_neg (by omega : ¬ (exponentBit byte steps).toNat = 0),
              hbit]
            have hv : v = 0 := by
              by_contra hne
              exact hs (hst.mpr (Nat.pos_of_ne_zero hne))
            rw [hv, Nat.mul_zero, Nat.zero_add, pow_one, Nat.mod_eq_of_lt hbase]
      · show (nextStarted st byte steps = 1) ↔
            0 < 2 * v + (exponentBit byte steps).toNat
        unfold nextStarted
        rcases exponentBit_toNat_le_one byte steps with hbit | hbit
        · have hb0 : exponentBit byte steps = UInt256.ofNat 0 := by
            rcases exponentBit_eq_zero_or_one byte steps with h | h
            · exact h
            · rw [h] at hbit; simp [Challenge.EvmProof.Word.word_toNat_ofNat] at hbit
          by_cases hs : st = 1
          · rw [if_pos hs]
            exact ⟨fun _ => by have := hst.mp hs; omega, fun _ => rfl⟩
          · rw [if_neg hs, if_neg (by rw [hb0]; exact word_zero_ne_one)]
            have hv : v = 0 := by
              by_contra hne; exact hs (hst.mpr (Nat.pos_of_ne_zero hne))
            simp [hv, hbit]
        · have hb1 : exponentBit byte steps = UInt256.ofNat 1 := by
            rcases exponentBit_eq_zero_or_one byte steps with h | h
            · rw [h] at hbit; simp [Challenge.EvmProof.Word.word_toNat_ofNat] at hbit
            · exact h
          by_cases hs : st = 1
          · rw [if_pos hs]; exact ⟨fun _ => by omega, fun _ => rfl⟩
          · rw [if_neg hs, if_pos hb1]
            exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- My `exponentBit` is the one `Word` already defines, so the reference's bit
arithmetic applies verbatim. -/
theorem exponentBit_eq_word (byte : UInt256) (j : Nat) :
    exponentBit byte j = BitPrefix.exponentBit byte j := rfl

theorem exponentBit_toNat_eq_nat (byte : UInt256) (j : Nat) (hj : j < 8) :
    (exponentBit byte j).toNat = BitPrefix.exponentBitNat byte j := by
  rw [exponentBit_eq_word]
  have h := congrArg UInt256.toNat (BitPrefix.exponentBit_eq byte j hj)
  have hbit := BitPrefix.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : BitPrefix.exponentBitNat byte j < 2 ^ 256)] at h
  exact h

/-- `prefixAfter` is the accumulated prefix shifted over the byte's own bits. -/
theorem prefixAfter_eq (byte : UInt256) (v0 steps : Nat) (hsteps : steps ≤ 8) :
    prefixAfter byte v0 steps = 2 ^ steps * v0 + BitPrefix.bitPrefix byte steps := by
  induction steps with
  | zero => simp [prefixAfter, BitPrefix.bitPrefix]
  | succ steps ih =>
      rw [prefixAfter, ih (by omega), BitPrefix.bitPrefix,
        exponentBit_toNat_eq_nat byte steps (by omega)]
      ring

/-- **One exponent byte contributes its own value**, base-256. -/
theorem prefixAfter_eight (byte : UInt256) (v0 : Nat)
    (hbyte : byte.toNat < 256) :
    prefixAfter byte v0 8 = 256 * v0 + byte.toNat := by
  rw [prefixAfter_eq byte v0 8 (by omega), BitPrefix.bitPrefix_eight byte hbyte]
  norm_num

/-- Numeric value of the exponent bytes consumed so far, base-256. -/
def expValueAfter (s : State) (expOff : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => 256 * expValueAfter s expOff i + (byteAt s expOff i).toNat

/-- **The accumulator computes the modular power.** After `i` exponent bytes the
accumulator holds `base ^ (value of those bytes) mod modulus`, starting from
`started = 0` and `acc = 1 mod modulus`. -/
theorem accAfterBytes_spec (s : State) (modulus base : Nat) (hmod : 0 < modulus)
    (hbase : base < modulus) (expOff : Nat)
    (hbytes : ∀ k, (byteAt s expOff k).toNat < 256) (i : Nat) :
    accAfterBytes s modulus base expOff 0 (base ^ 0 % modulus) i
        = base ^ expValueAfter s expOff i % modulus ∧
      (startedAfterBytes s expOff 0 i = 1 ↔ 0 < expValueAfter s expOff i) := by
  induction i with
  | zero =>
      refine ⟨rfl, ?_⟩
      simp [startedAfterBytes, expValueAfter]
  | succ i ih =>
      obtain ⟨hacc, hst⟩ := ih
      have h := accAfter_spec modulus base hmod hbase (byteAt s expOff i)
        (startedAfterBytes s expOff 0 i) (expValueAfter s expOff i) hst
        (startedAfterBytes_lt_two s expOff 0 i (by omega)) 8
      have hpre : prefixAfter (byteAt s expOff i) (expValueAfter s expOff i) 8
          = expValueAfter s expOff (i + 1) :=
        prefixAfter_eight _ _ (hbytes i)
      refine ⟨?_, ?_⟩
      · show accAfter modulus base (byteAt s expOff i)
            (startedAfterBytes s expOff 0 i)
            (accAfterBytes s modulus base expOff 0 (base ^ 0 % modulus) i) 8 = _
        rw [hacc, h.1, hpre]
      · show (startedAfter (startedAfterBytes s expOff 0 i)
            (byteAt s expOff i) 8 = 1) ↔ _
        rw [h.2, hpre]

@[simp] theorem exponentDone_executionEnv (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started : Nat) :
    (exponentDone s accumulatorWord count b e m baseOff expOff rest
      started).executionEnv = s.executionEnv := by
  simp [exponentDone]

@[simp] theorem exponentDone_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (started : Nat) :
    (exponentDone s accumulatorWord count b e m baseOff expOff rest started).halt
      = s.halt := by
  simp [exponentDone]

/-! ## Whole-phase trace

`gasSteps_exponentPhase` is the single entry point the rest of the proof needs:
from the exponent-loop entry all the way to the frame the serializer expects at
pc 1118, with the `started` slot pushed and popped inside. -/

/-- Entry stub plus loop initialisation. -/
def gasSteps_startExponent (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest)
      (byteLoopState s accumulatorWord count b e m baseOff expOff rest 0 0) :=
  (sound startExponentPath
    (run_startExponent s accumulatorWord count b e m baseOff expOff rest hcap
      hcode hrun) hcode hfork hrun hnp).trans
  (sound startExponentBodyPath
    (run_startExponentBody s accumulatorWord count b e m baseOff expOff rest
      hcap hrun) hcode hfork hrun hnp)

/-- The whole exponentiation phase: entry, every bit of every byte, then the
hand-back to the serializer with `started` dropped. -/
def gasSteps_exponentPhase (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 967) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest)
      (serializerHandoff
        (bytesState s accumulatorWord count b e m baseOff expOff rest 0 e)
        accumulatorWord count b e m baseOff expOff rest) :=
  (gasSteps_startExponent s accumulatorWord count b e m baseOff expOff rest
    (by omega) hcode hfork hrun hnp).trans <|
  (gasSteps_byteLoop s accumulatorWord count b e m baseOff expOff rest 0
    hcap hcount he hoff (by omega) hcode hfork hrun hnp).trans <|
  (sound outerGuardPath
    (run_outerFinishGuard
      (bytesState s accumulatorWord count b e m baseOff expOff rest 0 e)
      accumulatorWord count b e m baseOff expOff rest
      (startedAfterBytes s expOff 0 e) (by omega) he
      (by simpa using hcode) (by simpa using hrun))
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp)).trans
  (sound exponentExitPath
    (run_exponentExit
      (bytesState s accumulatorWord count b e m baseOff expOff rest 0 e)
      accumulatorWord count b e m baseOff expOff rest
      (startedAfterBytes s expOff 0 e) (by omega)
      (by simpa using hcode) (by simpa using hrun))
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp))

@[simp] theorem bytesState_callStack (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (started i : Nat) :
    (bytesState s accumulatorWord count b e m baseOff expOff rest started
      i).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [bytesState, byteStep, ih]

end Challenge.Modexp.Submission.Proofs.Bytecode.ExpCore
