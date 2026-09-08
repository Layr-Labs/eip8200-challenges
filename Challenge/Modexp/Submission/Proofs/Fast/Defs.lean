import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The appended Montgomery path occupies instruction indices 977..1741
(pc 1314..2862).  This module fixes the `Located` constructors, the
program-counter table and the jump-destination facts those blocks need.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩


/-! Private prototype: local-prefix PC certificates.

This is intentionally kept in the submission-local namespace.  A future
tracked integration can place these facts in `Fast.Defs` or another editable
submission helper; `Challenge.EvmProof.Program` remains unchanged.
-/

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

private theorem fastPCAnchor0 :
    Artifact.submissionArtifact.instructionPC 977 = 1314 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1017 = 1371 := by
  calc
    Artifact.submissionArtifact.instructionPC 1017 =
        Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 977).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 977 40
    _ = 1371 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1057 = 1428 := by
  calc
    Artifact.submissionArtifact.instructionPC 1057 =
        Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1017).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1017 40
    _ = 1428 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1097 = 1476 := by
  calc
    Artifact.submissionArtifact.instructionPC 1097 =
        Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1057).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1057 40
    _ = 1476 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1137 = 1532 := by
  calc
    Artifact.submissionArtifact.instructionPC 1137 =
        Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1097).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1097 40
    _ = 1532 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1177 = 1612 := by
  calc
    Artifact.submissionArtifact.instructionPC 1177 =
        Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1137).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1137 40
    _ = 1612 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1217 = 1669 := by
  calc
    Artifact.submissionArtifact.instructionPC 1217 =
        Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1177).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1177 40
    _ = 1669 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1257 = 1738 := by
  calc
    Artifact.submissionArtifact.instructionPC 1257 =
        Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1217).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1217 40
    _ = 1738 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1297 = 1809 := by
  calc
    Artifact.submissionArtifact.instructionPC 1297 =
        Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1257).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1257 40
    _ = 1809 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1337 = 1880 := by
  calc
    Artifact.submissionArtifact.instructionPC 1337 =
        Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1297).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1297 40
    _ = 1880 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1377 = 1937 := by
  calc
    Artifact.submissionArtifact.instructionPC 1377 =
        Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1337).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1337 40
    _ = 1937 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor10_1 :
    Artifact.submissionArtifact.instructionPC 1417 = 1986 := by
  calc
    Artifact.submissionArtifact.instructionPC 1417 =
        Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1377).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1377 40
    _ = 1986 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1423 = 2003 := by
  calc
    Artifact.submissionArtifact.instructionPC 1423 =
        Artifact.submissionArtifact.instructionPC 1417 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1417).take
              6)).length :=
      instructionPC_add Artifact.submissionArtifact 1417 6
    _ = 2003 := by
      rw [fastPCAnchor10_1]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1426 = 2008 := by
  calc
    Artifact.submissionArtifact.instructionPC 1426 =
        Artifact.submissionArtifact.instructionPC 1423 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1423).take
              3)).length :=
      instructionPC_add Artifact.submissionArtifact 1423 3
    _ = 2008 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1455 = 2049 := by
  calc
    Artifact.submissionArtifact.instructionPC 1455 =
        Artifact.submissionArtifact.instructionPC 1426 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1426).take
              29)).length :=
      instructionPC_add Artifact.submissionArtifact 1426 29
    _ = 2049 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor13_1 :
    Artifact.submissionArtifact.instructionPC 1495 = 2103 := by
  calc
    Artifact.submissionArtifact.instructionPC 1495 =
        Artifact.submissionArtifact.instructionPC 1455 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1455).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1455 40
    _ = 2103 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor13_2 :
    Artifact.submissionArtifact.instructionPC 1535 = 2144 := by
  calc
    Artifact.submissionArtifact.instructionPC 1535 =
        Artifact.submissionArtifact.instructionPC 1495 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1495).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1495 40
    _ = 2144 := by
      rw [fastPCAnchor13_1]
      rfl

private theorem fastPCAnchor13_3 :
    Artifact.submissionArtifact.instructionPC 1575 = 2185 := by
  calc
    Artifact.submissionArtifact.instructionPC 1575 =
        Artifact.submissionArtifact.instructionPC 1535 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1535).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1535 40
    _ = 2185 := by
      rw [fastPCAnchor13_2]
      rfl

private theorem fastPCAnchor13_4 :
    Artifact.submissionArtifact.instructionPC 1615 = 2226 := by
  calc
    Artifact.submissionArtifact.instructionPC 1615 =
        Artifact.submissionArtifact.instructionPC 1575 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1575).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1575 40
    _ = 2226 := by
      rw [fastPCAnchor13_3]
      rfl

private theorem fastPCAnchor13_5 :
    Artifact.submissionArtifact.instructionPC 1655 = 2267 := by
  calc
    Artifact.submissionArtifact.instructionPC 1655 =
        Artifact.submissionArtifact.instructionPC 1615 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1615).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1615 40
    _ = 2267 := by
      rw [fastPCAnchor13_4]
      rfl

private theorem fastPCAnchor13_6 :
    Artifact.submissionArtifact.instructionPC 1695 = 2308 := by
  calc
    Artifact.submissionArtifact.instructionPC 1695 =
        Artifact.submissionArtifact.instructionPC 1655 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1655).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1655 40
    _ = 2308 := by
      rw [fastPCAnchor13_5]
      rfl

private theorem fastPCAnchor13_7 :
    Artifact.submissionArtifact.instructionPC 1735 = 2349 := by
  calc
    Artifact.submissionArtifact.instructionPC 1735 =
        Artifact.submissionArtifact.instructionPC 1695 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1695).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1695 40
    _ = 2349 := by
      rw [fastPCAnchor13_6]
      rfl

private theorem fastPCAnchor13_8 :
    Artifact.submissionArtifact.instructionPC 1775 = 2390 := by
  calc
    Artifact.submissionArtifact.instructionPC 1775 =
        Artifact.submissionArtifact.instructionPC 1735 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1735).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1735 40
    _ = 2390 := by
      rw [fastPCAnchor13_7]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1815 = 2435 := by
  calc
    Artifact.submissionArtifact.instructionPC 1815 =
        Artifact.submissionArtifact.instructionPC 1775 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1775).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1775 40
    _ = 2435 := by
      rw [fastPCAnchor13_8]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1823 = 2445 := by
  calc
    Artifact.submissionArtifact.instructionPC 1823 =
        Artifact.submissionArtifact.instructionPC 1815 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1815).take
              8)).length :=
      instructionPC_add Artifact.submissionArtifact 1815 8
    _ = 2445 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor15_1 :
    Artifact.submissionArtifact.instructionPC 1863 = 2499 := by
  calc
    Artifact.submissionArtifact.instructionPC 1863 =
        Artifact.submissionArtifact.instructionPC 1823 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1823).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1823 40
    _ = 2499 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1865 = 2501 := by
  calc
    Artifact.submissionArtifact.instructionPC 1865 =
        Artifact.submissionArtifact.instructionPC 1863 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1863).take
              2)).length :=
      instructionPC_add Artifact.submissionArtifact 1863 2
    _ = 2501 := by
      rw [fastPCAnchor15_1]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1905 = 2639 := by
  calc
    Artifact.submissionArtifact.instructionPC 1905 =
        Artifact.submissionArtifact.instructionPC 1865 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1865).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1865 40
    _ = 2639 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1945 = 2693 := by
  calc
    Artifact.submissionArtifact.instructionPC 1945 =
        Artifact.submissionArtifact.instructionPC 1905 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1905).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1905 40
    _ = 2693 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1985 = 2871 := by
  calc
    Artifact.submissionArtifact.instructionPC 1985 =
        Artifact.submissionArtifact.instructionPC 1945 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1945).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1945 40
    _ = 2871 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1990 = 2876 := by
  calc
    Artifact.submissionArtifact.instructionPC 1990 =
        Artifact.submissionArtifact.instructionPC 1985 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1985).take
              5)).length :=
      instructionPC_add Artifact.submissionArtifact 1985 5
    _ = 2876 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 2016 = 2914 := by
  calc
    Artifact.submissionArtifact.instructionPC 2016 =
        Artifact.submissionArtifact.instructionPC 1990 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1990).take
              26)).length :=
      instructionPC_add Artifact.submissionArtifact 1990 26
    _ = 2914 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 2029 = 2935 := by
  calc
    Artifact.submissionArtifact.instructionPC 2029 =
        Artifact.submissionArtifact.instructionPC 2016 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2016).take
              13)).length :=
      instructionPC_add Artifact.submissionArtifact 2016 13
    _ = 2935 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 2064 = 2984 := by
  calc
    Artifact.submissionArtifact.instructionPC 2064 =
        Artifact.submissionArtifact.instructionPC 2029 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2029).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 2029 35
    _ = 2984 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 977 ≤ i) (hii : i ≤ 1016) :
    Artifact.submissionArtifact.instructionPC i =
      [1314,1315,1317,1318,1319,1321,1322,1323,1326,1327,1329,1330,1331,1332,1333,1336,1337,1338,1341,1342,1343,1344,1347,1348,1349,1352,1353,1354,1356,1357,1359,1360,1361,1363,1364,1365,1366,1367,1369,1370][i - 977]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (977 + (i - 977)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 977).take
              (i - 977))).length :=
      instructionPC_add Artifact.submissionArtifact 977 (i - 977)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1017 ≤ i) (hii : i ≤ 1056) :
    Artifact.submissionArtifact.instructionPC i =
      [1371,1372,1373,1375,1376,1377,1378,1379,1380,1381,1384,1385,1387,1388,1389,1390,1391,1392,1394,1395,1396,1399,1400,1401,1404,1405,1406,1409,1410,1411,1413,1414,1417,1418,1419,1421,1422,1423,1424,1427][i - 1017]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1017 + (i - 1017)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1017).take
              (i - 1017))).length :=
      instructionPC_add Artifact.submissionArtifact 1017 (i - 1017)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1096) :
    Artifact.submissionArtifact.instructionPC i =
      [1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1453,1454,1455,1456,1458,1459,1460,1461,1462,1463,1465,1466,1467,1468,1469,1470,1472,1473,1474,1475][i - 1057]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1057 + (i - 1057)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1057).take
              (i - 1057))).length :=
      instructionPC_add Artifact.submissionArtifact 1057 (i - 1057)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1097 ≤ i) (hii : i ≤ 1136) :
    Artifact.submissionArtifact.instructionPC i =
      [1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1505,1507,1508,1509,1510,1511,1514,1515,1516,1517,1519,1522,1523,1526,1529][i - 1097]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1097 + (i - 1097)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1097).take
              (i - 1097))).length :=
      instructionPC_add Artifact.submissionArtifact 1097 (i - 1097)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1137 ≤ i) (hii : i ≤ 1176) :
    Artifact.submissionArtifact.instructionPC i =
      [1532,1533,1534,1537,1538,1541,1544,1545,1548,1551,1554,1555,1556,1559,1560,1563,1566,1567,1569,1570,1573,1576,1579,1582,1585,1586,1587,1588,1589,1590,1592,1593,1596,1597,1600,1601,1604,1605,1606,1609][i - 1137]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1137 + (i - 1137)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1137).take
              (i - 1137))).length :=
      instructionPC_add Artifact.submissionArtifact 1137 (i - 1137)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1177 ≤ i) (hii : i ≤ 1216) :
    Artifact.submissionArtifact.instructionPC i =
      [1612,1615,1616,1617,1618,1619,1622,1623,1624,1625,1626,1630,1631,1632,1633,1634,1635,1638,1639,1642,1643,1645,1647,1649,1651,1653,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668][i - 1177]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1177 + (i - 1177)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1177).take
              (i - 1177))).length :=
      instructionPC_add Artifact.submissionArtifact 1177 (i - 1177)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1217 ≤ i) (hii : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1669,1670,1671,1672,1673,1676,1677,1680,1683,1686,1689,1692,1693,1694,1695,1696,1697,1699,1700,1701,1702,1704,1705,1706,1707,1710,1711,1712,1715,1718,1721,1724,1727,1728,1729,1731,1732,1735,1736,1737][i - 1217]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1217 + (i - 1217)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1217).take
              (i - 1217))).length :=
      instructionPC_add Artifact.submissionArtifact 1217 (i - 1217)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1257 ≤ i) (hii : i ≤ 1296) :
    Artifact.submissionArtifact.instructionPC i =
      [1738,1739,1742,1745,1748,1751,1754,1755,1756,1757,1760,1761,1763,1765,1767,1769,1770,1771,1772,1773,1774,1777,1778,1781,1782,1783,1784,1785,1786,1787,1789,1790,1793,1796,1799,1802,1805,1806,1807,1808][i - 1257]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1257 + (i - 1257)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1257).take
              (i - 1257))).length :=
      instructionPC_add Artifact.submissionArtifact 1257 (i - 1257)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1297 ≤ i) (hii : i ≤ 1336) :
    Artifact.submissionArtifact.instructionPC i =
      [1809,1810,1811,1814,1815,1818,1821,1824,1827,1830,1831,1832,1833,1835,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1852,1854,1855,1858,1859,1860,1863,1866,1869,1872,1875,1876,1877,1878,1879][i - 1297]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1297 + (i - 1297)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1297).take
              (i - 1297))).length :=
      instructionPC_add Artifact.submissionArtifact 1297 (i - 1297)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1337 ≤ i) (hii : i ≤ 1376) :
    Artifact.submissionArtifact.instructionPC i =
      [1880,1883,1884,1885,1886,1887,1888,1891,1892,1893,1894,1895,1896,1899,1900,1901,1902,1903,1904,1905,1906,1907,1910,1911,1912,1915,1916,1919,1920,1921,1922,1925,1926,1927,1929,1930,1931,1932,1935,1936][i - 1337]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1337 + (i - 1337)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1337).take
              (i - 1337))).length :=
      instructionPC_add Artifact.submissionArtifact 1337 (i - 1337)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1416) :
    Artifact.submissionArtifact.instructionPC i =
      [1937,1938,1939,1940,1942,1943,1944,1945,1946,1947,1948,1951,1952,1953,1955,1956,1957,1960,1961,1962,1963,1964,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1978,1979,1980,1981,1982,1983,1984,1985][i - 1377]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1377 + (i - 1377)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1377).take
              (i - 1377))).length :=
      instructionPC_add Artifact.submissionArtifact 1377 (i - 1377)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC10_1 (i : Nat) (hi : 1417 ≤ i) (hii : i ≤ 1422) :
    Artifact.submissionArtifact.instructionPC i =
      [1986,1991,1992,1993,2001,2002][i - 1417]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1417 + (i - 1417)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1417 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1417).take
              (i - 1417))).length :=
      instructionPC_add Artifact.submissionArtifact 1417 (i - 1417)
    _ = _ := by
      rw [fastPCAnchor10_1]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1423 ≤ i) (hii : i ≤ 1425) :
    Artifact.submissionArtifact.instructionPC i =
      [2003,2004,2007][i - 1423]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1423 + (i - 1423)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1423 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1423).take
              (i - 1423))).length :=
      instructionPC_add Artifact.submissionArtifact 1423 (i - 1423)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1426 ≤ i) (hii : i ≤ 1454) :
    Artifact.submissionArtifact.instructionPC i =
      [2008,2009,2010,2011,2012,2015,2016,2017,2018,2021,2022,2023,2026,2027,2030,2031,2032,2035,2036,2037,2038,2041,2042,2043,2044,2045,2046,2047,2048][i - 1426]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1426 + (i - 1426)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1426 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1426).take
              (i - 1426))).length :=
      instructionPC_add Artifact.submissionArtifact 1426 (i - 1426)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1455 ≤ i) (hii : i ≤ 1494) :
    Artifact.submissionArtifact.instructionPC i =
      [2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2064,2065,2067,2068,2069,2072,2073,2075,2076,2077,2078,2079,2082,2083,2085,2086,2088,2089,2092,2093,2096,2097,2098,2099,2100,2101,2102][i - 1455]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1455 + (i - 1455)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1455 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1455).take
              (i - 1455))).length :=
      instructionPC_add Artifact.submissionArtifact 1455 (i - 1455)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_1 (i : Nat) (hi : 1495 ≤ i) (hii : i ≤ 1534) :
    Artifact.submissionArtifact.instructionPC i =
      [2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143][i - 1495]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1495 + (i - 1495)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1495 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1495).take
              (i - 1495))).length :=
      instructionPC_add Artifact.submissionArtifact 1495 (i - 1495)
    _ = _ := by
      rw [fastPCAnchor13_1]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_2 (i : Nat) (hi : 1535 ≤ i) (hii : i ≤ 1574) :
    Artifact.submissionArtifact.instructionPC i =
      [2144,2145,2146,2147,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,2169,2170,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184][i - 1535]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1535 + (i - 1535)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1535 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1535).take
              (i - 1535))).length :=
      instructionPC_add Artifact.submissionArtifact 1535 (i - 1535)
    _ = _ := by
      rw [fastPCAnchor13_2]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_3 (i : Nat) (hi : 1575 ≤ i) (hii : i ≤ 1614) :
    Artifact.submissionArtifact.instructionPC i =
      [2185,2186,2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225][i - 1575]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1575 + (i - 1575)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1575 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1575).take
              (i - 1575))).length :=
      instructionPC_add Artifact.submissionArtifact 1575 (i - 1575)
    _ = _ := by
      rw [fastPCAnchor13_3]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_4 (i : Nat) (hi : 1615 ≤ i) (hii : i ≤ 1654) :
    Artifact.submissionArtifact.instructionPC i =
      [2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2254,2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266][i - 1615]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1615 + (i - 1615)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1615 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1615).take
              (i - 1615))).length :=
      instructionPC_add Artifact.submissionArtifact 1615 (i - 1615)
    _ = _ := by
      rw [fastPCAnchor13_4]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_5 (i : Nat) (hi : 1655 ≤ i) (hii : i ≤ 1694) :
    Artifact.submissionArtifact.instructionPC i =
      [2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,2291,2292,2293,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307][i - 1655]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1655 + (i - 1655)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1655 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1655).take
              (i - 1655))).length :=
      instructionPC_add Artifact.submissionArtifact 1655 (i - 1655)
    _ = _ := by
      rw [fastPCAnchor13_5]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_6 (i : Nat) (hi : 1695 ≤ i) (hii : i ≤ 1734) :
    Artifact.submissionArtifact.instructionPC i =
      [2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348][i - 1695]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1695 + (i - 1695)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1695 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1695).take
              (i - 1695))).length :=
      instructionPC_add Artifact.submissionArtifact 1695 (i - 1695)
    _ = _ := by
      rw [fastPCAnchor13_6]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_7 (i : Nat) (hi : 1735 ≤ i) (hii : i ≤ 1774) :
    Artifact.submissionArtifact.instructionPC i =
      [2349,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389][i - 1735]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1735 + (i - 1735)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1735 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1735).take
              (i - 1735))).length :=
      instructionPC_add Artifact.submissionArtifact 1735 (i - 1735)
    _ = _ := by
      rw [fastPCAnchor13_7]
      interval_cases i <;> rfl

@[simp] theorem fastPC13_8 (i : Nat) (hi : 1775 ≤ i) (hii : i ≤ 1814) :
    Artifact.submissionArtifact.instructionPC i =
      [2390,2391,2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2418,2419,2420,2421,2422,2423,2424,2425,2426,2429,2430,2431,2434][i - 1775]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1775 + (i - 1775)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1775 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1775).take
              (i - 1775))).length :=
      instructionPC_add Artifact.submissionArtifact 1775 (i - 1775)
    _ = _ := by
      rw [fastPCAnchor13_8]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1815 ≤ i) (hii : i ≤ 1822) :
    Artifact.submissionArtifact.instructionPC i =
      [2435,2436,2437,2438,2439,2440,2441,2442][i - 1815]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1815 + (i - 1815)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1815 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1815).take
              (i - 1815))).length :=
      instructionPC_add Artifact.submissionArtifact 1815 (i - 1815)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1823 ≤ i) (hii : i ≤ 1862) :
    Artifact.submissionArtifact.instructionPC i =
      [2445,2446,2447,2448,2451,2452,2453,2456,2457,2458,2461,2462,2463,2464,2465,2466,2467,2470,2471,2472,2473,2474,2475,2476,2479,2480,2481,2484,2485,2486,2487,2488,2490,2491,2492,2493,2494,2495,2497,2498][i - 1823]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1823 + (i - 1823)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1823 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1823).take
              (i - 1823))).length :=
      instructionPC_add Artifact.submissionArtifact 1823 (i - 1823)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC15_1 (i : Nat) (hi : 1863 ≤ i) (hii : i ≤ 1864) :
    Artifact.submissionArtifact.instructionPC i =
      [2499,2500][i - 1863]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1863 + (i - 1863)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1863 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1863).take
              (i - 1863))).length :=
      instructionPC_add Artifact.submissionArtifact 1863 (i - 1863)
    _ = _ := by
      rw [fastPCAnchor15_1]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1865 ≤ i) (hii : i ≤ 1904) :
    Artifact.submissionArtifact.instructionPC i =
      [2501,2502,2503,2504,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2566,2567,2568,2601,2602,2603,2604,2637,2638][i - 1865]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1865 + (i - 1865)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1865 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1865).take
              (i - 1865))).length :=
      instructionPC_add Artifact.submissionArtifact 1865 (i - 1865)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1905 ≤ i) (hii : i ≤ 1944) :
    Artifact.submissionArtifact.instructionPC i =
      [2639,2642,2643,2644,2647,2648,2649,2650,2651,2654,2655,2656,2659,2660,2663,2664,2665,2668,2669,2672,2673,2674,2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692][i - 1905]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1905 + (i - 1905)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1905 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1905).take
              (i - 1905))).length :=
      instructionPC_add Artifact.submissionArtifact 1905 (i - 1905)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1945 ≤ i) (hii : i ≤ 1984) :
    Artifact.submissionArtifact.instructionPC i =
      [2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2738,2739,2740,2773,2774,2775,2776,2809,2810,2811,2814,2815,2816,2819,2820,2821,2822,2823,2824,2827,2828,2829,2862,2863,2866,2867,2870][i - 1945]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1945 + (i - 1945)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1945 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1945).take
              (i - 1945))).length :=
      instructionPC_add Artifact.submissionArtifact 1945 (i - 1945)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1985 ≤ i) (hii : i ≤ 1989) :
    Artifact.submissionArtifact.instructionPC i =
      [2871,2872,2873,2874,2875][i - 1985]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1985 + (i - 1985)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1985 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1985).take
              (i - 1985))).length :=
      instructionPC_add Artifact.submissionArtifact 1985 (i - 1985)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1990 ≤ i) (hii : i ≤ 2015) :
    Artifact.submissionArtifact.instructionPC i =
      [2876,2877,2880,2881,2882,2883,2886,2887,2888,2890,2891,2894,2895,2896,2897,2900,2901,2902,2903,2904,2905,2906,2910,2911,2912,2913][i - 1990]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1990 + (i - 1990)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1990 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1990).take
              (i - 1990))).length :=
      instructionPC_add Artifact.submissionArtifact 1990 (i - 1990)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 2016 ≤ i) (hii : i ≤ 2028) :
    Artifact.submissionArtifact.instructionPC i =
      [2914,2915,2916,2917,2919,2920,2921,2924,2925,2927,2930,2931,2934][i - 2016]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2016 + (i - 2016)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2016 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2016).take
              (i - 2016))).length :=
      instructionPC_add Artifact.submissionArtifact 2016 (i - 2016)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 2029 ≤ i) (hii : i ≤ 2063) :
    Artifact.submissionArtifact.instructionPC i =
      [2935,2936,2937,2940,2941,2942,2943,2944,2945,2946,2947,2950,2951,2953,2956,2957,2958,2959,2960,2962,2963,2964,2965,2967,2968,2969,2970,2972,2973,2974,2976,2977,2979,2980,2983][i - 2029]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2029 + (i - 2029)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2029 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2029).take
              (i - 2029))).length :=
      instructionPC_add Artifact.submissionArtifact 2029 (i - 2029)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 2064 ≤ i) (hii : i ≤ 2078) :
    Artifact.submissionArtifact.instructionPC i =
      [2984,2985,2986,2989,2990,2993,2994,2997,3000,3001,3004,3007,3008,3009,3012][i - 2064]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2064 + (i - 2064)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2064 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2064).take
              (i - 2064))).length :=
      instructionPC_add Artifact.submissionArtifact 2064 (i - 2064)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2495 ≤ i) (hii : i ≤ 2547) :
    Artifact.submissionArtifact.instructionPC i =
      ([3619,3620,3621,3622,3623,3624,3625,3627,3628,3629,3630,3633,3634,3635,3637,3640,3641,3644,3647,3650,3653,3656,3657,3658,3661,3664,3667,3670,3673,3674,3675,3676,3678,3679,3681,3682,3683,3684,3686,3687,3688,3690,3691,3693,3694,3695,3696,3697,3700,3701,3702,3704,3707] : List Nat)[i - 2495]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1533 = true :=
  Artifact.isValidJumpDest_index 1138 (by rfl)

theorem jumpDest1555 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1555 = true :=
  Artifact.isValidJumpDest_index 1148 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  Artifact.isValidJumpDest_index 1155 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1586 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1615 = true :=
  Artifact.isValidJumpDest_index 1178 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1631 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1668 = true :=
  Artifact.isValidJumpDest_index 1216 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1693 = true :=
  Artifact.isValidJumpDest_index 1229 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1728 = true :=
  Artifact.isValidJumpDest_index 1250 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1736 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1755 = true :=
  Artifact.isValidJumpDest_index 1264 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1756 = true :=
  Artifact.isValidJumpDest_index 1265 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1769 = true :=
  Artifact.isValidJumpDest_index 1272 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1789 = true :=
  Artifact.isValidJumpDest_index 1287 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1806 = true :=
  Artifact.isValidJumpDest_index 1294 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1831 = true :=
  Artifact.isValidJumpDest_index 1307 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1832 = true :=
  Artifact.isValidJumpDest_index 1308 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1850 = true :=
  Artifact.isValidJumpDest_index 1320 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1876 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1886 = true :=
  Artifact.isValidJumpDest_index 1341 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1892 = true :=
  Artifact.isValidJumpDest_index 1345 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1900 = true :=
  Artifact.isValidJumpDest_index 1351 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1911 = true :=
  Artifact.isValidJumpDest_index 1360 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1915 = true :=
  Artifact.isValidJumpDest_index 1362 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1926 = true :=
  Artifact.isValidJumpDest_index 1369 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1939 = true :=
  Artifact.isValidJumpDest_index 1379 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1982 = true :=
  Artifact.isValidJumpDest_index 1413 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2003 = true :=
  Artifact.isValidJumpDest_index 1423 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2077 = true :=
  Artifact.isValidJumpDest_index 1477 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2480 = true :=
  Artifact.isValidJumpDest_index 1848 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2513 = true :=
  Artifact.isValidJumpDest_index 1875 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2655 = true :=
  Artifact.isValidJumpDest_index 1915 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2679 = true :=
  Artifact.isValidJumpDest_index 1931 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2876 = true :=
  Artifact.isValidJumpDest_index 1990 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2887 = true :=
  Artifact.isValidJumpDest_index 1997 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2890 = true :=
  Artifact.isValidJumpDest_index 1999 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2901 = true :=
  Artifact.isValidJumpDest_index 2006 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2914 = true :=
  Artifact.isValidJumpDest_index 2016 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2935 = true :=
  Artifact.isValidJumpDest_index 2029 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2957 = true :=
  Artifact.isValidJumpDest_index 2044 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2984 = true :=
  Artifact.isValidJumpDest_index 2064 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3008 = true :=
  Artifact.isValidJumpDest_index 2076 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3584 = true :=
  Artifact.isValidJumpDest_index 2472 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3619 = true :=
  Artifact.isValidJumpDest_index 2495 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3657 = true :=
  Artifact.isValidJumpDest_index 2517 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3674 = true :=
  Artifact.isValidJumpDest_index 2524 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
