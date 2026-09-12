import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The tables and jump facts below describe the selected round06 layout.
Each table uses a proved prefix-sum anchor and a bounded local slice.
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

/-! Submission-local prefix-sum PC certificates. -/

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
    Artifact.submissionArtifact.instructionPC 932 = 1251 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 961 = 1290 := by
  calc
    Artifact.submissionArtifact.instructionPC 961 =
        Artifact.submissionArtifact.instructionPC 932 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 932).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 932 29
    _ = 1290 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 998 = 1342 := by
  calc
    Artifact.submissionArtifact.instructionPC 998 =
        Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 961 37
    _ = 1342 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1034 = 1385 := by
  calc
    Artifact.submissionArtifact.instructionPC 1034 =
        Artifact.submissionArtifact.instructionPC 998 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 998).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 998 36
    _ = 1385 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1069 = 1429 := by
  calc
    Artifact.submissionArtifact.instructionPC 1069 =
        Artifact.submissionArtifact.instructionPC 1034 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1034).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1034 35
    _ = 1429 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1099 = 1486 := by
  calc
    Artifact.submissionArtifact.instructionPC 1099 =
        Artifact.submissionArtifact.instructionPC 1069 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1069).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1069 30
    _ = 1486 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1119 = 1514 := by
  calc
    Artifact.submissionArtifact.instructionPC 1119 =
        Artifact.submissionArtifact.instructionPC 1099 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1099).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1099 20
    _ = 1514 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1158 = 1582 := by
  calc
    Artifact.submissionArtifact.instructionPC 1158 =
        Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1119 39
    _ = 1582 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1186 = 1634 := by
  calc
    Artifact.submissionArtifact.instructionPC 1186 =
        Artifact.submissionArtifact.instructionPC 1158 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1158).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1158 28
    _ = 1634 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1226 = 1705 := by
  calc
    Artifact.submissionArtifact.instructionPC 1226 =
        Artifact.submissionArtifact.instructionPC 1186 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1186).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1186 40
    _ = 1705 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1260 = 1754 := by
  calc
    Artifact.submissionArtifact.instructionPC 1260 =
        Artifact.submissionArtifact.instructionPC 1226 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1226).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1226 34
    _ = 1754 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1299 = 1805 := by
  calc
    Artifact.submissionArtifact.instructionPC 1299 =
        Artifact.submissionArtifact.instructionPC 1260 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1260).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1260 39
    _ = 1805 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1336 = 1842 := by
  calc
    Artifact.submissionArtifact.instructionPC 1336 =
        Artifact.submissionArtifact.instructionPC 1299 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1299).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1299 37
    _ = 1842 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1379 = 1901 := by
  calc
    Artifact.submissionArtifact.instructionPC 1379 =
        Artifact.submissionArtifact.instructionPC 1336 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1336).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1336 43
    _ = 1901 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1420 = 1948 := by
  calc
    Artifact.submissionArtifact.instructionPC 1420 =
        Artifact.submissionArtifact.instructionPC 1379 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1379).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1379 41
    _ = 1948 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1456 = 1993 := by
  calc
    Artifact.submissionArtifact.instructionPC 1456 =
        Artifact.submissionArtifact.instructionPC 1420 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1420).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1420 36
    _ = 1993 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1497 = 2049 := by
  calc
    Artifact.submissionArtifact.instructionPC 1497 =
        Artifact.submissionArtifact.instructionPC 1456 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1456).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1456 41
    _ = 2049 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1538 = 2095 := by
  calc
    Artifact.submissionArtifact.instructionPC 1538 =
        Artifact.submissionArtifact.instructionPC 1497 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1497).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1497 41
    _ = 2095 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1562 = 2127 := by
  calc
    Artifact.submissionArtifact.instructionPC 1562 =
        Artifact.submissionArtifact.instructionPC 1538 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1538).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1538 24
    _ = 2127 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1605 = 2185 := by
  calc
    Artifact.submissionArtifact.instructionPC 1605 =
        Artifact.submissionArtifact.instructionPC 1562 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1562).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1562 43
    _ = 2185 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1608 = 2188 := by
  calc
    Artifact.submissionArtifact.instructionPC 1608 =
        Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1605 3
    _ = 2188 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1625 = 2211 := by
  calc
    Artifact.submissionArtifact.instructionPC 1625 =
        Artifact.submissionArtifact.instructionPC 1608 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1608).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1608 17
    _ = 2211 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1638 = 2232 := by
  calc
    Artifact.submissionArtifact.instructionPC 1638 =
        Artifact.submissionArtifact.instructionPC 1625 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1625).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1625 13
    _ = 2232 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1673 = 2281 := by
  calc
    Artifact.submissionArtifact.instructionPC 1673 =
        Artifact.submissionArtifact.instructionPC 1638 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1638).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1638 35
    _ = 2281 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2296 = 2995 := by
  calc
    Artifact.submissionArtifact.instructionPC 2296 =
        Artifact.submissionArtifact.instructionPC 1673 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1673).take 623)).length :=
      instructionPC_add Artifact.submissionArtifact 1673 623
    _ = 2995 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 932 ≤ i) (hii : i ≤ 960) :
    Artifact.submissionArtifact.instructionPC i =
      [1251,1252,1254,1255,1256,1258,1259,1260,1262,1263,1266,1267,1269,1270,1271,1272,1273,1275,1276,1278,1279,1280,1282,1283,1284,1285,1286,1288,1289][i - 932]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (932 + (i - 932)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 932 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 932).take (i - 932))).length :=
      instructionPC_add Artifact.submissionArtifact 932 (i - 932)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 961 ≤ i) (hii : i ≤ 997) :
    Artifact.submissionArtifact.instructionPC i =
      [1290,1291,1292,1294,1295,1296,1297,1298,1299,1300,1303,1304,1306,1307,1308,1309,1310,1311,1313,1314,1315,1318,1319,1320,1323,1324,1325,1326,1328,1329,1332,1333,1335,1336,1337,1338,1341][i - 961]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (961 + (i - 961)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take (i - 961))).length :=
      instructionPC_add Artifact.submissionArtifact 961 (i - 961)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 998 ≤ i) (hii : i ≤ 1033) :
    Artifact.submissionArtifact.instructionPC i =
      [1342,1343,1346,1347,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1368,1369,1370,1371,1372,1374,1375,1376,1377,1378,1379,1381,1382,1383,1384][i - 998]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (998 + (i - 998)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 998 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 998).take (i - 998))).length :=
      instructionPC_add Artifact.submissionArtifact 998 (i - 998)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1034 ≤ i) (hii : i ≤ 1068) :
    Artifact.submissionArtifact.instructionPC i =
      [1385,1386,1388,1389,1390,1391,1392,1393,1395,1396,1397,1398,1399,1400,1402,1403,1404,1405,1406,1407,1409,1410,1411,1412,1413,1414,1416,1417,1418,1419,1420,1423,1424,1425,1426][i - 1034]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1034 + (i - 1034)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1034 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1034).take (i - 1034))).length :=
      instructionPC_add Artifact.submissionArtifact 1034 (i - 1034)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1069 ≤ i) (hii : i ≤ 1098) :
    Artifact.submissionArtifact.instructionPC i =
      [1429,1430,1431,1434,1435,1438,1441,1442,1445,1448,1451,1452,1453,1456,1459,1460,1463,1466,1467,1468,1469,1470,1471,1473,1474,1477,1478,1481,1482,1485][i - 1069]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1069 + (i - 1069)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1069 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1069).take (i - 1069))).length :=
      instructionPC_add Artifact.submissionArtifact 1069 (i - 1069)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1099 ≤ i) (hii : i ≤ 1118) :
    Artifact.submissionArtifact.instructionPC i =
      [1486,1487,1488,1489,1490,1493,1494,1495,1496,1497,1500,1501,1502,1503,1504,1505,1508,1509,1512,1513][i - 1099]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1099 + (i - 1099)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1099 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1099).take (i - 1099))).length :=
      instructionPC_add Artifact.submissionArtifact 1099 (i - 1099)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1119 ≤ i) (hii : i ≤ 1157) :
    Artifact.submissionArtifact.instructionPC i =
      [1514,1515,1516,1517,1520,1521,1524,1527,1530,1533,1536,1537,1538,1539,1540,1541,1543,1544,1545,1546,1548,1549,1550,1551,1554,1555,1556,1559,1562,1565,1568,1571,1572,1573,1575,1576,1579,1580,1581][i - 1119]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1119 + (i - 1119)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take (i - 1119))).length :=
      instructionPC_add Artifact.submissionArtifact 1119 (i - 1119)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1158 ≤ i) (hii : i ≤ 1185) :
    Artifact.submissionArtifact.instructionPC i =
      [1582,1583,1586,1589,1592,1595,1598,1599,1600,1603,1604,1605,1606,1607,1608,1611,1612,1615,1616,1617,1620,1623,1624,1627,1630,1631,1632,1633][i - 1158]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1158 + (i - 1158)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1158 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1158).take (i - 1158))).length :=
      instructionPC_add Artifact.submissionArtifact 1158 (i - 1158)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1186 ≤ i) (hii : i ≤ 1225) :
    Artifact.submissionArtifact.instructionPC i =
      [1634,1635,1636,1639,1640,1643,1646,1649,1652,1655,1656,1657,1658,1660,1661,1662,1665,1666,1667,1668,1670,1671,1674,1675,1676,1677,1679,1680,1683,1684,1685,1688,1691,1694,1697,1700,1701,1702,1703,1704][i - 1186]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1186 + (i - 1186)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1186 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1186).take (i - 1186))).length :=
      instructionPC_add Artifact.submissionArtifact 1186 (i - 1186)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1226 ≤ i) (hii : i ≤ 1259) :
    Artifact.submissionArtifact.instructionPC i =
      [1705,1708,1709,1710,1711,1712,1713,1716,1717,1718,1719,1720,1721,1722,1723,1724,1727,1728,1729,1732,1733,1736,1737,1738,1739,1742,1743,1744,1746,1747,1748,1749,1752,1753][i - 1226]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1226 + (i - 1226)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1226 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1226).take (i - 1226))).length :=
      instructionPC_add Artifact.submissionArtifact 1226 (i - 1226)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1260 ≤ i) (hii : i ≤ 1298) :
    Artifact.submissionArtifact.instructionPC i =
      [1754,1755,1756,1757,1760,1761,1762,1764,1765,1766,1769,1770,1771,1772,1773,1775,1776,1777,1779,1780,1781,1782,1783,1784,1785,1787,1788,1789,1790,1791,1792,1793,1794,1795,1798,1799,1800,1803,1804][i - 1260]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1260 + (i - 1260)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1260 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1260).take (i - 1260))).length :=
      instructionPC_add Artifact.submissionArtifact 1260 (i - 1260)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1299 ≤ i) (hii : i ≤ 1335) :
    Artifact.submissionArtifact.instructionPC i =
      [1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841][i - 1299]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1299 + (i - 1299)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1299 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1299).take (i - 1299))).length :=
      instructionPC_add Artifact.submissionArtifact 1299 (i - 1299)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1336 ≤ i) (hii : i ≤ 1378) :
    Artifact.submissionArtifact.instructionPC i =
      [1842,1843,1845,1846,1847,1848,1850,1851,1852,1853,1854,1855,1856,1859,1860,1861,1862,1863,1866,1867,1868,1869,1872,1873,1874,1877,1878,1881,1882,1883,1886,1887,1888,1889,1892,1893,1894,1895,1896,1897,1898,1899,1900][i - 1336]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1336 + (i - 1336)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1336 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1336).take (i - 1336))).length :=
      instructionPC_add Artifact.submissionArtifact 1336 (i - 1336)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1379 ≤ i) (hii : i ≤ 1419) :
    Artifact.submissionArtifact.instructionPC i =
      [1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1916,1917,1919,1920,1921,1924,1925,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947][i - 1379]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1379 + (i - 1379)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1379 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1379).take (i - 1379))).length :=
      instructionPC_add Artifact.submissionArtifact 1379 (i - 1379)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1420 ≤ i) (hii : i ≤ 1455) :
    Artifact.submissionArtifact.instructionPC i =
      [1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1963,1964,1966,1967,1968,1969,1970,1971,1973,1974,1975,1978,1979,1980,1983,1984,1985,1986,1987,1988,1989,1990][i - 1420]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1420 + (i - 1420)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1420 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1420).take (i - 1420))).length :=
      instructionPC_add Artifact.submissionArtifact 1420 (i - 1420)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1456 ≤ i) (hii : i ≤ 1496) :
    Artifact.submissionArtifact.instructionPC i =
      [1993,1994,1995,1996,1999,2000,2001,2004,2005,2006,2009,2010,2012,2013,2014,2015,2016,2017,2020,2021,2022,2023,2024,2027,2028,2029,2032,2033,2034,2035,2036,2038,2039,2040,2041,2042,2043,2045,2046,2047,2048][i - 1456]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1456 + (i - 1456)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1456 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1456).take (i - 1456))).length :=
      instructionPC_add Artifact.submissionArtifact 1456 (i - 1456)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1497 ≤ i) (hii : i ≤ 1537) :
    Artifact.submissionArtifact.instructionPC i =
      [2049,2050,2051,2052,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2081,2082,2083,2084,2086,2087,2088,2089,2090,2092,2093,2094][i - 1497]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1497 + (i - 1497)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1497 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1497).take (i - 1497))).length :=
      instructionPC_add Artifact.submissionArtifact 1497 (i - 1497)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1538 ≤ i) (hii : i ≤ 1561) :
    Artifact.submissionArtifact.instructionPC i =
      [2095,2098,2099,2100,2103,2104,2105,2106,2107,2110,2111,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126][i - 1538]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1538 + (i - 1538)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1538 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1538).take (i - 1538))).length :=
      instructionPC_add Artifact.submissionArtifact 1538 (i - 1538)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1562 ≤ i) (hii : i ≤ 1604) :
    Artifact.submissionArtifact.instructionPC i =
      [2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2140,2141,2142,2143,2145,2146,2147,2148,2149,2151,2152,2153,2154,2157,2158,2159,2162,2163,2164,2165,2166,2167,2170,2171,2172,2175,2176,2177,2180,2181,2184][i - 1562]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1562 + (i - 1562)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1562 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1562).take (i - 1562))).length :=
      instructionPC_add Artifact.submissionArtifact 1562 (i - 1562)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1605 ≤ i) (hii : i ≤ 1607) :
    Artifact.submissionArtifact.instructionPC i =
      [2185,2186,2187][i - 1605]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1605 + (i - 1605)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take (i - 1605))).length :=
      instructionPC_add Artifact.submissionArtifact 1605 (i - 1605)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1608 ≤ i) (hii : i ≤ 1624) :
    Artifact.submissionArtifact.instructionPC i =
      [2188,2189,2192,2193,2194,2195,2198,2199,2200,2201,2202,2203,2204,2207,2208,2209,2210][i - 1608]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1608 + (i - 1608)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1608 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1608).take (i - 1608))).length :=
      instructionPC_add Artifact.submissionArtifact 1608 (i - 1608)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1625 ≤ i) (hii : i ≤ 1637) :
    Artifact.submissionArtifact.instructionPC i =
      [2211,2212,2213,2214,2216,2217,2218,2221,2222,2224,2227,2228,2231][i - 1625]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1625 + (i - 1625)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1625 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1625).take (i - 1625))).length :=
      instructionPC_add Artifact.submissionArtifact 1625 (i - 1625)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1638 ≤ i) (hii : i ≤ 1672) :
    Artifact.submissionArtifact.instructionPC i =
      [2232,2233,2234,2237,2238,2239,2240,2241,2242,2243,2244,2247,2248,2250,2253,2254,2255,2256,2257,2259,2260,2261,2262,2264,2265,2266,2267,2269,2270,2271,2273,2274,2276,2277,2280][i - 1638]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1638 + (i - 1638)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1638 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1638).take (i - 1638))).length :=
      instructionPC_add Artifact.submissionArtifact 1638 (i - 1638)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1673 ≤ i) (hii : i ≤ 1684) :
    Artifact.submissionArtifact.instructionPC i =
      [2281,2282,2283,2286,2287,2290,2291,2294,2297,2298,2301,2304][i - 1673]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1673 + (i - 1673)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1673 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1673).take (i - 1673))).length :=
      instructionPC_add Artifact.submissionArtifact 1673 (i - 1673)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2296 ≤ i) (hii : i ≤ 2341) :
    Artifact.submissionArtifact.instructionPC i =
      [2995,2996,2997,2998,2999,3000,3001,3003,3004,3005,3006,3009,3010,3011,3013,3016,3017,3020,3023,3026,3029,3032,3033,3034,3035,3037,3038,3040,3041,3042,3043,3045,3046,3047,3049,3050,3052,3053,3054,3055,3056,3059,3060,3061,3063,3066][i - 2296]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2296 + (i - 2296)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2296 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2296).take (i - 2296))).length :=
      instructionPC_add Artifact.submissionArtifact 2296 (i - 2296)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 888 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1430 = true :=
  Artifact.isValidJumpDest_index 1070 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1452 = true :=
  Artifact.isValidJumpDest_index 1080 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  Artifact.isValidJumpDest_index 1087 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1486 = true :=
  Artifact.isValidJumpDest_index 1099 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1501 = true :=
  Artifact.isValidJumpDest_index 1110 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1513 = true :=
  Artifact.isValidJumpDest_index 1118 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1537 = true :=
  Artifact.isValidJumpDest_index 1130 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1572 = true :=
  Artifact.isValidJumpDest_index 1151 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1580 = true :=
  Artifact.isValidJumpDest_index 1156 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1165 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3261 = true :=
  Artifact.isValidJumpDest_index 2498 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1604 = true :=
  Artifact.isValidJumpDest_index 1168 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1616 = true :=
  Artifact.isValidJumpDest_index 1176 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1631 = true :=
  Artifact.isValidJumpDest_index 1183 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1656 = true :=
  Artifact.isValidJumpDest_index 1196 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1657 = true :=
  Artifact.isValidJumpDest_index 1197 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1675 = true :=
  Artifact.isValidJumpDest_index 1209 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1701 = true :=
  Artifact.isValidJumpDest_index 1222 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1711 = true :=
  Artifact.isValidJumpDest_index 1230 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1717 = true :=
  Artifact.isValidJumpDest_index 1234 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1728 = true :=
  Artifact.isValidJumpDest_index 1243 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1732 = true :=
  Artifact.isValidJumpDest_index 1245 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1743 = true :=
  Artifact.isValidJumpDest_index 1252 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1756 = true :=
  Artifact.isValidJumpDest_index 1262 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1791 = true :=
  Artifact.isValidJumpDest_index 1289 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1805 = true :=
  Artifact.isValidJumpDest_index 1299 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1929 = true :=
  Artifact.isValidJumpDest_index 1401 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2028 = true :=
  Artifact.isValidJumpDest_index 1480 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2059 = true :=
  Artifact.isValidJumpDest_index 1505 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2115 = true :=
  Artifact.isValidJumpDest_index 1550 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2188 = true :=
  Artifact.isValidJumpDest_index 1608 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2199 = true :=
  Artifact.isValidJumpDest_index 1615 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2211 = true :=
  Artifact.isValidJumpDest_index 1625 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2232 = true :=
  Artifact.isValidJumpDest_index 1638 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2254 = true :=
  Artifact.isValidJumpDest_index 1653 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2281 = true :=
  Artifact.isValidJumpDest_index 1673 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2960 = true :=
  Artifact.isValidJumpDest_index 2273 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2995 = true :=
  Artifact.isValidJumpDest_index 2296 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3033 = true :=
  Artifact.isValidJumpDest_index 2318 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4874 = true :=
  Artifact.isValidJumpDest_index 3752 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5037 = true :=
  Artifact.isValidJumpDest_index 3872 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5288 = true :=
  Artifact.isValidJumpDest_index 4053 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5277 = true :=
  Artifact.isValidJumpDest_index 4046 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
