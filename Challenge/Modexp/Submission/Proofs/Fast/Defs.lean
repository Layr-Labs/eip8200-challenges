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
    Artifact.submissionArtifact.instructionPC 1033 = 1385 := by
  calc
    Artifact.submissionArtifact.instructionPC 1033 =
        Artifact.submissionArtifact.instructionPC 998 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 998).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 998 35
    _ = 1385 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1065 = 1429 := by
  calc
    Artifact.submissionArtifact.instructionPC 1065 =
        Artifact.submissionArtifact.instructionPC 1033 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1033).take 32)).length :=
      instructionPC_add Artifact.submissionArtifact 1033 32
    _ = 1429 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1095 = 1486 := by
  calc
    Artifact.submissionArtifact.instructionPC 1095 =
        Artifact.submissionArtifact.instructionPC 1065 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1065).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1065 30
    _ = 1486 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1115 = 1514 := by
  calc
    Artifact.submissionArtifact.instructionPC 1115 =
        Artifact.submissionArtifact.instructionPC 1095 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1095).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1095 20
    _ = 1514 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1154 = 1582 := by
  calc
    Artifact.submissionArtifact.instructionPC 1154 =
        Artifact.submissionArtifact.instructionPC 1115 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1115).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1115 39
    _ = 1582 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1179 = 1629 := by
  calc
    Artifact.submissionArtifact.instructionPC 1179 =
        Artifact.submissionArtifact.instructionPC 1154 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1154).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 1154 25
    _ = 1629 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1221 = 1702 := by
  calc
    Artifact.submissionArtifact.instructionPC 1221 =
        Artifact.submissionArtifact.instructionPC 1179 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1179).take 42)).length :=
      instructionPC_add Artifact.submissionArtifact 1179 42
    _ = 1702 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1255 = 1751 := by
  calc
    Artifact.submissionArtifact.instructionPC 1255 =
        Artifact.submissionArtifact.instructionPC 1221 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1221).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1221 34
    _ = 1751 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1294 = 1802 := by
  calc
    Artifact.submissionArtifact.instructionPC 1294 =
        Artifact.submissionArtifact.instructionPC 1255 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1255).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1255 39
    _ = 1802 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1331 = 1839 := by
  calc
    Artifact.submissionArtifact.instructionPC 1331 =
        Artifact.submissionArtifact.instructionPC 1294 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1294).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1294 37
    _ = 1839 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1374 = 1898 := by
  calc
    Artifact.submissionArtifact.instructionPC 1374 =
        Artifact.submissionArtifact.instructionPC 1331 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1331).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1331 43
    _ = 1898 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1415 = 1945 := by
  calc
    Artifact.submissionArtifact.instructionPC 1415 =
        Artifact.submissionArtifact.instructionPC 1374 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1374).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1374 41
    _ = 1945 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1451 = 1990 := by
  calc
    Artifact.submissionArtifact.instructionPC 1451 =
        Artifact.submissionArtifact.instructionPC 1415 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1415).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1415 36
    _ = 1990 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1492 = 2046 := by
  calc
    Artifact.submissionArtifact.instructionPC 1492 =
        Artifact.submissionArtifact.instructionPC 1451 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1451).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1451 41
    _ = 2046 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1533 = 2092 := by
  calc
    Artifact.submissionArtifact.instructionPC 1533 =
        Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1492).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1492 41
    _ = 2092 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1557 = 2124 := by
  calc
    Artifact.submissionArtifact.instructionPC 1557 =
        Artifact.submissionArtifact.instructionPC 1533 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1533).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1533 24
    _ = 2124 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1600 = 2182 := by
  calc
    Artifact.submissionArtifact.instructionPC 1600 =
        Artifact.submissionArtifact.instructionPC 1557 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1557).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1557 43
    _ = 2182 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1603 = 2185 := by
  calc
    Artifact.submissionArtifact.instructionPC 1603 =
        Artifact.submissionArtifact.instructionPC 1600 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1600).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1600 3
    _ = 2185 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1620 = 2208 := by
  calc
    Artifact.submissionArtifact.instructionPC 1620 =
        Artifact.submissionArtifact.instructionPC 1603 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1603).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1603 17
    _ = 2208 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1633 = 2229 := by
  calc
    Artifact.submissionArtifact.instructionPC 1633 =
        Artifact.submissionArtifact.instructionPC 1620 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1620).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1620 13
    _ = 2229 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1668 = 2278 := by
  calc
    Artifact.submissionArtifact.instructionPC 1668 =
        Artifact.submissionArtifact.instructionPC 1633 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1633).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1633 35
    _ = 2278 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2278 = 3007 := by
  calc
    Artifact.submissionArtifact.instructionPC 2278 =
        Artifact.submissionArtifact.instructionPC 1668 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1668).take 610)).length :=
      instructionPC_add Artifact.submissionArtifact 1668 610
    _ = 3007 := by
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

@[simp] theorem fastPC2 (i : Nat) (hi : 998 ≤ i) (hii : i ≤ 1032) :
    Artifact.submissionArtifact.instructionPC i =
      [1342,1343,1346,1347,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1368,1369,1371,1372,1373,1374,1375,1377,1378,1379,1380,1381,1382,1384][i - 998]! := by
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

@[simp] theorem fastPC3 (i : Nat) (hi : 1033 ≤ i) (hii : i ≤ 1064) :
    Artifact.submissionArtifact.instructionPC i =
      [1385,1386,1387,1388,1389,1391,1392,1393,1394,1395,1396,1398,1399,1400,1401,1402,1403,1405,1406,1407,1408,1409,1410,1412,1413,1414,1415,1416,1423,1424,1425,1426][i - 1033]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1033 + (i - 1033)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1033 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1033).take (i - 1033))).length :=
      instructionPC_add Artifact.submissionArtifact 1033 (i - 1033)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1065 ≤ i) (hii : i ≤ 1094) :
    Artifact.submissionArtifact.instructionPC i =
      [1429,1430,1431,1434,1435,1438,1441,1442,1445,1448,1451,1452,1453,1456,1459,1460,1463,1466,1467,1468,1469,1470,1471,1473,1474,1477,1478,1481,1482,1485][i - 1065]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1065 + (i - 1065)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1065 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1065).take (i - 1065))).length :=
      instructionPC_add Artifact.submissionArtifact 1065 (i - 1065)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1095 ≤ i) (hii : i ≤ 1114) :
    Artifact.submissionArtifact.instructionPC i =
      [1486,1487,1488,1489,1490,1493,1494,1495,1496,1497,1500,1501,1502,1503,1504,1505,1508,1509,1512,1513][i - 1095]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1095 + (i - 1095)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1095 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1095).take (i - 1095))).length :=
      instructionPC_add Artifact.submissionArtifact 1095 (i - 1095)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1115 ≤ i) (hii : i ≤ 1153) :
    Artifact.submissionArtifact.instructionPC i =
      [1514,1515,1516,1517,1520,1521,1524,1527,1530,1533,1536,1537,1538,1539,1540,1541,1543,1544,1545,1546,1548,1549,1550,1551,1554,1555,1556,1559,1562,1565,1568,1571,1572,1573,1575,1576,1579,1580,1581][i - 1115]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1115 + (i - 1115)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1115 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1115).take (i - 1115))).length :=
      instructionPC_add Artifact.submissionArtifact 1115 (i - 1115)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1154 ≤ i) (hii : i ≤ 1178) :
    Artifact.submissionArtifact.instructionPC i =
      [1582,1583,1586,1589,1592,1595,1598,1599,1600,1601,1602,1603,1606,1607,1610,1611,1612,1615,1618,1619,1622,1625,1626,1627,1628][i - 1154]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1154 + (i - 1154)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1154 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1154).take (i - 1154))).length :=
      instructionPC_add Artifact.submissionArtifact 1154 (i - 1154)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1179 ≤ i) (hii : i ≤ 1220) :
    Artifact.submissionArtifact.instructionPC i =
      [1629,1630,1631,1634,1635,1638,1641,1644,1647,1650,1651,1652,1653,1655,1656,1657,1660,1661,1662,1663,1665,1666,1669,1670,1671,1672,1674,1675,1678,1679,1680,1683,1686,1689,1692,1695,1696,1697,1698,1699,1700,1701][i - 1179]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1179 + (i - 1179)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1179 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1179).take (i - 1179))).length :=
      instructionPC_add Artifact.submissionArtifact 1179 (i - 1179)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1221 ≤ i) (hii : i ≤ 1254) :
    Artifact.submissionArtifact.instructionPC i =
      [1702,1705,1706,1707,1708,1709,1710,1713,1714,1715,1716,1717,1718,1719,1720,1721,1724,1725,1726,1729,1730,1733,1734,1735,1736,1739,1740,1741,1743,1744,1745,1746,1749,1750][i - 1221]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1221 + (i - 1221)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1221 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1221).take (i - 1221))).length :=
      instructionPC_add Artifact.submissionArtifact 1221 (i - 1221)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1255 ≤ i) (hii : i ≤ 1293) :
    Artifact.submissionArtifact.instructionPC i =
      [1751,1752,1753,1754,1757,1758,1759,1761,1762,1763,1766,1767,1768,1769,1770,1772,1773,1774,1776,1777,1778,1779,1780,1781,1782,1784,1785,1786,1787,1788,1789,1790,1791,1792,1795,1796,1797,1800,1801][i - 1255]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1255 + (i - 1255)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1255 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1255).take (i - 1255))).length :=
      instructionPC_add Artifact.submissionArtifact 1255 (i - 1255)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1294 ≤ i) (hii : i ≤ 1330) :
    Artifact.submissionArtifact.instructionPC i =
      [1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838][i - 1294]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1294 + (i - 1294)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1294 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1294).take (i - 1294))).length :=
      instructionPC_add Artifact.submissionArtifact 1294 (i - 1294)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1331 ≤ i) (hii : i ≤ 1373) :
    Artifact.submissionArtifact.instructionPC i =
      [1839,1840,1842,1843,1844,1845,1847,1848,1849,1850,1851,1852,1853,1856,1857,1858,1859,1860,1863,1864,1865,1866,1869,1870,1871,1874,1875,1878,1879,1880,1883,1884,1885,1886,1889,1890,1891,1892,1893,1894,1895,1896,1897][i - 1331]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1331 + (i - 1331)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1331 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1331).take (i - 1331))).length :=
      instructionPC_add Artifact.submissionArtifact 1331 (i - 1331)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1374 ≤ i) (hii : i ≤ 1414) :
    Artifact.submissionArtifact.instructionPC i =
      [1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1913,1914,1916,1917,1918,1921,1922,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944][i - 1374]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1374 + (i - 1374)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1374 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1374).take (i - 1374))).length :=
      instructionPC_add Artifact.submissionArtifact 1374 (i - 1374)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1415 ≤ i) (hii : i ≤ 1450) :
    Artifact.submissionArtifact.instructionPC i =
      [1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1960,1961,1963,1964,1965,1966,1967,1968,1970,1971,1972,1975,1976,1977,1980,1981,1982,1983,1984,1985,1986,1987][i - 1415]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1415 + (i - 1415)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1415 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1415).take (i - 1415))).length :=
      instructionPC_add Artifact.submissionArtifact 1415 (i - 1415)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1451 ≤ i) (hii : i ≤ 1491) :
    Artifact.submissionArtifact.instructionPC i =
      [1990,1991,1992,1993,1996,1997,1998,2001,2002,2003,2006,2007,2009,2010,2011,2012,2013,2014,2017,2018,2019,2020,2021,2024,2025,2026,2029,2030,2031,2032,2033,2035,2036,2037,2038,2039,2040,2042,2043,2044,2045][i - 1451]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1451 + (i - 1451)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1451 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1451).take (i - 1451))).length :=
      instructionPC_add Artifact.submissionArtifact 1451 (i - 1451)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1492 ≤ i) (hii : i ≤ 1532) :
    Artifact.submissionArtifact.instructionPC i =
      [2046,2047,2048,2049,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2078,2079,2080,2081,2083,2084,2085,2086,2087,2089,2090,2091][i - 1492]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1492 + (i - 1492)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1492).take (i - 1492))).length :=
      instructionPC_add Artifact.submissionArtifact 1492 (i - 1492)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1533 ≤ i) (hii : i ≤ 1556) :
    Artifact.submissionArtifact.instructionPC i =
      [2092,2095,2096,2097,2100,2101,2102,2103,2104,2107,2108,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123][i - 1533]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1533 + (i - 1533)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1533 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1533).take (i - 1533))).length :=
      instructionPC_add Artifact.submissionArtifact 1533 (i - 1533)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1557 ≤ i) (hii : i ≤ 1599) :
    Artifact.submissionArtifact.instructionPC i =
      [2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2137,2138,2139,2140,2142,2143,2144,2145,2146,2148,2149,2150,2151,2154,2155,2156,2159,2160,2161,2162,2163,2164,2167,2168,2169,2172,2173,2174,2177,2178,2181][i - 1557]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1557 + (i - 1557)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1557 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1557).take (i - 1557))).length :=
      instructionPC_add Artifact.submissionArtifact 1557 (i - 1557)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1600 ≤ i) (hii : i ≤ 1602) :
    Artifact.submissionArtifact.instructionPC i =
      [2182,2183,2184][i - 1600]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1600 + (i - 1600)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1600 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1600).take (i - 1600))).length :=
      instructionPC_add Artifact.submissionArtifact 1600 (i - 1600)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1603 ≤ i) (hii : i ≤ 1619) :
    Artifact.submissionArtifact.instructionPC i =
      [2185,2186,2189,2190,2191,2192,2195,2196,2197,2198,2199,2200,2201,2204,2205,2206,2207][i - 1603]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1603 + (i - 1603)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1603 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1603).take (i - 1603))).length :=
      instructionPC_add Artifact.submissionArtifact 1603 (i - 1603)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1620 ≤ i) (hii : i ≤ 1632) :
    Artifact.submissionArtifact.instructionPC i =
      [2208,2209,2210,2211,2213,2214,2215,2218,2219,2221,2224,2225,2228][i - 1620]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1620 + (i - 1620)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1620 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1620).take (i - 1620))).length :=
      instructionPC_add Artifact.submissionArtifact 1620 (i - 1620)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1633 ≤ i) (hii : i ≤ 1667) :
    Artifact.submissionArtifact.instructionPC i =
      [2229,2230,2231,2234,2235,2236,2237,2238,2239,2240,2241,2244,2245,2247,2250,2251,2252,2253,2254,2256,2257,2258,2259,2261,2262,2263,2264,2266,2267,2268,2270,2271,2273,2274,2277][i - 1633]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1633 + (i - 1633)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1633 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1633).take (i - 1633))).length :=
      instructionPC_add Artifact.submissionArtifact 1633 (i - 1633)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1668 ≤ i) (hii : i ≤ 1679) :
    Artifact.submissionArtifact.instructionPC i =
      [2278,2279,2280,2283,2284,2287,2288,2291,2294,2295,2298,2301][i - 1668]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1668 + (i - 1668)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1668 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1668).take (i - 1668))).length :=
      instructionPC_add Artifact.submissionArtifact 1668 (i - 1668)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2278 ≤ i) (hii : i ≤ 2323) :
    Artifact.submissionArtifact.instructionPC i =
      [3007,3008,3009,3010,3011,3012,3013,3015,3016,3017,3018,3021,3022,3023,3025,3028,3029,3032,3035,3038,3041,3044,3045,3046,3047,3049,3050,3052,3053,3054,3055,3057,3058,3059,3061,3062,3064,3065,3066,3067,3068,3070,3071,3072,3074,3077][i - 2278]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2278 + (i - 2278)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2278 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2278).take (i - 2278))).length :=
      instructionPC_add Artifact.submissionArtifact 2278 (i - 2278)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 888 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1430 = true :=
  Artifact.isValidJumpDest_index 1066 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1452 = true :=
  Artifact.isValidJumpDest_index 1076 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1486 = true :=
  Artifact.isValidJumpDest_index 1095 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1501 = true :=
  Artifact.isValidJumpDest_index 1106 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1513 = true :=
  Artifact.isValidJumpDest_index 1114 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1537 = true :=
  Artifact.isValidJumpDest_index 1126 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1572 = true :=
  Artifact.isValidJumpDest_index 1147 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1580 = true :=
  Artifact.isValidJumpDest_index 1152 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1161 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3216 = true :=
  Artifact.isValidJumpDest_index 2433 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1161 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1611 = true :=
  Artifact.isValidJumpDest_index 1169 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1626 = true :=
  Artifact.isValidJumpDest_index 1176 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1651 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1652 = true :=
  Artifact.isValidJumpDest_index 1190 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1670 = true :=
  Artifact.isValidJumpDest_index 1202 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1698 = true :=
  Artifact.isValidJumpDest_index 1217 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1708 = true :=
  Artifact.isValidJumpDest_index 1225 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1714 = true :=
  Artifact.isValidJumpDest_index 1229 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1725 = true :=
  Artifact.isValidJumpDest_index 1238 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1729 = true :=
  Artifact.isValidJumpDest_index 1240 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1740 = true :=
  Artifact.isValidJumpDest_index 1247 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1753 = true :=
  Artifact.isValidJumpDest_index 1257 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1788 = true :=
  Artifact.isValidJumpDest_index 1284 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1802 = true :=
  Artifact.isValidJumpDest_index 1294 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1926 = true :=
  Artifact.isValidJumpDest_index 1396 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2025 = true :=
  Artifact.isValidJumpDest_index 1475 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2056 = true :=
  Artifact.isValidJumpDest_index 1500 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2112 = true :=
  Artifact.isValidJumpDest_index 1545 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2185 = true :=
  Artifact.isValidJumpDest_index 1603 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2196 = true :=
  Artifact.isValidJumpDest_index 1610 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2208 = true :=
  Artifact.isValidJumpDest_index 1620 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2229 = true :=
  Artifact.isValidJumpDest_index 1633 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2251 = true :=
  Artifact.isValidJumpDest_index 1648 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2278 = true :=
  Artifact.isValidJumpDest_index 1668 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2972 = true :=
  Artifact.isValidJumpDest_index 2255 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3007 = true :=
  Artifact.isValidJumpDest_index 2278 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3045 = true :=
  Artifact.isValidJumpDest_index 2300 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4877 = true :=
  Artifact.isValidJumpDest_index 3707 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5032 = true :=
  Artifact.isValidJumpDest_index 3819 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5279 = true :=
  Artifact.isValidJumpDest_index 3998 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5268 = true :=
  Artifact.isValidJumpDest_index 3991 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
