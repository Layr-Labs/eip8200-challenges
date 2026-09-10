import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The appended Montgomery path occupies instruction indices 977..1741
(pc 1314..2500).  This module fixes the `Located` constructors, the
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
    Artifact.submissionArtifact.instructionPC 971 = 1275 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1010 = 1331 := by
  calc
    Artifact.submissionArtifact.instructionPC 1010 =
        Artifact.submissionArtifact.instructionPC 971 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 971).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 971 39
    _ = 1331 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1050 = 1388 := by
  calc
    Artifact.submissionArtifact.instructionPC 1050 =
        Artifact.submissionArtifact.instructionPC 1010 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1010).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1010 40
    _ = 1388 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1082 = 1427 := by
  calc
    Artifact.submissionArtifact.instructionPC 1082 =
        Artifact.submissionArtifact.instructionPC 1050 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1050).take 32)).length :=
      instructionPC_add Artifact.submissionArtifact 1050 32
    _ = 1427 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1122 = 1483 := by
  calc
    Artifact.submissionArtifact.instructionPC 1122 =
        Artifact.submissionArtifact.instructionPC 1082 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1082).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1082 40
    _ = 1483 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1161 = 1558 := by
  calc
    Artifact.submissionArtifact.instructionPC 1161 =
        Artifact.submissionArtifact.instructionPC 1122 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1122).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1122 39
    _ = 1558 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1201 = 1606 := by
  calc
    Artifact.submissionArtifact.instructionPC 1201 =
        Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1161 40
    _ = 1606 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1240 = 1674 := by
  calc
    Artifact.submissionArtifact.instructionPC 1240 =
        Artifact.submissionArtifact.instructionPC 1201 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1201).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1201 39
    _ = 1674 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1279 = 1740 := by
  calc
    Artifact.submissionArtifact.instructionPC 1279 =
        Artifact.submissionArtifact.instructionPC 1240 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1240).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1240 39
    _ = 1740 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1319 = 1811 := by
  calc
    Artifact.submissionArtifact.instructionPC 1319 =
        Artifact.submissionArtifact.instructionPC 1279 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1279).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1279 40
    _ = 1811 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1359 = 1868 := by
  calc
    Artifact.submissionArtifact.instructionPC 1359 =
        Artifact.submissionArtifact.instructionPC 1319 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1319).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1319 40
    _ = 1868 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1398 = 1919 := by
  calc
    Artifact.submissionArtifact.instructionPC 1398 =
        Artifact.submissionArtifact.instructionPC 1359 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1359).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1359 39
    _ = 1919 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1435 = 1956 := by
  calc
    Artifact.submissionArtifact.instructionPC 1435 =
        Artifact.submissionArtifact.instructionPC 1398 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1398).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1398 37
    _ = 1956 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1478 = 2015 := by
  calc
    Artifact.submissionArtifact.instructionPC 1478 =
        Artifact.submissionArtifact.instructionPC 1435 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1435).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1435 43
    _ = 2015 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1519 = 2062 := by
  calc
    Artifact.submissionArtifact.instructionPC 1519 =
        Artifact.submissionArtifact.instructionPC 1478 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1478).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1478 41
    _ = 2062 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1555 = 2107 := by
  calc
    Artifact.submissionArtifact.instructionPC 1555 =
        Artifact.submissionArtifact.instructionPC 1519 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1519).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1519 36
    _ = 2107 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1596 = 2163 := by
  calc
    Artifact.submissionArtifact.instructionPC 1596 =
        Artifact.submissionArtifact.instructionPC 1555 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1555).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1555 41
    _ = 2163 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1637 = 2209 := by
  calc
    Artifact.submissionArtifact.instructionPC 1637 =
        Artifact.submissionArtifact.instructionPC 1596 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1596).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1596 41
    _ = 2209 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1677 = 2292 := by
  calc
    Artifact.submissionArtifact.instructionPC 1677 =
        Artifact.submissionArtifact.instructionPC 1637 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1637).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1637 40
    _ = 2292 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1717 = 2494 := by
  calc
    Artifact.submissionArtifact.instructionPC 1717 =
        Artifact.submissionArtifact.instructionPC 1677 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1677).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1677 40
    _ = 2494 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1735 = 2552 := by
  calc
    Artifact.submissionArtifact.instructionPC 1735 =
        Artifact.submissionArtifact.instructionPC 1717 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1717).take 18)).length :=
      instructionPC_add Artifact.submissionArtifact 1717 18
    _ = 2552 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1760 = 2588 := by
  calc
    Artifact.submissionArtifact.instructionPC 1760 =
        Artifact.submissionArtifact.instructionPC 1735 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1735).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 1735 25
    _ = 2588 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1773 = 2609 := by
  calc
    Artifact.submissionArtifact.instructionPC 1773 =
        Artifact.submissionArtifact.instructionPC 1760 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1760).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1760 13
    _ = 2609 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1808 = 2658 := by
  calc
    Artifact.submissionArtifact.instructionPC 1808 =
        Artifact.submissionArtifact.instructionPC 1773 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1773).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1773 35
    _ = 2658 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 971 ≤ i) (hii : i ≤ 1009) :
    Artifact.submissionArtifact.instructionPC i =
      [1275,1276,1278,1279,1280,1282,1283,1286,1287,1289,1290,1291,1292,1293,1296,1297,1298,1301,1302,1303,1304,1307,1308,1309,1312,1313,1314,1316,1317,1319,1320,1321,1323,1324,1325,1326,1327,1329,1330][i - 971]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (971 + (i - 971)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 971 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 971).take (i - 971))).length :=
      instructionPC_add Artifact.submissionArtifact 971 (i - 971)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1010 ≤ i) (hii : i ≤ 1049) :
    Artifact.submissionArtifact.instructionPC i =
      [1331,1332,1333,1335,1336,1337,1338,1339,1340,1341,1344,1345,1347,1348,1349,1350,1351,1352,1354,1355,1356,1359,1360,1361,1364,1365,1366,1369,1370,1371,1373,1374,1377,1378,1379,1381,1382,1383,1384,1387][i - 1010]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1010 + (i - 1010)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1010 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1010).take (i - 1010))).length :=
      instructionPC_add Artifact.submissionArtifact 1010 (i - 1010)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1050 ≤ i) (hii : i ≤ 1081) :
    Artifact.submissionArtifact.instructionPC i =
      [1388,1389,1392,1393,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1414,1415,1417,1418,1419,1420,1421,1423,1424,1425,1426][i - 1050]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1050 + (i - 1050)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1050 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1050).take (i - 1050))).length :=
      instructionPC_add Artifact.submissionArtifact 1050 (i - 1050)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1082 ≤ i) (hii : i ≤ 1121) :
    Artifact.submissionArtifact.instructionPC i =
      [1427,1428,1430,1431,1432,1433,1434,1435,1437,1438,1439,1440,1441,1442,1444,1445,1446,1447,1448,1449,1451,1452,1453,1454,1455,1456,1458,1459,1460,1461,1462,1465,1466,1467,1468,1470,1473,1474,1477,1480][i - 1082]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1082 + (i - 1082)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1082 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1082).take (i - 1082))).length :=
      instructionPC_add Artifact.submissionArtifact 1082 (i - 1082)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1122 ≤ i) (hii : i ≤ 1160) :
    Artifact.submissionArtifact.instructionPC i =
      [1483,1484,1485,1488,1489,1492,1495,1496,1499,1502,1505,1506,1509,1510,1513,1516,1517,1519,1520,1523,1526,1529,1532,1535,1536,1537,1538,1539,1540,1542,1543,1546,1547,1550,1551,1554,1555,1556,1557][i - 1122]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1122 + (i - 1122)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1122 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1122).take (i - 1122))).length :=
      instructionPC_add Artifact.submissionArtifact 1122 (i - 1122)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1161 ≤ i) (hii : i ≤ 1200) :
    Artifact.submissionArtifact.instructionPC i =
      [1558,1559,1560,1561,1562,1563,1566,1567,1568,1569,1570,1573,1574,1575,1576,1577,1578,1581,1582,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605][i - 1161]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1161 + (i - 1161)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take (i - 1161))).length :=
      instructionPC_add Artifact.submissionArtifact 1161 (i - 1161)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1201 ≤ i) (hii : i ≤ 1239) :
    Artifact.submissionArtifact.instructionPC i =
      [1606,1607,1608,1609,1612,1613,1616,1619,1622,1625,1628,1629,1630,1631,1632,1633,1635,1636,1637,1638,1640,1641,1642,1643,1646,1647,1648,1651,1654,1657,1660,1663,1664,1665,1667,1668,1671,1672,1673][i - 1201]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1201 + (i - 1201)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1201 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1201).take (i - 1201))).length :=
      instructionPC_add Artifact.submissionArtifact 1201 (i - 1201)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1240 ≤ i) (hii : i ≤ 1278) :
    Artifact.submissionArtifact.instructionPC i =
      [1674,1675,1678,1681,1684,1687,1690,1691,1692,1693,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1708,1709,1712,1713,1714,1715,1716,1717,1718,1720,1721,1724,1727,1730,1733,1736,1737,1738,1739][i - 1240]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1240 + (i - 1240)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1240 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1240).take (i - 1240))).length :=
      instructionPC_add Artifact.submissionArtifact 1240 (i - 1240)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1279 ≤ i) (hii : i ≤ 1318) :
    Artifact.submissionArtifact.instructionPC i =
      [1740,1741,1742,1745,1746,1749,1752,1755,1758,1761,1762,1763,1764,1766,1767,1768,1771,1772,1773,1774,1776,1777,1780,1781,1782,1783,1785,1786,1789,1790,1791,1794,1797,1800,1803,1806,1807,1808,1809,1810][i - 1279]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1279 + (i - 1279)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1279 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1279).take (i - 1279))).length :=
      instructionPC_add Artifact.submissionArtifact 1279 (i - 1279)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1319 ≤ i) (hii : i ≤ 1358) :
    Artifact.submissionArtifact.instructionPC i =
      [1811,1814,1815,1816,1817,1818,1819,1822,1823,1824,1825,1826,1827,1830,1831,1832,1833,1834,1835,1836,1837,1838,1841,1842,1843,1846,1847,1850,1851,1852,1853,1856,1857,1858,1860,1861,1862,1863,1866,1867][i - 1319]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1319 + (i - 1319)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1319 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1319).take (i - 1319))).length :=
      instructionPC_add Artifact.submissionArtifact 1319 (i - 1319)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1359 ≤ i) (hii : i ≤ 1397) :
    Artifact.submissionArtifact.instructionPC i =
      [1868,1869,1870,1871,1874,1875,1876,1878,1879,1880,1883,1884,1885,1886,1887,1889,1890,1891,1893,1894,1895,1896,1897,1898,1899,1901,1902,1903,1904,1905,1906,1907,1908,1909,1912,1913,1914,1917,1918][i - 1359]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1359 + (i - 1359)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1359 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1359).take (i - 1359))).length :=
      instructionPC_add Artifact.submissionArtifact 1359 (i - 1359)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1398 ≤ i) (hii : i ≤ 1434) :
    Artifact.submissionArtifact.instructionPC i =
      [1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955][i - 1398]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1398 + (i - 1398)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1398 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1398).take (i - 1398))).length :=
      instructionPC_add Artifact.submissionArtifact 1398 (i - 1398)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1435 ≤ i) (hii : i ≤ 1477) :
    Artifact.submissionArtifact.instructionPC i =
      [1956,1957,1959,1960,1961,1962,1964,1965,1966,1967,1968,1969,1970,1973,1974,1975,1976,1977,1980,1981,1982,1983,1986,1987,1988,1991,1992,1995,1996,1997,2000,2001,2002,2003,2006,2007,2008,2009,2010,2011,2012,2013,2014][i - 1435]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1435 + (i - 1435)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1435 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1435).take (i - 1435))).length :=
      instructionPC_add Artifact.submissionArtifact 1435 (i - 1435)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1478 ≤ i) (hii : i ≤ 1518) :
    Artifact.submissionArtifact.instructionPC i =
      [2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2030,2031,2033,2034,2035,2038,2039,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061][i - 1478]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1478 + (i - 1478)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1478 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1478).take (i - 1478))).length :=
      instructionPC_add Artifact.submissionArtifact 1478 (i - 1478)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1519 ≤ i) (hii : i ≤ 1554) :
    Artifact.submissionArtifact.instructionPC i =
      [2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2077,2078,2080,2081,2082,2083,2084,2085,2087,2088,2089,2092,2093,2094,2097,2098,2099,2100,2101,2102,2103,2104][i - 1519]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1519 + (i - 1519)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1519 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1519).take (i - 1519))).length :=
      instructionPC_add Artifact.submissionArtifact 1519 (i - 1519)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1555 ≤ i) (hii : i ≤ 1595) :
    Artifact.submissionArtifact.instructionPC i =
      [2107,2108,2109,2110,2113,2114,2115,2118,2119,2120,2123,2124,2126,2127,2128,2129,2130,2131,2134,2135,2136,2137,2138,2141,2142,2143,2146,2147,2148,2149,2150,2152,2153,2154,2155,2156,2157,2159,2160,2161,2162][i - 1555]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1555 + (i - 1555)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1555 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1555).take (i - 1555))).length :=
      instructionPC_add Artifact.submissionArtifact 1555 (i - 1555)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1596 ≤ i) (hii : i ≤ 1636) :
    Artifact.submissionArtifact.instructionPC i =
      [2163,2164,2165,2166,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,2195,2196,2197,2198,2200,2201,2202,2203,2204,2206,2207,2208][i - 1596]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1596 + (i - 1596)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1596 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1596).take (i - 1596))).length :=
      instructionPC_add Artifact.submissionArtifact 1596 (i - 1596)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1637 ≤ i) (hii : i ≤ 1676) :
    Artifact.submissionArtifact.instructionPC i =
      [2209,2212,2213,2214,2217,2218,2219,2220,2221,2224,2225,2226,2229,2230,2231,2232,2233,2235,2236,2237,2240,2241,2242,2243,2244,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,2291][i - 1637]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1637 + (i - 1637)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1637 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1637).take (i - 1637))).length :=
      instructionPC_add Artifact.submissionArtifact 1637 (i - 1637)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1677 ≤ i) (hii : i ≤ 1716) :
    Artifact.submissionArtifact.instructionPC i =
      [2292,2293,2294,2295,2296,2329,2330,2331,2332,2365,2366,2367,2368,2369,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2417,2418,2419,2420,2421,2454,2455,2456,2457,2490,2491][i - 1677]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1677 + (i - 1677)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1677 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1677).take (i - 1677))).length :=
      instructionPC_add Artifact.submissionArtifact 1677 (i - 1677)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1717 ≤ i) (hii : i ≤ 1734) :
    Artifact.submissionArtifact.instructionPC i =
      [2494,2495,2496,2499,2500,2501,2502,2505,2506,2507,2540,2541,2544,2545,2548,2549,2550,2551][i - 1717]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1717 + (i - 1717)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1717 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1717).take (i - 1717))).length :=
      instructionPC_add Artifact.submissionArtifact 1717 (i - 1717)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1735 ≤ i) (hii : i ≤ 1759) :
    Artifact.submissionArtifact.instructionPC i =
      [2552,2555,2556,2557,2558,2561,2562,2563,2565,2566,2569,2570,2571,2572,2575,2576,2577,2578,2579,2580,2581,2584,2585,2586,2587][i - 1735]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1735 + (i - 1735)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1735 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1735).take (i - 1735))).length :=
      instructionPC_add Artifact.submissionArtifact 1735 (i - 1735)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1760 ≤ i) (hii : i ≤ 1772) :
    Artifact.submissionArtifact.instructionPC i =
      [2588,2589,2590,2591,2593,2594,2595,2598,2599,2601,2604,2605,2608][i - 1760]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1760 + (i - 1760)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1760 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1760).take (i - 1760))).length :=
      instructionPC_add Artifact.submissionArtifact 1760 (i - 1760)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1773 ≤ i) (hii : i ≤ 1807) :
    Artifact.submissionArtifact.instructionPC i =
      [2609,2610,2611,2614,2615,2616,2617,2618,2619,2620,2621,2624,2625,2627,2630,2631,2632,2633,2634,2636,2637,2638,2639,2641,2642,2643,2644,2646,2647,2648,2650,2651,2653,2654,2657][i - 1773]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1773 + (i - 1773)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1773 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1773).take (i - 1773))).length :=
      instructionPC_add Artifact.submissionArtifact 1773 (i - 1773)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1808 ≤ i) (hii : i ≤ 1821) :
    Artifact.submissionArtifact.instructionPC i =
      [2658,2659,2660,2663,2664,2667,2668,2671,2674,2675,2678,2681,2682,2685][i - 1808]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1808 + (i - 1808)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1808 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1808).take (i - 1808))).length :=
      instructionPC_add Artifact.submissionArtifact 1808 (i - 1808)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl


/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2454 ≤ i) (hii : i ≤ 2505) :
    Artifact.submissionArtifact.instructionPC i =
      ([3401,3402,3403,3404,3405,3406,3407,3409,3410,3411,3412,3415,3416,3417,3419,3422,3423,3426,3429,3432,3435,3438,3439,3442,3445,3448,3451,3454,3455,3456,3457,3459,3460,3462,3463,3464,3465,3467,3468,3469,3471,3472,3474,3475,3476,3477,3478,3481,3482,3483,3485,3488] : List Nat)[i - 2454]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1158 = true :=
  Artifact.isValidJumpDest_index 894 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1484 = true :=
  Artifact.isValidJumpDest_index 1123 (by rfl)


theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1519 = true :=
  Artifact.isValidJumpDest_index 1139 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1536 = true :=
  Artifact.isValidJumpDest_index 1146 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1559 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1574 = true :=
  Artifact.isValidJumpDest_index 1173 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1605 = true :=
  Artifact.isValidJumpDest_index 1200 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1629 = true :=
  Artifact.isValidJumpDest_index 1212 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1664 = true :=
  Artifact.isValidJumpDest_index 1233 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1672 = true :=
  Artifact.isValidJumpDest_index 1238 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1691 = true :=
  Artifact.isValidJumpDest_index 1247 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1692 = true :=
  Artifact.isValidJumpDest_index 1248 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1701 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1720 = true :=
  Artifact.isValidJumpDest_index 1269 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1276 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1762 = true :=
  Artifact.isValidJumpDest_index 1289 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1763 = true :=
  Artifact.isValidJumpDest_index 1290 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1781 = true :=
  Artifact.isValidJumpDest_index 1302 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1807 = true :=
  Artifact.isValidJumpDest_index 1315 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1817 = true :=
  Artifact.isValidJumpDest_index 1323 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1823 = true :=
  Artifact.isValidJumpDest_index 1327 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1831 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1842 = true :=
  Artifact.isValidJumpDest_index 1342 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1846 = true :=
  Artifact.isValidJumpDest_index 1344 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1857 = true :=
  Artifact.isValidJumpDest_index 1351 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1870 = true :=
  Artifact.isValidJumpDest_index 1361 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1905 = true :=
  Artifact.isValidJumpDest_index 1388 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1919 = true :=
  Artifact.isValidJumpDest_index 1398 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2043 = true :=
  Artifact.isValidJumpDest_index 1500 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2142 = true :=
  Artifact.isValidJumpDest_index 1579 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2173 = true :=
  Artifact.isValidJumpDest_index 1604 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2225 = true :=
  Artifact.isValidJumpDest_index 1647 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2241 = true :=
  Artifact.isValidJumpDest_index 1658 (by rfl)


theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2562 = true :=
  Artifact.isValidJumpDest_index 1741 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2565 = true :=
  Artifact.isValidJumpDest_index 1743 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2576 = true :=
  Artifact.isValidJumpDest_index 1750 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2588 = true :=
  Artifact.isValidJumpDest_index 1760 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2609 = true :=
  Artifact.isValidJumpDest_index 1773 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2631 = true :=
  Artifact.isValidJumpDest_index 1788 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2658 = true :=
  Artifact.isValidJumpDest_index 1808 (by rfl)


theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3366 = true :=
  Artifact.isValidJumpDest_index 2431 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3401 = true :=
  Artifact.isValidJumpDest_index 2454 (by rfl)


theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3455 = true :=
  Artifact.isValidJumpDest_index 2482 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
