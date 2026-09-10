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
    Artifact.submissionArtifact.instructionPC 971 = 1308 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1010 = 1364 := by
  calc
    Artifact.submissionArtifact.instructionPC 1010 =
        Artifact.submissionArtifact.instructionPC 971 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 971).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 971 39
    _ = 1364 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1050 = 1421 := by
  calc
    Artifact.submissionArtifact.instructionPC 1050 =
        Artifact.submissionArtifact.instructionPC 1010 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1010).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1010 40
    _ = 1421 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1082 = 1460 := by
  calc
    Artifact.submissionArtifact.instructionPC 1082 =
        Artifact.submissionArtifact.instructionPC 1050 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1050).take 32)).length :=
      instructionPC_add Artifact.submissionArtifact 1050 32
    _ = 1460 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1122 = 1516 := by
  calc
    Artifact.submissionArtifact.instructionPC 1122 =
        Artifact.submissionArtifact.instructionPC 1082 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1082).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1082 40
    _ = 1516 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1161 = 1595 := by
  calc
    Artifact.submissionArtifact.instructionPC 1161 =
        Artifact.submissionArtifact.instructionPC 1122 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1122).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1122 39
    _ = 1595 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1201 = 1652 := by
  calc
    Artifact.submissionArtifact.instructionPC 1201 =
        Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1161 40
    _ = 1652 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1240 = 1720 := by
  calc
    Artifact.submissionArtifact.instructionPC 1240 =
        Artifact.submissionArtifact.instructionPC 1201 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1201).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1201 39
    _ = 1720 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1279 = 1790 := by
  calc
    Artifact.submissionArtifact.instructionPC 1279 =
        Artifact.submissionArtifact.instructionPC 1240 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1240).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1240 39
    _ = 1790 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1319 = 1861 := by
  calc
    Artifact.submissionArtifact.instructionPC 1319 =
        Artifact.submissionArtifact.instructionPC 1279 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1279).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1279 40
    _ = 1861 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1359 = 1918 := by
  calc
    Artifact.submissionArtifact.instructionPC 1359 =
        Artifact.submissionArtifact.instructionPC 1319 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1319).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1319 40
    _ = 1918 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1398 = 1976 := by
  calc
    Artifact.submissionArtifact.instructionPC 1398 =
        Artifact.submissionArtifact.instructionPC 1359 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1359).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1359 39
    _ = 1976 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1435 = 2013 := by
  calc
    Artifact.submissionArtifact.instructionPC 1435 =
        Artifact.submissionArtifact.instructionPC 1398 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1398).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1398 37
    _ = 2013 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1478 = 2072 := by
  calc
    Artifact.submissionArtifact.instructionPC 1478 =
        Artifact.submissionArtifact.instructionPC 1435 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1435).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1435 43
    _ = 2072 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1519 = 2119 := by
  calc
    Artifact.submissionArtifact.instructionPC 1519 =
        Artifact.submissionArtifact.instructionPC 1478 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1478).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1478 41
    _ = 2119 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1555 = 2164 := by
  calc
    Artifact.submissionArtifact.instructionPC 1555 =
        Artifact.submissionArtifact.instructionPC 1519 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1519).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1519 36
    _ = 2164 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1596 = 2220 := by
  calc
    Artifact.submissionArtifact.instructionPC 1596 =
        Artifact.submissionArtifact.instructionPC 1555 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1555).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1555 41
    _ = 2220 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1637 = 2266 := by
  calc
    Artifact.submissionArtifact.instructionPC 1637 =
        Artifact.submissionArtifact.instructionPC 1596 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1596).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1596 41
    _ = 2266 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1677 = 2400 := by
  calc
    Artifact.submissionArtifact.instructionPC 1677 =
        Artifact.submissionArtifact.instructionPC 1637 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1637).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1637 40
    _ = 2400 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1698 = 2465 := by
  calc
    Artifact.submissionArtifact.instructionPC 1698 =
        Artifact.submissionArtifact.instructionPC 1677 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1677).take 21)).length :=
      instructionPC_add Artifact.submissionArtifact 1677 21
    _ = 2465 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1701 = 2468 := by
  calc
    Artifact.submissionArtifact.instructionPC 1701 =
        Artifact.submissionArtifact.instructionPC 1698 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1698).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1698 3
    _ = 2468 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1726 = 2505 := by
  calc
    Artifact.submissionArtifact.instructionPC 1726 =
        Artifact.submissionArtifact.instructionPC 1701 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1701).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 1701 25
    _ = 2505 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1739 = 2526 := by
  calc
    Artifact.submissionArtifact.instructionPC 1739 =
        Artifact.submissionArtifact.instructionPC 1726 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1726).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1726 13
    _ = 2526 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1774 = 2575 := by
  calc
    Artifact.submissionArtifact.instructionPC 1774 =
        Artifact.submissionArtifact.instructionPC 1739 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1739).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1739 35
    _ = 2575 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 971 ≤ i) (hii : i ≤ 1009) :
    Artifact.submissionArtifact.instructionPC i =
      [1308,1309,1311,1312,1313,1315,1316,1319,1320,1322,1323,1324,1325,1326,1329,1330,1331,1334,1335,1336,1337,1340,1341,1342,1345,1346,1347,1349,1350,1352,1353,1354,1356,1357,1358,1359,1360,1362,1363][i - 971]! := by
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
      [1364,1365,1366,1368,1369,1370,1371,1372,1373,1374,1377,1378,1380,1381,1382,1383,1384,1385,1387,1388,1389,1392,1393,1394,1397,1398,1399,1402,1403,1404,1406,1407,1410,1411,1412,1414,1415,1416,1417,1420][i - 1010]! := by
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
      [1421,1422,1425,1426,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1447,1448,1450,1451,1452,1453,1454,1456,1457,1458,1459][i - 1050]! := by
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
      [1460,1461,1463,1464,1465,1466,1467,1468,1470,1471,1472,1473,1474,1475,1477,1478,1479,1480,1481,1482,1484,1485,1486,1487,1488,1489,1491,1492,1493,1494,1495,1498,1499,1500,1501,1503,1506,1507,1510,1513][i - 1082]! := by
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
      [1516,1517,1518,1521,1522,1525,1528,1529,1532,1535,1538,1539,1542,1543,1546,1549,1550,1552,1553,1556,1559,1562,1565,1568,1569,1570,1571,1572,1573,1575,1576,1579,1580,1583,1584,1587,1588,1589,1592][i - 1122]! := by
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
      [1595,1598,1599,1600,1601,1602,1605,1606,1607,1608,1609,1613,1614,1615,1616,1617,1618,1621,1622,1625,1626,1628,1630,1632,1634,1636,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651][i - 1161]! := by
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
      [1652,1653,1654,1655,1658,1659,1662,1665,1668,1671,1674,1675,1676,1677,1678,1679,1681,1682,1683,1684,1686,1687,1688,1689,1692,1693,1694,1697,1700,1703,1706,1709,1710,1711,1713,1714,1717,1718,1719][i - 1201]! := by
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
      [1720,1721,1724,1727,1730,1733,1736,1737,1738,1739,1742,1743,1745,1747,1749,1751,1752,1753,1754,1755,1758,1759,1762,1763,1764,1765,1766,1767,1768,1770,1771,1774,1777,1780,1783,1786,1787,1788,1789][i - 1240]! := by
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
      [1790,1791,1792,1795,1796,1799,1802,1805,1808,1811,1812,1813,1814,1816,1817,1818,1821,1822,1823,1824,1826,1827,1830,1831,1832,1833,1835,1836,1839,1840,1841,1844,1847,1850,1853,1856,1857,1858,1859,1860][i - 1279]! := by
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
      [1861,1864,1865,1866,1867,1868,1869,1872,1873,1874,1875,1876,1877,1880,1881,1882,1883,1884,1885,1886,1887,1888,1891,1892,1893,1896,1897,1900,1901,1902,1903,1906,1907,1908,1910,1911,1912,1913,1916,1917][i - 1319]! := by
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
      [1918,1919,1920,1921,1924,1925,1926,1928,1929,1930,1933,1934,1935,1936,1937,1939,1940,1941,1943,1944,1945,1946,1947,1948,1949,1951,1952,1953,1954,1955,1956,1957,1958,1959,1964,1965,1966,1974,1975][i - 1359]! := by
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
      [1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012][i - 1398]! := by
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
      [2013,2014,2016,2017,2018,2019,2021,2022,2023,2024,2025,2026,2027,2030,2031,2032,2033,2034,2037,2038,2039,2040,2043,2044,2045,2048,2049,2052,2053,2054,2057,2058,2059,2060,2063,2064,2065,2066,2067,2068,2069,2070,2071][i - 1435]! := by
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
      [2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2087,2088,2090,2091,2092,2095,2096,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118][i - 1478]! := by
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
      [2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2134,2135,2137,2138,2139,2140,2141,2142,2144,2145,2146,2149,2150,2151,2154,2155,2156,2157,2158,2159,2160,2161][i - 1519]! := by
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
      [2164,2165,2166,2167,2170,2171,2172,2175,2176,2177,2180,2181,2183,2184,2185,2186,2187,2188,2191,2192,2193,2194,2195,2198,2199,2200,2203,2204,2205,2206,2207,2209,2210,2211,2212,2213,2214,2216,2217,2218,2219][i - 1555]! := by
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
      [2220,2221,2222,2223,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2252,2253,2254,2255,2257,2258,2259,2260,2261,2263,2264,2265][i - 1596]! := by
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
      [2266,2269,2270,2271,2274,2275,2276,2277,2278,2281,2282,2283,2308,2309,2310,2311,2312,2313,2314,2347,2348,2349,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2399][i - 1637]! := by
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

@[simp] theorem fastPC18 (i : Nat) (hi : 1677 ≤ i) (hii : i ≤ 1697) :
    Artifact.submissionArtifact.instructionPC i =
      [2400,2401,2402,2435,2436,2439,2440,2441,2444,2445,2446,2447,2450,2451,2452,2455,2456,2457,2460,2461,2464][i - 1677]! := by
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

@[simp] theorem fastPC19 (i : Nat) (hi : 1698 ≤ i) (hii : i ≤ 1700) :
    Artifact.submissionArtifact.instructionPC i =
      [2465,2466,2467][i - 1698]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1698 + (i - 1698)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1698 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1698).take (i - 1698))).length :=
      instructionPC_add Artifact.submissionArtifact 1698 (i - 1698)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1701 ≤ i) (hii : i ≤ 1725) :
    Artifact.submissionArtifact.instructionPC i =
      [2468,2471,2472,2473,2474,2477,2478,2479,2481,2482,2485,2486,2487,2488,2491,2492,2493,2494,2495,2496,2497,2501,2502,2503,2504][i - 1701]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1701 + (i - 1701)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1701 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1701).take (i - 1701))).length :=
      instructionPC_add Artifact.submissionArtifact 1701 (i - 1701)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1726 ≤ i) (hii : i ≤ 1738) :
    Artifact.submissionArtifact.instructionPC i =
      [2505,2506,2507,2508,2510,2511,2512,2515,2516,2518,2521,2522,2525][i - 1726]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1726 + (i - 1726)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1726 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1726).take (i - 1726))).length :=
      instructionPC_add Artifact.submissionArtifact 1726 (i - 1726)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1739 ≤ i) (hii : i ≤ 1773) :
    Artifact.submissionArtifact.instructionPC i =
      [2526,2527,2528,2531,2532,2533,2534,2535,2536,2537,2538,2541,2542,2544,2547,2548,2549,2550,2551,2553,2554,2555,2556,2558,2559,2560,2561,2563,2564,2565,2567,2568,2570,2571,2574][i - 1739]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1739 + (i - 1739)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1739 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1739).take (i - 1739))).length :=
      instructionPC_add Artifact.submissionArtifact 1739 (i - 1739)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1774 ≤ i) (hii : i ≤ 1787) :
    Artifact.submissionArtifact.instructionPC i =
      [2575,2576,2577,2580,2581,2584,2585,2588,2591,2592,2595,2598,2599,2602][i - 1774]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1774 + (i - 1774)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1774 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1774).take (i - 1774))).length :=
      instructionPC_add Artifact.submissionArtifact 1774 (i - 1774)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl


/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2420 ≤ i) (hii : i ≤ 2471) :
    Artifact.submissionArtifact.instructionPC i =
      ([3333,3334,3335,3336,3337,3338,3339,3341,3342,3343,3344,3347,3348,3349,3351,3354,3355,3358,3361,3364,3367,3370,3371,3374,3377,3380,3383,3386,3387,3388,3389,3391,3392,3394,3395,3396,3397,3399,3400,3401,3403,3404,3406,3407,3408,3409,3410,3413,3414,3415,3417,3420] : List Nat)[i - 2420]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1191 = true :=
  Artifact.isValidJumpDest_index 894 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1517 = true :=
  Artifact.isValidJumpDest_index 1123 (by rfl)


theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1552 = true :=
  Artifact.isValidJumpDest_index 1139 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  Artifact.isValidJumpDest_index 1146 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1598 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1614 = true :=
  Artifact.isValidJumpDest_index 1173 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1651 = true :=
  Artifact.isValidJumpDest_index 1200 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1675 = true :=
  Artifact.isValidJumpDest_index 1212 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1710 = true :=
  Artifact.isValidJumpDest_index 1233 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1718 = true :=
  Artifact.isValidJumpDest_index 1238 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1247 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1738 = true :=
  Artifact.isValidJumpDest_index 1248 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1751 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1770 = true :=
  Artifact.isValidJumpDest_index 1269 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1787 = true :=
  Artifact.isValidJumpDest_index 1276 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1812 = true :=
  Artifact.isValidJumpDest_index 1289 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1813 = true :=
  Artifact.isValidJumpDest_index 1290 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1831 = true :=
  Artifact.isValidJumpDest_index 1302 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1857 = true :=
  Artifact.isValidJumpDest_index 1315 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1867 = true :=
  Artifact.isValidJumpDest_index 1323 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1873 = true :=
  Artifact.isValidJumpDest_index 1327 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1881 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1892 = true :=
  Artifact.isValidJumpDest_index 1342 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1896 = true :=
  Artifact.isValidJumpDest_index 1344 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1907 = true :=
  Artifact.isValidJumpDest_index 1351 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1920 = true :=
  Artifact.isValidJumpDest_index 1361 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1955 = true :=
  Artifact.isValidJumpDest_index 1388 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1976 = true :=
  Artifact.isValidJumpDest_index 1398 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2100 = true :=
  Artifact.isValidJumpDest_index 1500 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2199 = true :=
  Artifact.isValidJumpDest_index 1579 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2230 = true :=
  Artifact.isValidJumpDest_index 1604 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2282 = true :=
  Artifact.isValidJumpDest_index 1647 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2311 = true :=
  Artifact.isValidJumpDest_index 1652 (by rfl)


theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2478 = true :=
  Artifact.isValidJumpDest_index 1707 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2481 = true :=
  Artifact.isValidJumpDest_index 1709 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2492 = true :=
  Artifact.isValidJumpDest_index 1716 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2505 = true :=
  Artifact.isValidJumpDest_index 1726 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2526 = true :=
  Artifact.isValidJumpDest_index 1739 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2548 = true :=
  Artifact.isValidJumpDest_index 1754 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2575 = true :=
  Artifact.isValidJumpDest_index 1774 (by rfl)


theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3298 = true :=
  Artifact.isValidJumpDest_index 2397 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3333 = true :=
  Artifact.isValidJumpDest_index 2420 (by rfl)


theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3387 = true :=
  Artifact.isValidJumpDest_index 2448 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
