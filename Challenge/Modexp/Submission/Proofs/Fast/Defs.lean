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
    Artifact.submissionArtifact.instructionPC 977 = 1314 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1017 = 1371 := by
  calc
    Artifact.submissionArtifact.instructionPC 1017 =
        Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 977 40
    _ = 1371 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1057 = 1428 := by
  calc
    Artifact.submissionArtifact.instructionPC 1057 =
        Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1017).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1017 40
    _ = 1428 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1093 = 1471 := by
  calc
    Artifact.submissionArtifact.instructionPC 1093 =
        Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1057).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1057 36
    _ = 1471 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1133 = 1527 := by
  calc
    Artifact.submissionArtifact.instructionPC 1133 =
        Artifact.submissionArtifact.instructionPC 1093 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1093).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1093 40
    _ = 1527 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1173 = 1605 := by
  calc
    Artifact.submissionArtifact.instructionPC 1173 =
        Artifact.submissionArtifact.instructionPC 1133 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1133).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1133 40
    _ = 1605 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1213 = 1660 := by
  calc
    Artifact.submissionArtifact.instructionPC 1213 =
        Artifact.submissionArtifact.instructionPC 1173 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1173).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1173 40
    _ = 1660 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1253 = 1729 := by
  calc
    Artifact.submissionArtifact.instructionPC 1253 =
        Artifact.submissionArtifact.instructionPC 1213 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1213).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1213 40
    _ = 1729 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1293 = 1800 := by
  calc
    Artifact.submissionArtifact.instructionPC 1293 =
        Artifact.submissionArtifact.instructionPC 1253 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1253).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1253 40
    _ = 1800 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1333 = 1871 := by
  calc
    Artifact.submissionArtifact.instructionPC 1333 =
        Artifact.submissionArtifact.instructionPC 1293 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1293).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1293 40
    _ = 1871 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1373 = 1928 := by
  calc
    Artifact.submissionArtifact.instructionPC 1373 =
        Artifact.submissionArtifact.instructionPC 1333 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1333).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1333 40
    _ = 1928 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1412 = 1979 := by
  calc
    Artifact.submissionArtifact.instructionPC 1412 =
        Artifact.submissionArtifact.instructionPC 1373 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1373).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1373 39
    _ = 1979 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1449 = 2016 := by
  calc
    Artifact.submissionArtifact.instructionPC 1449 =
        Artifact.submissionArtifact.instructionPC 1412 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1412).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1412 37
    _ = 2016 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1492 = 2075 := by
  calc
    Artifact.submissionArtifact.instructionPC 1492 =
        Artifact.submissionArtifact.instructionPC 1449 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1449).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1449 43
    _ = 2075 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1533 = 2122 := by
  calc
    Artifact.submissionArtifact.instructionPC 1533 =
        Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1492).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1492 41
    _ = 2122 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1570 = 2168 := by
  calc
    Artifact.submissionArtifact.instructionPC 1570 =
        Artifact.submissionArtifact.instructionPC 1533 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1533).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1533 37
    _ = 2168 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1611 = 2224 := by
  calc
    Artifact.submissionArtifact.instructionPC 1611 =
        Artifact.submissionArtifact.instructionPC 1570 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1570).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1570 41
    _ = 2224 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1654 = 2272 := by
  calc
    Artifact.submissionArtifact.instructionPC 1654 =
        Artifact.submissionArtifact.instructionPC 1611 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1611).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1611 43
    _ = 2272 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1692 = 2324 := by
  calc
    Artifact.submissionArtifact.instructionPC 1692 =
        Artifact.submissionArtifact.instructionPC 1654 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1654).take 38)).length :=
      instructionPC_add Artifact.submissionArtifact 1654 38
    _ = 2324 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1732 = 2472 := by
  calc
    Artifact.submissionArtifact.instructionPC 1732 =
        Artifact.submissionArtifact.instructionPC 1692 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1692).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1692 40
    _ = 2472 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1737 = 2477 := by
  calc
    Artifact.submissionArtifact.instructionPC 1737 =
        Artifact.submissionArtifact.instructionPC 1732 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1732).take 5)).length :=
      instructionPC_add Artifact.submissionArtifact 1732 5
    _ = 2477 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1763 = 2514 := by
  calc
    Artifact.submissionArtifact.instructionPC 1763 =
        Artifact.submissionArtifact.instructionPC 1737 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1737).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 1737 26
    _ = 2514 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1776 = 2535 := by
  calc
    Artifact.submissionArtifact.instructionPC 1776 =
        Artifact.submissionArtifact.instructionPC 1763 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1763).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1763 13
    _ = 2535 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1811 = 2584 := by
  calc
    Artifact.submissionArtifact.instructionPC 1811 =
        Artifact.submissionArtifact.instructionPC 1776 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1776).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1776 35
    _ = 2584 := by
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
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take (i - 977))).length :=
      instructionPC_add Artifact.submissionArtifact 977 (i - 977)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1017 ≤ i) (hii : i ≤ 1056) :
    Artifact.submissionArtifact.instructionPC i =
      [1371,1372,1373,1375,1376,1377,1378,1379,1380,1381,1384,1385,1387,1388,1389,1390,1391,1392,1394,1395,1396,1399,1400,1401,1404,1405,1406,1409,1410,1411,1413,1414,1417,1418,1420,1421,1422,1423,1424,1427][i - 1017]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1017 + (i - 1017)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1017).take (i - 1017))).length :=
      instructionPC_add Artifact.submissionArtifact 1017 (i - 1017)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1092) :
    Artifact.submissionArtifact.instructionPC i =
      [1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1454,1455,1456,1457,1458,1460,1461,1462,1463,1464,1465,1467,1468,1469,1470][i - 1057]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1057 + (i - 1057)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1057).take (i - 1057))).length :=
      instructionPC_add Artifact.submissionArtifact 1057 (i - 1057)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1093 ≤ i) (hii : i ≤ 1132) :
    Artifact.submissionArtifact.instructionPC i =
      [1471,1472,1474,1475,1476,1477,1478,1479,1481,1482,1483,1484,1485,1486,1488,1489,1490,1491,1492,1493,1495,1496,1497,1498,1499,1500,1502,1503,1504,1505,1506,1509,1510,1511,1512,1514,1517,1518,1521,1524][i - 1093]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1093 + (i - 1093)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1093 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1093).take (i - 1093))).length :=
      instructionPC_add Artifact.submissionArtifact 1093 (i - 1093)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1133 ≤ i) (hii : i ≤ 1172) :
    Artifact.submissionArtifact.instructionPC i =
      [1527,1528,1529,1532,1533,1536,1539,1540,1543,1546,1549,1550,1551,1554,1555,1558,1561,1562,1564,1565,1568,1571,1574,1577,1580,1581,1582,1583,1584,1585,1587,1588,1591,1592,1595,1596,1599,1600,1601,1603][i - 1133]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1133 + (i - 1133)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1133 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1133).take (i - 1133))).length :=
      instructionPC_add Artifact.submissionArtifact 1133 (i - 1133)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1173 ≤ i) (hii : i ≤ 1212) :
    Artifact.submissionArtifact.instructionPC i =
      [1605,1607,1608,1609,1610,1611,1614,1615,1616,1617,1618,1621,1622,1623,1624,1625,1626,1629,1630,1633,1634,1636,1638,1640,1642,1644,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659][i - 1173]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1173 + (i - 1173)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1173 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1173).take (i - 1173))).length :=
      instructionPC_add Artifact.submissionArtifact 1173 (i - 1173)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1213 ≤ i) (hii : i ≤ 1252) :
    Artifact.submissionArtifact.instructionPC i =
      [1660,1661,1662,1663,1664,1667,1668,1671,1674,1677,1680,1683,1684,1685,1686,1687,1688,1690,1691,1692,1693,1695,1696,1697,1698,1701,1702,1703,1706,1709,1712,1715,1718,1719,1720,1722,1723,1726,1727,1728][i - 1213]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1213 + (i - 1213)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1213 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1213).take (i - 1213))).length :=
      instructionPC_add Artifact.submissionArtifact 1213 (i - 1213)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1253 ≤ i) (hii : i ≤ 1292) :
    Artifact.submissionArtifact.instructionPC i =
      [1729,1730,1733,1736,1739,1742,1745,1746,1747,1748,1751,1752,1754,1756,1758,1760,1761,1762,1763,1764,1765,1768,1769,1772,1773,1774,1775,1776,1777,1778,1780,1781,1784,1787,1790,1793,1796,1797,1798,1799][i - 1253]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1253 + (i - 1253)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1253 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1253).take (i - 1253))).length :=
      instructionPC_add Artifact.submissionArtifact 1253 (i - 1253)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1293 ≤ i) (hii : i ≤ 1332) :
    Artifact.submissionArtifact.instructionPC i =
      [1800,1801,1802,1805,1806,1809,1812,1815,1818,1821,1822,1823,1824,1826,1827,1828,1831,1832,1833,1834,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1854,1857,1860,1863,1866,1867,1868,1869,1870][i - 1293]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1293 + (i - 1293)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1293 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1293).take (i - 1293))).length :=
      instructionPC_add Artifact.submissionArtifact 1293 (i - 1293)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1333 ≤ i) (hii : i ≤ 1372) :
    Artifact.submissionArtifact.instructionPC i =
      [1871,1874,1875,1876,1877,1878,1879,1882,1883,1884,1885,1886,1887,1890,1891,1892,1893,1894,1895,1896,1897,1898,1901,1902,1903,1906,1907,1910,1911,1912,1913,1916,1917,1918,1920,1921,1922,1923,1926,1927][i - 1333]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1333 + (i - 1333)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1333 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1333).take (i - 1333))).length :=
      instructionPC_add Artifact.submissionArtifact 1333 (i - 1333)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1373 ≤ i) (hii : i ≤ 1411) :
    Artifact.submissionArtifact.instructionPC i =
      [1928,1929,1930,1931,1934,1935,1936,1938,1939,1940,1943,1944,1945,1946,1947,1949,1950,1951,1953,1954,1955,1956,1957,1958,1959,1961,1962,1963,1964,1965,1966,1967,1968,1969,1972,1973,1974,1977,1978][i - 1373]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1373 + (i - 1373)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1373 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1373).take (i - 1373))).length :=
      instructionPC_add Artifact.submissionArtifact 1373 (i - 1373)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1412 ≤ i) (hii : i ≤ 1448) :
    Artifact.submissionArtifact.instructionPC i =
      [1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015][i - 1412]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1412 + (i - 1412)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1412 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1412).take (i - 1412))).length :=
      instructionPC_add Artifact.submissionArtifact 1412 (i - 1412)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1449 ≤ i) (hii : i ≤ 1491) :
    Artifact.submissionArtifact.instructionPC i =
      [2016,2017,2019,2020,2021,2022,2024,2025,2026,2027,2028,2029,2030,2033,2034,2035,2036,2037,2040,2041,2042,2043,2046,2047,2048,2051,2052,2055,2056,2057,2060,2061,2062,2063,2066,2067,2068,2069,2070,2071,2072,2073,2074][i - 1449]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1449 + (i - 1449)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1449 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1449).take (i - 1449))).length :=
      instructionPC_add Artifact.submissionArtifact 1449 (i - 1449)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1492 ≤ i) (hii : i ≤ 1532) :
    Artifact.submissionArtifact.instructionPC i =
      [2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2090,2091,2093,2094,2095,2098,2099,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121][i - 1492]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1492 + (i - 1492)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1492).take (i - 1492))).length :=
      instructionPC_add Artifact.submissionArtifact 1492 (i - 1492)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1533 ≤ i) (hii : i ≤ 1569) :
    Artifact.submissionArtifact.instructionPC i =
      [2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2137,2138,2140,2141,2142,2143,2144,2145,2147,2148,2149,2152,2153,2154,2157,2158,2159,2160,2161,2162,2163,2164,2165][i - 1533]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1533 + (i - 1533)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1533 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1533).take (i - 1533))).length :=
      instructionPC_add Artifact.submissionArtifact 1533 (i - 1533)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1570 ≤ i) (hii : i ≤ 1610) :
    Artifact.submissionArtifact.instructionPC i =
      [2168,2169,2170,2171,2174,2175,2176,2179,2180,2181,2184,2185,2187,2188,2189,2190,2191,2192,2195,2196,2197,2198,2199,2202,2203,2204,2207,2208,2209,2210,2211,2213,2214,2215,2216,2217,2218,2220,2221,2222,2223][i - 1570]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1570 + (i - 1570)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1570 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1570).take (i - 1570))).length :=
      instructionPC_add Artifact.submissionArtifact 1570 (i - 1570)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1611 ≤ i) (hii : i ≤ 1653) :
    Artifact.submissionArtifact.instructionPC i =
      [2224,2225,2226,2227,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2258,2259,2260,2261,2263,2264,2265,2266,2267,2269,2270,2271][i - 1611]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1611 + (i - 1611)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1611 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1611).take (i - 1611))).length :=
      instructionPC_add Artifact.submissionArtifact 1611 (i - 1611)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1654 ≤ i) (hii : i ≤ 1691) :
    Artifact.submissionArtifact.instructionPC i =
      [2272,2275,2276,2277,2280,2281,2282,2283,2284,2287,2288,2289,2292,2293,2296,2297,2298,2301,2302,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323][i - 1654]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1654 + (i - 1654)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1654 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1654).take (i - 1654))).length :=
      instructionPC_add Artifact.submissionArtifact 1654 (i - 1654)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1692 ≤ i) (hii : i ≤ 1731) :
    Artifact.submissionArtifact.instructionPC i =
      [2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2368,2369,2370,2403,2404,2405,2406,2439,2440,2441,2444,2445,2446,2449,2450,2451,2452,2453,2454,2457,2458,2459,2462,2463,2464,2467,2468,2471][i - 1692]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1692 + (i - 1692)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1692 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1692).take (i - 1692))).length :=
      instructionPC_add Artifact.submissionArtifact 1692 (i - 1692)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1732 ≤ i) (hii : i ≤ 1736) :
    Artifact.submissionArtifact.instructionPC i =
      [2472,2473,2474,2475,2476][i - 1732]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1732 + (i - 1732)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1732 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1732).take (i - 1732))).length :=
      instructionPC_add Artifact.submissionArtifact 1732 (i - 1732)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1737 ≤ i) (hii : i ≤ 1762) :
    Artifact.submissionArtifact.instructionPC i =
      [2477,2478,2481,2482,2483,2484,2487,2488,2489,2491,2492,2495,2496,2497,2498,2501,2502,2503,2504,2505,2506,2507,2510,2511,2512,2513][i - 1737]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1737 + (i - 1737)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1737 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1737).take (i - 1737))).length :=
      instructionPC_add Artifact.submissionArtifact 1737 (i - 1737)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1763 ≤ i) (hii : i ≤ 1775) :
    Artifact.submissionArtifact.instructionPC i =
      [2514,2515,2516,2517,2519,2520,2521,2524,2525,2527,2530,2531,2534][i - 1763]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1763 + (i - 1763)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1763 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1763).take (i - 1763))).length :=
      instructionPC_add Artifact.submissionArtifact 1763 (i - 1763)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1776 ≤ i) (hii : i ≤ 1810) :
    Artifact.submissionArtifact.instructionPC i =
      [2535,2536,2537,2540,2541,2542,2543,2544,2545,2546,2547,2550,2551,2553,2556,2557,2558,2559,2560,2562,2563,2564,2565,2567,2568,2569,2570,2572,2573,2574,2576,2577,2579,2580,2583][i - 1776]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1776 + (i - 1776)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1776 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1776).take (i - 1776))).length :=
      instructionPC_add Artifact.submissionArtifact 1776 (i - 1776)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1811 ≤ i) (hii : i ≤ 1825) :
    Artifact.submissionArtifact.instructionPC i =
      [2584,2585,2586,2589,2590,2593,2594,2597,2600,2601,2604,2607,2608,2609,2612][i - 1811]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1811 + (i - 1811)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1811 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1811).take (i - 1811))).length :=
      instructionPC_add Artifact.submissionArtifact 1811 (i - 1811)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl


/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2458 ≤ i) (hii : i ≤ 2510) :
    Artifact.submissionArtifact.instructionPC i =
      ([3329,3330,3331,3332,3333,3334,3335,3337,3338,3339,3340,3343,3344,3345,3347,3350,3351,3354,3357,3360,3363,3366,3367,3368,3371,3374,3377,3380,3383,3384,3385,3386,3388,3389,3391,3392,3393,3394,3396,3397,3398,3400,3401,3403,3404,3405,3406,3407,3410,3411,3412,3414,3417] : List Nat)[i - 2458]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

theorem jumpDest1528 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1528 = true :=
  Artifact.isValidJumpDest_index 1134 (by rfl)

theorem jumpDest1550 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1550 = true :=
  Artifact.isValidJumpDest_index 1144 (by rfl)

theorem jumpDest1564 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1564 = true :=
  Artifact.isValidJumpDest_index 1151 (by rfl)

theorem jumpDest1581 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1581 = true :=
  Artifact.isValidJumpDest_index 1158 (by rfl)

theorem jumpDest1607 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1607 = true :=
  Artifact.isValidJumpDest_index 1174 (by rfl)

theorem jumpDest1622 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1622 = true :=
  Artifact.isValidJumpDest_index 1185 (by rfl)

theorem jumpDest1659 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1659 = true :=
  Artifact.isValidJumpDest_index 1212 (by rfl)

theorem jumpDest1684 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1684 = true :=
  Artifact.isValidJumpDest_index 1225 (by rfl)

theorem jumpDest1719 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1719 = true :=
  Artifact.isValidJumpDest_index 1246 (by rfl)

theorem jumpDest1727 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1727 = true :=
  Artifact.isValidJumpDest_index 1251 (by rfl)

theorem jumpDest1746 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1746 = true :=
  Artifact.isValidJumpDest_index 1260 (by rfl)

theorem jumpDest1747 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1747 = true :=
  Artifact.isValidJumpDest_index 1261 (by rfl)

theorem jumpDest1760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1760 = true :=
  Artifact.isValidJumpDest_index 1268 (by rfl)

theorem jumpDest1780 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1780 = true :=
  Artifact.isValidJumpDest_index 1283 (by rfl)

theorem jumpDest1797 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1797 = true :=
  Artifact.isValidJumpDest_index 1290 (by rfl)

theorem jumpDest1822 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1822 = true :=
  Artifact.isValidJumpDest_index 1303 (by rfl)

theorem jumpDest1823 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1823 = true :=
  Artifact.isValidJumpDest_index 1304 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1841 = true :=
  Artifact.isValidJumpDest_index 1316 (by rfl)

theorem jumpDest1867 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1867 = true :=
  Artifact.isValidJumpDest_index 1329 (by rfl)

theorem jumpDest1877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1877 = true :=
  Artifact.isValidJumpDest_index 1337 (by rfl)

theorem jumpDest1883 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1883 = true :=
  Artifact.isValidJumpDest_index 1341 (by rfl)

theorem jumpDest1891 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1891 = true :=
  Artifact.isValidJumpDest_index 1347 (by rfl)

theorem jumpDest1902 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1902 = true :=
  Artifact.isValidJumpDest_index 1356 (by rfl)

theorem jumpDest1906 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1906 = true :=
  Artifact.isValidJumpDest_index 1358 (by rfl)

theorem jumpDest1917 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1917 = true :=
  Artifact.isValidJumpDest_index 1365 (by rfl)

theorem jumpDest1930 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1930 = true :=
  Artifact.isValidJumpDest_index 1375 (by rfl)

theorem jumpDest1965 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1965 = true :=
  Artifact.isValidJumpDest_index 1402 (by rfl)

theorem jumpDest1979 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1979 = true :=
  Artifact.isValidJumpDest_index 1412 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2103 = true :=
  Artifact.isValidJumpDest_index 1514 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2203 = true :=
  Artifact.isValidJumpDest_index 1594 (by rfl)

theorem jumpDest2481 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2236 = true :=
  Artifact.isValidJumpDest_index 1621 (by rfl)

theorem jumpDest2622 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2288 = true :=
  Artifact.isValidJumpDest_index 1664 (by rfl)

theorem jumpDest2646 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2312 = true :=
  Artifact.isValidJumpDest_index 1680 (by rfl)

theorem jumpDest2841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2477 = true :=
  Artifact.isValidJumpDest_index 1737 (by rfl)

theorem jumpDest2852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2488 = true :=
  Artifact.isValidJumpDest_index 1744 (by rfl)

theorem jumpDest2855 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2491 = true :=
  Artifact.isValidJumpDest_index 1746 (by rfl)

theorem jumpDest2866 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2502 = true :=
  Artifact.isValidJumpDest_index 1753 (by rfl)

theorem jumpDest2879 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2514 = true :=
  Artifact.isValidJumpDest_index 1763 (by rfl)

theorem jumpDest2900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2535 = true :=
  Artifact.isValidJumpDest_index 1776 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2557 = true :=
  Artifact.isValidJumpDest_index 1791 (by rfl)

theorem jumpDest2949 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2584 = true :=
  Artifact.isValidJumpDest_index 1811 (by rfl)

theorem jumpDest2973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2608 = true :=
  Artifact.isValidJumpDest_index 1823 (by rfl)

theorem jumpDest3535 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3294 = true :=
  Artifact.isValidJumpDest_index 2435 (by rfl)

theorem jumpDest3569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3329 = true :=
  Artifact.isValidJumpDest_index 2458 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3367 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

theorem jumpDest3625 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3384 = true :=
  Artifact.isValidJumpDest_index 2487 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
