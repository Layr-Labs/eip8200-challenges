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
    Artifact.submissionArtifact.instructionPC 976 = 1314 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1015 = 1371 := by
  calc
    Artifact.submissionArtifact.instructionPC 1015 =
        Artifact.submissionArtifact.instructionPC 976 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 976).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 976 39
    _ = 1371 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1055 = 1428 := by
  calc
    Artifact.submissionArtifact.instructionPC 1055 =
        Artifact.submissionArtifact.instructionPC 1015 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1015).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1015 40
    _ = 1428 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1091 = 1471 := by
  calc
    Artifact.submissionArtifact.instructionPC 1091 =
        Artifact.submissionArtifact.instructionPC 1055 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1055).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1055 36
    _ = 1471 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1131 = 1527 := by
  calc
    Artifact.submissionArtifact.instructionPC 1131 =
        Artifact.submissionArtifact.instructionPC 1091 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1091).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1091 40
    _ = 1527 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1171 = 1605 := by
  calc
    Artifact.submissionArtifact.instructionPC 1171 =
        Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1131).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1131 40
    _ = 1605 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1211 = 1660 := by
  calc
    Artifact.submissionArtifact.instructionPC 1211 =
        Artifact.submissionArtifact.instructionPC 1171 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1171).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1171 40
    _ = 1660 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1251 = 1729 := by
  calc
    Artifact.submissionArtifact.instructionPC 1251 =
        Artifact.submissionArtifact.instructionPC 1211 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1211).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1211 40
    _ = 1729 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1291 = 1800 := by
  calc
    Artifact.submissionArtifact.instructionPC 1291 =
        Artifact.submissionArtifact.instructionPC 1251 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1251).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1251 40
    _ = 1800 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1331 = 1871 := by
  calc
    Artifact.submissionArtifact.instructionPC 1331 =
        Artifact.submissionArtifact.instructionPC 1291 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1291).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1291 40
    _ = 1871 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1371 = 1928 := by
  calc
    Artifact.submissionArtifact.instructionPC 1371 =
        Artifact.submissionArtifact.instructionPC 1331 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1331).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1331 40
    _ = 1928 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1410 = 1979 := by
  calc
    Artifact.submissionArtifact.instructionPC 1410 =
        Artifact.submissionArtifact.instructionPC 1371 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1371).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1371 39
    _ = 1979 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1447 = 2016 := by
  calc
    Artifact.submissionArtifact.instructionPC 1447 =
        Artifact.submissionArtifact.instructionPC 1410 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1410).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1410 37
    _ = 2016 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1490 = 2075 := by
  calc
    Artifact.submissionArtifact.instructionPC 1490 =
        Artifact.submissionArtifact.instructionPC 1447 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1447).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1447 43
    _ = 2075 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1531 = 2122 := by
  calc
    Artifact.submissionArtifact.instructionPC 1531 =
        Artifact.submissionArtifact.instructionPC 1490 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1490).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1490 41
    _ = 2122 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1568 = 2168 := by
  calc
    Artifact.submissionArtifact.instructionPC 1568 =
        Artifact.submissionArtifact.instructionPC 1531 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1531).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1531 37
    _ = 2168 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1609 = 2224 := by
  calc
    Artifact.submissionArtifact.instructionPC 1609 =
        Artifact.submissionArtifact.instructionPC 1568 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1568).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1568 41
    _ = 2224 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1652 = 2272 := by
  calc
    Artifact.submissionArtifact.instructionPC 1652 =
        Artifact.submissionArtifact.instructionPC 1609 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1609).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1609 43
    _ = 2272 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1690 = 2324 := by
  calc
    Artifact.submissionArtifact.instructionPC 1690 =
        Artifact.submissionArtifact.instructionPC 1652 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1652).take 38)).length :=
      instructionPC_add Artifact.submissionArtifact 1652 38
    _ = 2324 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1729 = 2501 := by
  calc
    Artifact.submissionArtifact.instructionPC 1729 =
        Artifact.submissionArtifact.instructionPC 1690 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1690).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1690 39
    _ = 2501 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1734 = 2506 := by
  calc
    Artifact.submissionArtifact.instructionPC 1734 =
        Artifact.submissionArtifact.instructionPC 1729 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1729).take 5)).length :=
      instructionPC_add Artifact.submissionArtifact 1729 5
    _ = 2506 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1760 = 2543 := by
  calc
    Artifact.submissionArtifact.instructionPC 1760 =
        Artifact.submissionArtifact.instructionPC 1734 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1734).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 1734 26
    _ = 2543 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1773 = 2564 := by
  calc
    Artifact.submissionArtifact.instructionPC 1773 =
        Artifact.submissionArtifact.instructionPC 1760 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1760).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1760 13
    _ = 2564 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1808 = 2613 := by
  calc
    Artifact.submissionArtifact.instructionPC 1808 =
        Artifact.submissionArtifact.instructionPC 1773 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1773).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1773 35
    _ = 2613 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 976 ≤ i) (hii : i ≤ 1014) :
    Artifact.submissionArtifact.instructionPC i =
      [1314,1315,1317,1318,1319,1321,1322,1326,1327,1329,1330,1331,1332,1333,1336,1337,1338,1341,1342,1343,1344,1347,1348,1349,1352,1353,1354,1356,1357,1359,1360,1361,1363,1364,1365,1366,1367,1369,1370][i - 976]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (976 + (i - 976)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 976 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 976).take (i - 976))).length :=
      instructionPC_add Artifact.submissionArtifact 976 (i - 976)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1015 ≤ i) (hii : i ≤ 1054) :
    Artifact.submissionArtifact.instructionPC i =
      [1371,1372,1373,1375,1376,1377,1378,1379,1380,1381,1384,1385,1387,1388,1389,1390,1391,1392,1394,1395,1396,1399,1400,1401,1404,1405,1406,1409,1410,1411,1413,1414,1417,1418,1420,1421,1422,1423,1424,1427][i - 1015]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1015 + (i - 1015)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1015 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1015).take (i - 1015))).length :=
      instructionPC_add Artifact.submissionArtifact 1015 (i - 1015)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1055 ≤ i) (hii : i ≤ 1090) :
    Artifact.submissionArtifact.instructionPC i =
      [1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1454,1455,1456,1457,1458,1460,1461,1462,1463,1464,1465,1467,1468,1469,1470][i - 1055]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1055 + (i - 1055)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1055 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1055).take (i - 1055))).length :=
      instructionPC_add Artifact.submissionArtifact 1055 (i - 1055)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1091 ≤ i) (hii : i ≤ 1130) :
    Artifact.submissionArtifact.instructionPC i =
      [1471,1472,1474,1475,1476,1477,1478,1479,1481,1482,1483,1484,1485,1486,1488,1489,1490,1491,1492,1493,1495,1496,1497,1498,1499,1500,1502,1503,1504,1505,1506,1509,1510,1511,1512,1514,1517,1518,1521,1524][i - 1091]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1091 + (i - 1091)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1091 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1091).take (i - 1091))).length :=
      instructionPC_add Artifact.submissionArtifact 1091 (i - 1091)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1131 ≤ i) (hii : i ≤ 1170) :
    Artifact.submissionArtifact.instructionPC i =
      [1527,1528,1529,1532,1533,1536,1539,1540,1543,1546,1549,1550,1551,1554,1555,1558,1561,1562,1564,1565,1568,1571,1574,1577,1580,1581,1582,1583,1584,1585,1587,1588,1591,1592,1595,1596,1599,1600,1601,1603][i - 1131]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1131 + (i - 1131)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1131).take (i - 1131))).length :=
      instructionPC_add Artifact.submissionArtifact 1131 (i - 1131)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1171 ≤ i) (hii : i ≤ 1210) :
    Artifact.submissionArtifact.instructionPC i =
      [1605,1607,1608,1609,1610,1611,1614,1615,1616,1617,1618,1621,1622,1623,1624,1625,1626,1629,1630,1633,1634,1636,1638,1640,1642,1644,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659][i - 1171]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1171 + (i - 1171)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1171 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1171).take (i - 1171))).length :=
      instructionPC_add Artifact.submissionArtifact 1171 (i - 1171)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1211 ≤ i) (hii : i ≤ 1250) :
    Artifact.submissionArtifact.instructionPC i =
      [1660,1661,1662,1663,1664,1667,1668,1671,1674,1677,1680,1683,1684,1685,1686,1687,1688,1690,1691,1692,1693,1695,1696,1697,1698,1701,1702,1703,1706,1709,1712,1715,1718,1719,1720,1722,1723,1726,1727,1728][i - 1211]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1211 + (i - 1211)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1211 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1211).take (i - 1211))).length :=
      instructionPC_add Artifact.submissionArtifact 1211 (i - 1211)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1251 ≤ i) (hii : i ≤ 1290) :
    Artifact.submissionArtifact.instructionPC i =
      [1729,1730,1733,1736,1739,1742,1745,1746,1747,1748,1751,1752,1754,1756,1758,1760,1761,1762,1763,1764,1765,1768,1769,1772,1773,1774,1775,1776,1777,1778,1780,1781,1784,1787,1790,1793,1796,1797,1798,1799][i - 1251]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1251 + (i - 1251)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1251 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1251).take (i - 1251))).length :=
      instructionPC_add Artifact.submissionArtifact 1251 (i - 1251)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1291 ≤ i) (hii : i ≤ 1330) :
    Artifact.submissionArtifact.instructionPC i =
      [1800,1801,1802,1805,1806,1809,1812,1815,1818,1821,1822,1823,1824,1826,1827,1828,1831,1832,1833,1834,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1854,1857,1860,1863,1866,1867,1868,1869,1870][i - 1291]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1291 + (i - 1291)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1291 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1291).take (i - 1291))).length :=
      instructionPC_add Artifact.submissionArtifact 1291 (i - 1291)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1331 ≤ i) (hii : i ≤ 1370) :
    Artifact.submissionArtifact.instructionPC i =
      [1871,1874,1875,1876,1877,1878,1879,1882,1883,1884,1885,1886,1887,1890,1891,1892,1893,1894,1895,1896,1897,1898,1901,1902,1903,1906,1907,1910,1911,1912,1913,1916,1917,1918,1920,1921,1922,1923,1926,1927][i - 1331]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1331 + (i - 1331)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1331 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1331).take (i - 1331))).length :=
      instructionPC_add Artifact.submissionArtifact 1331 (i - 1331)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1371 ≤ i) (hii : i ≤ 1409) :
    Artifact.submissionArtifact.instructionPC i =
      [1928,1929,1930,1931,1934,1935,1936,1938,1939,1940,1943,1944,1945,1946,1947,1949,1950,1951,1953,1954,1955,1956,1957,1958,1959,1961,1962,1963,1964,1965,1966,1967,1968,1969,1972,1973,1974,1977,1978][i - 1371]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1371 + (i - 1371)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1371 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1371).take (i - 1371))).length :=
      instructionPC_add Artifact.submissionArtifact 1371 (i - 1371)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1410 ≤ i) (hii : i ≤ 1446) :
    Artifact.submissionArtifact.instructionPC i =
      [1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015][i - 1410]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1410 + (i - 1410)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1410 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1410).take (i - 1410))).length :=
      instructionPC_add Artifact.submissionArtifact 1410 (i - 1410)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1447 ≤ i) (hii : i ≤ 1489) :
    Artifact.submissionArtifact.instructionPC i =
      [2016,2017,2019,2020,2021,2022,2024,2025,2026,2027,2028,2029,2030,2033,2034,2035,2036,2037,2040,2041,2042,2043,2046,2047,2048,2051,2052,2055,2056,2057,2060,2061,2062,2063,2066,2067,2068,2069,2070,2071,2072,2073,2074][i - 1447]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1447 + (i - 1447)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1447 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1447).take (i - 1447))).length :=
      instructionPC_add Artifact.submissionArtifact 1447 (i - 1447)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1490 ≤ i) (hii : i ≤ 1530) :
    Artifact.submissionArtifact.instructionPC i =
      [2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2090,2091,2093,2094,2095,2098,2099,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121][i - 1490]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1490 + (i - 1490)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1490 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1490).take (i - 1490))).length :=
      instructionPC_add Artifact.submissionArtifact 1490 (i - 1490)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1531 ≤ i) (hii : i ≤ 1567) :
    Artifact.submissionArtifact.instructionPC i =
      [2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2137,2138,2140,2141,2142,2143,2144,2145,2147,2148,2149,2152,2153,2154,2157,2158,2159,2160,2161,2162,2163,2164,2165][i - 1531]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1531 + (i - 1531)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1531 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1531).take (i - 1531))).length :=
      instructionPC_add Artifact.submissionArtifact 1531 (i - 1531)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1568 ≤ i) (hii : i ≤ 1608) :
    Artifact.submissionArtifact.instructionPC i =
      [2168,2169,2170,2171,2174,2175,2176,2179,2180,2181,2184,2185,2187,2188,2189,2190,2191,2192,2195,2196,2197,2198,2199,2202,2203,2204,2207,2208,2209,2210,2211,2213,2214,2215,2216,2217,2218,2220,2221,2222,2223][i - 1568]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1568 + (i - 1568)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1568 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1568).take (i - 1568))).length :=
      instructionPC_add Artifact.submissionArtifact 1568 (i - 1568)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1609 ≤ i) (hii : i ≤ 1651) :
    Artifact.submissionArtifact.instructionPC i =
      [2224,2225,2226,2227,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2258,2259,2260,2261,2263,2264,2265,2266,2267,2269,2270,2271][i - 1609]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1609 + (i - 1609)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1609 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1609).take (i - 1609))).length :=
      instructionPC_add Artifact.submissionArtifact 1609 (i - 1609)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1652 ≤ i) (hii : i ≤ 1689) :
    Artifact.submissionArtifact.instructionPC i =
      [2272,2275,2276,2277,2280,2281,2282,2283,2284,2287,2288,2289,2292,2293,2296,2297,2298,2301,2302,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323][i - 1652]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1652 + (i - 1652)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1652 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1652).take (i - 1652))).length :=
      instructionPC_add Artifact.submissionArtifact 1652 (i - 1652)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1690 ≤ i) (hii : i ≤ 1728) :
    Artifact.submissionArtifact.instructionPC i =
      [2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2368,2369,2370,2403,2404,2405,2406,2439,2440,2441,2444,2445,2446,2449,2450,2451,2452,2453,2454,2457,2458,2459,2492,2493,2496,2497,2500][i - 1690]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1690 + (i - 1690)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1690 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1690).take (i - 1690))).length :=
      instructionPC_add Artifact.submissionArtifact 1690 (i - 1690)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1729 ≤ i) (hii : i ≤ 1733) :
    Artifact.submissionArtifact.instructionPC i =
      [2501,2502,2503,2504,2505][i - 1729]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1729 + (i - 1729)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1729 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1729).take (i - 1729))).length :=
      instructionPC_add Artifact.submissionArtifact 1729 (i - 1729)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1734 ≤ i) (hii : i ≤ 1759) :
    Artifact.submissionArtifact.instructionPC i =
      [2506,2507,2510,2511,2512,2513,2516,2517,2518,2520,2521,2524,2525,2526,2527,2530,2531,2532,2533,2534,2535,2536,2539,2540,2541,2542][i - 1734]!  := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1734 + (i - 1734)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1734 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1734).take (i - 1734))).length :=
      instructionPC_add Artifact.submissionArtifact 1734 (i - 1734)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1760 ≤ i) (hii : i ≤ 1772) :
    Artifact.submissionArtifact.instructionPC i =
      [2543,2544,2545,2546,2548,2549,2550,2553,2554,2556,2559,2560,2563][i - 1760]!  := by
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
      [2564,2565,2566,2569,2570,2571,2572,2573,2574,2575,2576,2579,2580,2582,2585,2586,2587,2588,2589,2591,2592,2593,2594,2596,2597,2598,2599,2601,2602,2603,2605,2606,2608,2609,2612][i - 1773]!  := by
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

@[simp] theorem fastPC23 (i : Nat) (hi : 1808 ≤ i) (hii : i ≤ 1822) :
    Artifact.submissionArtifact.instructionPC i =
      [2613,2614,2615,2618,2619,2622,2623,2626,2629,2630,2633,2636,2637,2638,2641][i - 1808]!  := by
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
    (hi : 2455 ≤ i) (hii : i ≤ 2507) :
    Artifact.submissionArtifact.instructionPC i =
      ([3358,3359,3360,3361,3362,3363,3364,3366,3367,3368,3369,3372,3373,3374,3376,3379,3380,3383,3386,3389,3392,3395,3396,3397,3400,3403,3406,3409,3412,3413,3414,3415,3417,3418,3420,3421,3422,3423,3425,3426,3427,3429,3430,3432,3433,3434,3435,3436,3439,3440,3441,3443,3446] : List Nat)[i - 2455]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 898 (by rfl)

theorem jumpDest1528 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1528 = true :=
  Artifact.isValidJumpDest_index 1132 (by rfl)

theorem jumpDest1550 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1550 = true :=
  Artifact.isValidJumpDest_index 1142 (by rfl)

theorem jumpDest1564 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1564 = true :=
  Artifact.isValidJumpDest_index 1149 (by rfl)

theorem jumpDest1581 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1581 = true :=
  Artifact.isValidJumpDest_index 1156 (by rfl)

theorem jumpDest1607 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1607 = true :=
  Artifact.isValidJumpDest_index 1172 (by rfl)

theorem jumpDest1622 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1622 = true :=
  Artifact.isValidJumpDest_index 1183 (by rfl)

theorem jumpDest1659 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1659 = true :=
  Artifact.isValidJumpDest_index 1210 (by rfl)

theorem jumpDest1684 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1684 = true :=
  Artifact.isValidJumpDest_index 1223 (by rfl)

theorem jumpDest1719 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1719 = true :=
  Artifact.isValidJumpDest_index 1244 (by rfl)

theorem jumpDest1727 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1727 = true :=
  Artifact.isValidJumpDest_index 1249 (by rfl)

theorem jumpDest1746 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1746 = true :=
  Artifact.isValidJumpDest_index 1258 (by rfl)

theorem jumpDest1747 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1747 = true :=
  Artifact.isValidJumpDest_index 1259 (by rfl)

theorem jumpDest1760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1760 = true :=
  Artifact.isValidJumpDest_index 1266 (by rfl)

theorem jumpDest1780 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1780 = true :=
  Artifact.isValidJumpDest_index 1281 (by rfl)

theorem jumpDest1797 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1797 = true :=
  Artifact.isValidJumpDest_index 1288 (by rfl)

theorem jumpDest1822 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1822 = true :=
  Artifact.isValidJumpDest_index 1301 (by rfl)

theorem jumpDest1823 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1823 = true :=
  Artifact.isValidJumpDest_index 1302 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1841 = true :=
  Artifact.isValidJumpDest_index 1314 (by rfl)

theorem jumpDest1867 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1867 = true :=
  Artifact.isValidJumpDest_index 1327 (by rfl)

theorem jumpDest1877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1877 = true :=
  Artifact.isValidJumpDest_index 1335 (by rfl)

theorem jumpDest1883 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1883 = true :=
  Artifact.isValidJumpDest_index 1339 (by rfl)

theorem jumpDest1891 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1891 = true :=
  Artifact.isValidJumpDest_index 1345 (by rfl)

theorem jumpDest1902 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1902 = true :=
  Artifact.isValidJumpDest_index 1354 (by rfl)

theorem jumpDest1906 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1906 = true :=
  Artifact.isValidJumpDest_index 1356 (by rfl)

theorem jumpDest1917 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1917 = true :=
  Artifact.isValidJumpDest_index 1363 (by rfl)

theorem jumpDest1930 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1930 = true :=
  Artifact.isValidJumpDest_index 1373 (by rfl)

theorem jumpDest1965 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1965 = true :=
  Artifact.isValidJumpDest_index 1400 (by rfl)

theorem jumpDest1979 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1979 = true :=
  Artifact.isValidJumpDest_index 1410 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2103 = true :=
  Artifact.isValidJumpDest_index 1512 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2203 = true :=
  Artifact.isValidJumpDest_index 1592 (by rfl)

theorem jumpDest2481 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2236 = true :=
  Artifact.isValidJumpDest_index 1619 (by rfl)

theorem jumpDest2622 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2288 = true :=
  Artifact.isValidJumpDest_index 1662 (by rfl)

theorem jumpDest2646 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2312 = true :=
  Artifact.isValidJumpDest_index 1678 (by rfl)

theorem jumpDest2841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2506 = true :=
  Artifact.isValidJumpDest_index 1734 (by rfl)

theorem jumpDest2852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2517 = true :=
  Artifact.isValidJumpDest_index 1741 (by rfl)

theorem jumpDest2855 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2520 = true :=
  Artifact.isValidJumpDest_index 1743 (by rfl)

theorem jumpDest2866 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2531 = true :=
  Artifact.isValidJumpDest_index 1750 (by rfl)

theorem jumpDest2879 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2543 = true :=
  Artifact.isValidJumpDest_index 1760 (by rfl)

theorem jumpDest2900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2564 = true :=
  Artifact.isValidJumpDest_index 1773 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2586 = true :=
  Artifact.isValidJumpDest_index 1788 (by rfl)

theorem jumpDest2949 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2613 = true :=
  Artifact.isValidJumpDest_index 1808 (by rfl)

theorem jumpDest2973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2637 = true :=
  Artifact.isValidJumpDest_index 1820 (by rfl)

theorem jumpDest3535 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3323 = true :=
  Artifact.isValidJumpDest_index 2432 (by rfl)

theorem jumpDest3569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3358 = true :=
  Artifact.isValidJumpDest_index 2455 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3396 = true :=
  Artifact.isValidJumpDest_index 2477 (by rfl)

theorem jumpDest3625 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3413 = true :=
  Artifact.isValidJumpDest_index 2484 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
