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
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 977 40
    _ = 1371 := by rw [fastPCAnchor0]; rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1057 = 1428 := by
  calc
    Artifact.submissionArtifact.instructionPC 1057 =
        Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1017).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1017 40
    _ = 1428 := by rw [fastPCAnchor1]; rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1097 = 1476 := by
  calc
    Artifact.submissionArtifact.instructionPC 1097 =
        Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1057).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1057 40
    _ = 1476 := by rw [fastPCAnchor2]; rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1137 = 1532 := by
  calc
    Artifact.submissionArtifact.instructionPC 1137 =
        Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1097).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1097 40
    _ = 1532 := by rw [fastPCAnchor3]; rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1177 = 1612 := by
  calc
    Artifact.submissionArtifact.instructionPC 1177 =
        Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1137).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1137 40
    _ = 1612 := by rw [fastPCAnchor4]; rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1217 = 1669 := by
  calc
    Artifact.submissionArtifact.instructionPC 1217 =
        Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1177).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1177 40
    _ = 1669 := by rw [fastPCAnchor5]; rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1257 = 1738 := by
  calc
    Artifact.submissionArtifact.instructionPC 1257 =
        Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1217).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1217 40
    _ = 1738 := by rw [fastPCAnchor6]; rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1297 = 1809 := by
  calc
    Artifact.submissionArtifact.instructionPC 1297 =
        Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1257).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1257 40
    _ = 1809 := by rw [fastPCAnchor7]; rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1337 = 1880 := by
  calc
    Artifact.submissionArtifact.instructionPC 1337 =
        Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1297).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1297 40
    _ = 1880 := by rw [fastPCAnchor8]; rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1377 = 1937 := by
  calc
    Artifact.submissionArtifact.instructionPC 1377 =
        Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1337).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1337 40
    _ = 1937 := by rw [fastPCAnchor9]; rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1416 = 1995 := by
  calc
    Artifact.submissionArtifact.instructionPC 1416 =
        Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1377).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1377 39
    _ = 1995 := by rw [fastPCAnchor10]; rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1452 = 2128 := by
  calc
    Artifact.submissionArtifact.instructionPC 1452 =
        Artifact.submissionArtifact.instructionPC 1416 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1416).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1416 36
    _ = 2128 := by rw [fastPCAnchor11]; rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1492 = 2213 := by
  calc
    Artifact.submissionArtifact.instructionPC 1492 =
        Artifact.submissionArtifact.instructionPC 1452 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1452).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1452 40
    _ = 2213 := by rw [fastPCAnchor12]; rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1532 = 2291 := by
  calc
    Artifact.submissionArtifact.instructionPC 1532 =
        Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1492).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1492 40
    _ = 2291 := by rw [fastPCAnchor13]; rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1567 = 2397 := by
  calc
    Artifact.submissionArtifact.instructionPC 1567 =
        Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1532).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1532 35
    _ = 2397 := by rw [fastPCAnchor14]; rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1608 = 2453 := by
  calc
    Artifact.submissionArtifact.instructionPC 1608 =
        Artifact.submissionArtifact.instructionPC 1567 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1567).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1567 41
    _ = 2453 := by rw [fastPCAnchor15]; rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1651 = 2501 := by
  calc
    Artifact.submissionArtifact.instructionPC 1651 =
        Artifact.submissionArtifact.instructionPC 1608 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1608).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1608 43
    _ = 2501 := by rw [fastPCAnchor16]; rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1691 = 2555 := by
  calc
    Artifact.submissionArtifact.instructionPC 1691 =
        Artifact.submissionArtifact.instructionPC 1651 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1651).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1651 40
    _ = 2555 := by rw [fastPCAnchor17]; rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1734 = 2643 := by
  calc
    Artifact.submissionArtifact.instructionPC 1734 =
        Artifact.submissionArtifact.instructionPC 1691 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1691).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1691 43
    _ = 2643 := by rw [fastPCAnchor18]; rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1739 = 2648 := by
  calc
    Artifact.submissionArtifact.instructionPC 1739 =
        Artifact.submissionArtifact.instructionPC 1734 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1734).take 5)).length :=
      instructionPC_add Artifact.submissionArtifact 1734 5
    _ = 2648 := by rw [fastPCAnchor19]; rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1765 = 2686 := by
  calc
    Artifact.submissionArtifact.instructionPC 1765 =
        Artifact.submissionArtifact.instructionPC 1739 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1739).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 1739 26
    _ = 2686 := by rw [fastPCAnchor20]; rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1778 = 2707 := by
  calc
    Artifact.submissionArtifact.instructionPC 1778 =
        Artifact.submissionArtifact.instructionPC 1765 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1765).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1765 13
    _ = 2707 := by rw [fastPCAnchor21]; rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1813 = 2756 := by
  calc
    Artifact.submissionArtifact.instructionPC 1813 =
        Artifact.submissionArtifact.instructionPC 1778 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1778).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1778 35
    _ = 2756 := by rw [fastPCAnchor22]; rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 977 ≤ i) (hii : i ≤ 1016) :
    Artifact.submissionArtifact.instructionPC i =
      ([1314,1315,1317,1318,1319,1321,1322,1323,1326,1327,1329,1330,1331,1332,1333,1336,1337,1338,1341,1342,1343,1344,1347,1348,1349,1352,1353,1354,1356,1357,1359,1360,1361,1363,1364,1365,1366,1367,1369,1370] : List Nat)[i - 977]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (977 + (i - 977)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take (i - 977))).length :=
      instructionPC_add Artifact.submissionArtifact 977 (i - 977)
    _ = _ := by rw [fastPCAnchor0]; interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1017 ≤ i) (hii : i ≤ 1056) :
    Artifact.submissionArtifact.instructionPC i =
      ([1371,1372,1373,1375,1376,1377,1378,1379,1380,1381,1384,1385,1387,1388,1389,1390,1391,1392,1394,1395,1396,1399,1400,1401,1404,1405,1406,1409,1410,1411,1413,1414,1417,1418,1419,1421,1422,1423,1424,1427] : List Nat)[i - 1017]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1017 + (i - 1017)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1017).take (i - 1017))).length :=
      instructionPC_add Artifact.submissionArtifact 1017 (i - 1017)
    _ = _ := by rw [fastPCAnchor1]; interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1096) :
    Artifact.submissionArtifact.instructionPC i =
      ([1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1453,1454,1455,1456,1458,1459,1460,1461,1462,1463,1465,1466,1467,1468,1469,1470,1472,1473,1474,1475] : List Nat)[i - 1057]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1057 + (i - 1057)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1057).take (i - 1057))).length :=
      instructionPC_add Artifact.submissionArtifact 1057 (i - 1057)
    _ = _ := by rw [fastPCAnchor2]; interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1097 ≤ i) (hii : i ≤ 1136) :
    Artifact.submissionArtifact.instructionPC i =
      ([1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1505,1507,1508,1509,1510,1511,1514,1515,1516,1517,1519,1522,1523,1526,1529] : List Nat)[i - 1097]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1097 + (i - 1097)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1097).take (i - 1097))).length :=
      instructionPC_add Artifact.submissionArtifact 1097 (i - 1097)
    _ = _ := by rw [fastPCAnchor3]; interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1137 ≤ i) (hii : i ≤ 1176) :
    Artifact.submissionArtifact.instructionPC i =
      ([1532,1533,1534,1537,1538,1541,1544,1545,1548,1551,1554,1555,1556,1559,1560,1563,1566,1567,1569,1570,1573,1576,1579,1582,1585,1586,1587,1588,1589,1590,1592,1593,1596,1597,1600,1601,1604,1605,1606,1609] : List Nat)[i - 1137]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1137 + (i - 1137)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1137).take (i - 1137))).length :=
      instructionPC_add Artifact.submissionArtifact 1137 (i - 1137)
    _ = _ := by rw [fastPCAnchor4]; interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1177 ≤ i) (hii : i ≤ 1216) :
    Artifact.submissionArtifact.instructionPC i =
      ([1612,1615,1616,1617,1618,1619,1622,1623,1624,1625,1626,1630,1631,1632,1633,1634,1635,1638,1639,1642,1643,1645,1647,1649,1651,1653,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668] : List Nat)[i - 1177]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1177 + (i - 1177)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1177).take (i - 1177))).length :=
      instructionPC_add Artifact.submissionArtifact 1177 (i - 1177)
    _ = _ := by rw [fastPCAnchor5]; interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1217 ≤ i) (hii : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      ([1669,1670,1671,1672,1673,1676,1677,1680,1683,1686,1689,1692,1693,1694,1695,1696,1697,1699,1700,1701,1702,1704,1705,1706,1707,1710,1711,1712,1715,1718,1721,1724,1727,1728,1729,1731,1732,1735,1736,1737] : List Nat)[i - 1217]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1217 + (i - 1217)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1217).take (i - 1217))).length :=
      instructionPC_add Artifact.submissionArtifact 1217 (i - 1217)
    _ = _ := by rw [fastPCAnchor6]; interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1257 ≤ i) (hii : i ≤ 1296) :
    Artifact.submissionArtifact.instructionPC i =
      ([1738,1739,1742,1745,1748,1751,1754,1755,1756,1757,1760,1761,1763,1765,1767,1769,1770,1771,1772,1773,1774,1777,1778,1781,1782,1783,1784,1785,1786,1787,1789,1790,1793,1796,1799,1802,1805,1806,1807,1808] : List Nat)[i - 1257]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1257 + (i - 1257)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1257).take (i - 1257))).length :=
      instructionPC_add Artifact.submissionArtifact 1257 (i - 1257)
    _ = _ := by rw [fastPCAnchor7]; interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1297 ≤ i) (hii : i ≤ 1336) :
    Artifact.submissionArtifact.instructionPC i =
      ([1809,1810,1811,1814,1815,1818,1821,1824,1827,1830,1831,1832,1833,1835,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1852,1854,1855,1858,1859,1860,1863,1866,1869,1872,1875,1876,1877,1878,1879] : List Nat)[i - 1297]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1297 + (i - 1297)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1297).take (i - 1297))).length :=
      instructionPC_add Artifact.submissionArtifact 1297 (i - 1297)
    _ = _ := by rw [fastPCAnchor8]; interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1337 ≤ i) (hii : i ≤ 1376) :
    Artifact.submissionArtifact.instructionPC i =
      ([1880,1883,1884,1885,1886,1887,1888,1891,1892,1893,1894,1895,1896,1899,1900,1901,1902,1903,1904,1905,1906,1907,1910,1911,1912,1915,1916,1919,1920,1921,1922,1925,1926,1927,1929,1930,1931,1932,1935,1936] : List Nat)[i - 1337]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1337 + (i - 1337)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1337).take (i - 1337))).length :=
      instructionPC_add Artifact.submissionArtifact 1337 (i - 1337)
    _ = _ := by rw [fastPCAnchor9]; interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1415) :
    Artifact.submissionArtifact.instructionPC i =
      ([1937,1938,1939,1940,1943,1944,1945,1947,1948,1949,1952,1953,1954,1955,1956,1958,1959,1960,1962,1963,1964,1965,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1977,1978,1983,1984,1985,1993,1994] : List Nat)[i - 1377]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1377 + (i - 1377)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1377).take (i - 1377))).length :=
      instructionPC_add Artifact.submissionArtifact 1377 (i - 1377)
    _ = _ := by rw [fastPCAnchor10]; interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1416 ≤ i) (hii : i ≤ 1451) :
    Artifact.submissionArtifact.instructionPC i =
      ([1995,1996,1999,2000,2033,2066,2068,2070,2072,2074,2076,2078,2080,2082,2084,2086,2088,2090,2092,2094,2096,2098,2100,2102,2104,2106,2108,2110,2112,2114,2116,2118,2120,2122,2124,2126] : List Nat)[i - 1416]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1416 + (i - 1416)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1416 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1416).take (i - 1416))).length :=
      instructionPC_add Artifact.submissionArtifact 1416 (i - 1416)
    _ = _ := by rw [fastPCAnchor11]; interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1452 ≤ i) (hii : i ≤ 1491) :
    Artifact.submissionArtifact.instructionPC i =
      ([2128,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2147,2148,2149,2150,2153,2154,2155,2158,2159,2162,2163,2164,2167,2168,2169,2170,2173,2174,2175,2176,2177,2178,2179,2212] : List Nat)[i - 1452]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1452 + (i - 1452)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1452 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1452).take (i - 1452))).length :=
      instructionPC_add Artifact.submissionArtifact 1452 (i - 1452)
    _ = _ := by rw [fastPCAnchor12]; interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1492 ≤ i) (hii : i ≤ 1531) :
    Artifact.submissionArtifact.instructionPC i =
      ([2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2228,2229,2231,2232,2233,2236,2237,2239,2240,2241,2242,2243,2244,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290] : List Nat)[i - 1492]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1492 + (i - 1492)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1492).take (i - 1492))).length :=
      instructionPC_add Artifact.submissionArtifact 1492 (i - 1492)
    _ = _ := by rw [fastPCAnchor13]; interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1532 ≤ i) (hii : i ≤ 1566) :
    Artifact.submissionArtifact.instructionPC i =
      ([2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2306,2307,2340,2341,2342,2343,2344,2377,2378,2381,2382,2383,2386,2387,2388,2389,2390,2391,2392,2393,2394] : List Nat)[i - 1532]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1532 + (i - 1532)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1532).take (i - 1532))).length :=
      instructionPC_add Artifact.submissionArtifact 1532 (i - 1532)
    _ = _ := by rw [fastPCAnchor14]; interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1567 ≤ i) (hii : i ≤ 1607) :
    Artifact.submissionArtifact.instructionPC i =
      ([2397,2398,2399,2400,2403,2404,2405,2408,2409,2410,2413,2414,2416,2417,2418,2419,2420,2421,2424,2425,2426,2427,2428,2431,2432,2433,2436,2437,2438,2439,2440,2442,2443,2444,2445,2446,2447,2449,2450,2451,2452] : List Nat)[i - 1567]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1567 + (i - 1567)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1567 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1567).take (i - 1567))).length :=
      instructionPC_add Artifact.submissionArtifact 1567 (i - 1567)
    _ = _ := by rw [fastPCAnchor15]; interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1608 ≤ i) (hii : i ≤ 1650) :
    Artifact.submissionArtifact.instructionPC i =
      ([2453,2454,2455,2456,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468,2469,2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,2480,2481,2482,2483,2484,2485,2487,2488,2489,2490,2492,2493,2494,2495,2496,2498,2499,2500] : List Nat)[i - 1608]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1608 + (i - 1608)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1608 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1608).take (i - 1608))).length :=
      instructionPC_add Artifact.submissionArtifact 1608 (i - 1608)
    _ = _ := by rw [fastPCAnchor16]; interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1651 ≤ i) (hii : i ≤ 1690) :
    Artifact.submissionArtifact.instructionPC i =
      ([2501,2504,2505,2506,2509,2510,2511,2512,2513,2516,2517,2518,2521,2522,2525,2526,2527,2530,2531,2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549,2550,2551,2552,2553,2554] : List Nat)[i - 1651]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1651 + (i - 1651)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1651 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1651).take (i - 1651))).length :=
      instructionPC_add Artifact.submissionArtifact 1651 (i - 1651)
    _ = _ := by rw [fastPCAnchor17]; interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1691 ≤ i) (hii : i ≤ 1733) :
    Artifact.submissionArtifact.instructionPC i =
      ([2555,2556,2557,2558,2559,2560,2561,2562,2563,2564,2565,2566,2567,2569,2570,2571,2572,2574,2575,2576,2577,2578,2580,2581,2582,2583,2586,2587,2588,2591,2592,2593,2594,2595,2596,2599,2600,2601,2634,2635,2638,2639,2642] : List Nat)[i - 1691]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1691 + (i - 1691)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1691 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1691).take (i - 1691))).length :=
      instructionPC_add Artifact.submissionArtifact 1691 (i - 1691)
    _ = _ := by rw [fastPCAnchor18]; interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1734 ≤ i) (hii : i ≤ 1738) :
    Artifact.submissionArtifact.instructionPC i =
      ([2643,2644,2645,2646,2647] : List Nat)[i - 1734]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1734 + (i - 1734)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1734 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1734).take (i - 1734))).length :=
      instructionPC_add Artifact.submissionArtifact 1734 (i - 1734)
    _ = _ := by rw [fastPCAnchor19]; interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1739 ≤ i) (hii : i ≤ 1764) :
    Artifact.submissionArtifact.instructionPC i =
      ([2648,2649,2652,2653,2654,2655,2658,2659,2660,2662,2663,2666,2667,2668,2669,2672,2673,2674,2675,2676,2677,2678,2682,2683,2684,2685] : List Nat)[i - 1739]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1739 + (i - 1739)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1739 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1739).take (i - 1739))).length :=
      instructionPC_add Artifact.submissionArtifact 1739 (i - 1739)
    _ = _ := by rw [fastPCAnchor20]; interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1765 ≤ i) (hii : i ≤ 1777) :
    Artifact.submissionArtifact.instructionPC i =
      ([2686,2687,2688,2689,2691,2692,2693,2696,2697,2699,2702,2703,2706] : List Nat)[i - 1765]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1765 + (i - 1765)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1765 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1765).take (i - 1765))).length :=
      instructionPC_add Artifact.submissionArtifact 1765 (i - 1765)
    _ = _ := by rw [fastPCAnchor21]; interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1778 ≤ i) (hii : i ≤ 1812) :
    Artifact.submissionArtifact.instructionPC i =
      ([2707,2708,2709,2712,2713,2714,2715,2716,2717,2718,2719,2722,2723,2725,2728,2729,2730,2731,2732,2734,2735,2736,2737,2739,2740,2741,2742,2744,2745,2746,2748,2749,2751,2752,2755] : List Nat)[i - 1778]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1778 + (i - 1778)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1778 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1778).take (i - 1778))).length :=
      instructionPC_add Artifact.submissionArtifact 1778 (i - 1778)
    _ = _ := by rw [fastPCAnchor22]; interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1813 ≤ i) (hii : i ≤ 1827) :
    Artifact.submissionArtifact.instructionPC i =
      ([2756,2757,2758,2761,2762,2765,2766,2769,2772,2773,2776,2779,2780,2781,2784] : List Nat)[i - 1813]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1813 + (i - 1813)) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1813 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1813).take (i - 1813))).length :=
      instructionPC_add Artifact.submissionArtifact 1813 (i - 1813)
    _ = _ := by rw [fastPCAnchor23]; interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2202 ≤ i) (hii : i ≤ 2254) :
    Artifact.submissionArtifact.instructionPC i =
      ([3391,3392,3393,3394,3395,3396,3397,3399,3400,3401,3402,3405,3406,3407,3409,3412,3413,3416,3419,3422,3425,3428,3429,3430,3433,3436,3439,3442,3445,3446,3447,3448,3450,3451,3453,3454,3455,3456,3458,3459,3460,3462,3463,3465,3466,3467,3468,3469,3472,3473,3474,3476,3479] : List Nat)[i - 2202]! := by
  interval_cases i <;> decide

@[simp] theorem complementPC1578 : Artifact.submissionArtifact.instructionPC 1579 = 2416 := by rfl
@[simp] theorem complementPC1637 : Artifact.submissionArtifact.instructionPC 1639 = 2487 := by rfl
@[simp] theorem complementPC1640 : Artifact.submissionArtifact.instructionPC 1643 = 2492 := by rfl
@[simp] theorem complementPC1644 : Artifact.submissionArtifact.instructionPC 1648 = 2498 := by rfl
@[simp] theorem complementPC1699 : Artifact.submissionArtifact.instructionPC 1704 = 2569 := by rfl
@[simp] theorem complementPC1702 : Artifact.submissionArtifact.instructionPC 1708 = 2574 := by rfl
@[simp] theorem complementPC1706 : Artifact.submissionArtifact.instructionPC 1713 = 2580 := by rfl
@[simp] theorem complementPC2520 : Artifact.submissionArtifact.instructionPC 2528 = 3866 := by rfl
@[simp] theorem complementPC2549 : Artifact.submissionArtifact.instructionPC 2558 = 3897 := by rfl
@[simp] theorem complementPC2553 : Artifact.submissionArtifact.instructionPC 2563 = 3903 := by rfl
@[simp] theorem complementPC2558 : Artifact.submissionArtifact.instructionPC 2569 = 3910 := by rfl
@[simp] theorem complementPC2587 : Artifact.submissionArtifact.instructionPC 2599 = 3941 := by rfl
@[simp] theorem complementPC2591 : Artifact.submissionArtifact.instructionPC 2604 = 3947 := by rfl
@[simp] theorem complementPC2596 : Artifact.submissionArtifact.instructionPC 2610 = 3954 := by rfl
@[simp] theorem complementPC2625 : Artifact.submissionArtifact.instructionPC 2640 = 3985 := by rfl
@[simp] theorem complementPC2629 : Artifact.submissionArtifact.instructionPC 2645 = 3991 := by rfl
@[simp] theorem complementPC2634 : Artifact.submissionArtifact.instructionPC 2651 = 3998 := by rfl
@[simp] theorem complementPC2663 : Artifact.submissionArtifact.instructionPC 2681 = 4029 := by rfl
@[simp] theorem complementPC2667 : Artifact.submissionArtifact.instructionPC 2686 = 4035 := by rfl
@[simp] theorem complementPC2729 : Artifact.submissionArtifact.instructionPC 2749 = 4129 := by rfl
@[simp] theorem complementPC2901 : Artifact.submissionArtifact.instructionPC 2922 = 4357 := by rfl
@[simp] theorem complementPC2930 : Artifact.submissionArtifact.instructionPC 2952 = 4388 := by rfl
@[simp] theorem complementPC2934 : Artifact.submissionArtifact.instructionPC 2957 = 4394 := by rfl
@[simp] theorem complementPC3001 : Artifact.submissionArtifact.instructionPC 3025 = 4477 := by rfl
@[simp] theorem complementPC3054 : Artifact.submissionArtifact.instructionPC 3079 = 4550 := by rfl
@[simp] theorem complementLiteral0 : UInt256.lnot (0 : UInt256) = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) := by decide
@[simp] theorem complementLiteral31 : UInt256.lnot (31 : UInt256) = (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) := by decide

set_option linter.unusedSimpArgs false in
 theorem runComplement1578 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1578 1 31, opAt 1579 .NOT]
      { template with pc := UInt256.ofNat 2414, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2417,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1578 = 2414 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1579 = 2416 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement1637 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1638 1 31, opAt 1639 .NOT]
      { template with pc := UInt256.ofNat 2485, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2488,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1638 = 2485 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1639 = 2487 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement1640 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1642 1 31, opAt 1643 .NOT]
      { template with pc := UInt256.ofNat 2490, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2493,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1642 = 2490 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1643 = 2492 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement1644 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1647 1 31, opAt 1648 .NOT]
      { template with pc := UInt256.ofNat 2496, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2499,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1647 = 2496 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1648 = 2498 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement1699 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1703 1 31, opAt 1704 .NOT]
      { template with pc := UInt256.ofNat 2567, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2570,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1703 = 2567 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1704 = 2569 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement1702 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1707 1 31, opAt 1708 .NOT]
      { template with pc := UInt256.ofNat 2572, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2575,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1707 = 2572 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1708 = 2574 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement1706 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 1712 1 31, opAt 1713 .NOT]
      { template with pc := UInt256.ofNat 2578, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 2581,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 1712 = 2578 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1713 = 2580 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2520 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2527 1 0, opAt 2528 .NOT]
      { template with pc := UInt256.ofNat 3864, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3867,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2527 = 3864 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2528 = 3866 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral0,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2549 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2557 1 31, opAt 2558 .NOT]
      { template with pc := UInt256.ofNat 3895, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3898,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2557 = 3895 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2558 = 3897 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2553 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2562 1 31, opAt 2563 .NOT]
      { template with pc := UInt256.ofNat 3901, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3904,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2562 = 3901 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2563 = 3903 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2558 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2568 1 0, opAt 2569 .NOT]
      { template with pc := UInt256.ofNat 3908, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3911,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2568 = 3908 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2569 = 3910 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral0,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2587 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2598 1 31, opAt 2599 .NOT]
      { template with pc := UInt256.ofNat 3939, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3942,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2598 = 3939 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2599 = 3941 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2591 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2603 1 31, opAt 2604 .NOT]
      { template with pc := UInt256.ofNat 3945, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3948,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2603 = 3945 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2604 = 3947 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2596 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2609 1 0, opAt 2610 .NOT]
      { template with pc := UInt256.ofNat 3952, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3955,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2609 = 3952 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2610 = 3954 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral0,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2625 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2639 1 31, opAt 2640 .NOT]
      { template with pc := UInt256.ofNat 3983, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3986,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2639 = 3983 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2640 = 3985 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2629 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2644 1 31, opAt 2645 .NOT]
      { template with pc := UInt256.ofNat 3989, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3992,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2644 = 3989 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2645 = 3991 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2634 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2650 1 0, opAt 2651 .NOT]
      { template with pc := UInt256.ofNat 3996, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 3999,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2650 = 3996 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2651 = 3998 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral0,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2663 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2680 1 31, opAt 2681 .NOT]
      { template with pc := UInt256.ofNat 4027, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4030,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2680 = 4027 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2681 = 4029 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2667 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2685 1 31, opAt 2686 .NOT]
      { template with pc := UInt256.ofNat 4033, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4036,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2685 = 4033 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2686 = 4035 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2729 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2748 1 31, opAt 2749 .NOT]
      { template with pc := UInt256.ofNat 4127, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4130,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2748 = 4127 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2749 = 4129 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2901 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2921 1 0, opAt 2922 .NOT]
      { template with pc := UInt256.ofNat 4355, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4358,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2921 = 4355 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2922 = 4357 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral0,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2930 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2951 1 31, opAt 2952 .NOT]
      { template with pc := UInt256.ofNat 4386, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4389,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2951 = 4386 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2952 = 4388 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement2934 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 2956 1 31, opAt 2957 .NOT]
      { template with pc := UInt256.ofNat 4392, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4395,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 2956 = 4392 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 2957 = 4394 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement3001 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 3024 1 31, opAt 3025 .NOT]
      { template with pc := UInt256.ofNat 4475, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4478,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 3024 = 4475 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 3025 = 4477 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
 theorem runComplement3054 (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt 3078 1 31, opAt 3079 .NOT]
      { template with pc := UInt256.ofNat 4548, stack := rest, halt := .Running } =
    some { template with pc := UInt256.ofNat 4551,
      stack := (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) :: rest, halt := .Running } := by
  have hpc0 : Artifact.submissionArtifact.instructionPC 3078 = 4548 := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 3079 = 4550 := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral31,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1974 = true :=
  Artifact.isValidJumpDest_index 1406 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1995 = true :=
  Artifact.isValidJumpDest_index 1416 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2241 = true :=
  Artifact.isValidJumpDest_index 1514 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2432 = true :=
  Artifact.isValidJumpDest_index 1591 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2465 = true :=
  Artifact.isValidJumpDest_index 1618 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2517 = true :=
  Artifact.isValidJumpDest_index 1661 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2541 = true :=
  Artifact.isValidJumpDest_index 1677 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2648 = true :=
  Artifact.isValidJumpDest_index 1739 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2659 = true :=
  Artifact.isValidJumpDest_index 1746 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2662 = true :=
  Artifact.isValidJumpDest_index 1748 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2673 = true :=
  Artifact.isValidJumpDest_index 1755 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2686 = true :=
  Artifact.isValidJumpDest_index 1765 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2707 = true :=
  Artifact.isValidJumpDest_index 1778 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2729 = true :=
  Artifact.isValidJumpDest_index 1793 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2756 = true :=
  Artifact.isValidJumpDest_index 1813 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2780 = true :=
  Artifact.isValidJumpDest_index 1825 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3356 = true :=
  Artifact.isValidJumpDest_index 2179 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3391 = true :=
  Artifact.isValidJumpDest_index 2202 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3429 = true :=
  Artifact.isValidJumpDest_index 2224 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3446 = true :=
  Artifact.isValidJumpDest_index 2231 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
