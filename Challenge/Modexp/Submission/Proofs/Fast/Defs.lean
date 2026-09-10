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
    Artifact.submissionArtifact.instructionPC 977 = 1307 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1017 = 1364 := by
  calc
    Artifact.submissionArtifact.instructionPC 1017 =
        Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 977 40
    _ = 1364 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1057 = 1421 := by
  calc
    Artifact.submissionArtifact.instructionPC 1057 =
        Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1017).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1017 40
    _ = 1421 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1097 = 1469 := by
  calc
    Artifact.submissionArtifact.instructionPC 1097 =
        Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1057).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1057 40
    _ = 1469 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1137 = 1525 := by
  calc
    Artifact.submissionArtifact.instructionPC 1137 =
        Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1097).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1097 40
    _ = 1525 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1177 = 1601 := by
  calc
    Artifact.submissionArtifact.instructionPC 1177 =
        Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1137).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1137 40
    _ = 1601 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1217 = 1650 := by
  calc
    Artifact.submissionArtifact.instructionPC 1217 =
        Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1177).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1177 40
    _ = 1650 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1257 = 1719 := by
  calc
    Artifact.submissionArtifact.instructionPC 1257 =
        Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1217).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1217 40
    _ = 1719 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1297 = 1786 := by
  calc
    Artifact.submissionArtifact.instructionPC 1297 =
        Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1257).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1257 40
    _ = 1786 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1337 = 1857 := by
  calc
    Artifact.submissionArtifact.instructionPC 1337 =
        Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1297).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1297 40
    _ = 1857 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1377 = 1914 := by
  calc
    Artifact.submissionArtifact.instructionPC 1377 =
        Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1337).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1337 40
    _ = 1914 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1416 = 1965 := by
  calc
    Artifact.submissionArtifact.instructionPC 1416 =
        Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1377).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1377 39
    _ = 1965 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1453 = 2002 := by
  calc
    Artifact.submissionArtifact.instructionPC 1453 =
        Artifact.submissionArtifact.instructionPC 1416 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1416).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1416 37
    _ = 2002 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1496 = 2061 := by
  calc
    Artifact.submissionArtifact.instructionPC 1496 =
        Artifact.submissionArtifact.instructionPC 1453 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1453).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1453 43
    _ = 2061 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1537 = 2108 := by
  calc
    Artifact.submissionArtifact.instructionPC 1537 =
        Artifact.submissionArtifact.instructionPC 1496 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1496).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1496 41
    _ = 2108 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1574 = 2154 := by
  calc
    Artifact.submissionArtifact.instructionPC 1574 =
        Artifact.submissionArtifact.instructionPC 1537 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1537).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1537 37
    _ = 2154 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1615 = 2210 := by
  calc
    Artifact.submissionArtifact.instructionPC 1615 =
        Artifact.submissionArtifact.instructionPC 1574 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1574).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1574 41
    _ = 2210 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1658 = 2258 := by
  calc
    Artifact.submissionArtifact.instructionPC 1658 =
        Artifact.submissionArtifact.instructionPC 1615 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1615).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1615 43
    _ = 2258 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1698 = 2312 := by
  calc
    Artifact.submissionArtifact.instructionPC 1698 =
        Artifact.submissionArtifact.instructionPC 1658 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1658).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1658 40
    _ = 2312 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1738 = 2490 := by
  calc
    Artifact.submissionArtifact.instructionPC 1738 =
        Artifact.submissionArtifact.instructionPC 1698 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1698).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1698 40
    _ = 2490 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1743 = 2495 := by
  calc
    Artifact.submissionArtifact.instructionPC 1743 =
        Artifact.submissionArtifact.instructionPC 1738 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1738).take 5)).length :=
      instructionPC_add Artifact.submissionArtifact 1738 5
    _ = 2495 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1769 = 2533 := by
  calc
    Artifact.submissionArtifact.instructionPC 1769 =
        Artifact.submissionArtifact.instructionPC 1743 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1743).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 1743 26
    _ = 2533 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1782 = 2554 := by
  calc
    Artifact.submissionArtifact.instructionPC 1782 =
        Artifact.submissionArtifact.instructionPC 1769 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1769).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1769 13
    _ = 2554 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1817 = 2603 := by
  calc
    Artifact.submissionArtifact.instructionPC 1817 =
        Artifact.submissionArtifact.instructionPC 1782 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1782).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1782 35
    _ = 2603 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 977 ≤ i) (hii : i ≤ 1016) :
    Artifact.submissionArtifact.instructionPC i =
      [1307,1308,1310,1311,1312,1314,1315,1316,1319,1320,1322,1323,1324,1325,1326,1329,1330,1331,1334,1335,1336,1337,1340,1341,1342,1345,1346,1347,1349,1350,1352,1353,1354,1356,1357,1358,1359,1360,1362,1363][i - 977]! := by
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
      [1364,1365,1366,1368,1369,1370,1371,1372,1373,1374,1377,1378,1380,1381,1382,1383,1384,1385,1387,1388,1389,1392,1393,1394,1397,1398,1399,1402,1403,1404,1406,1407,1410,1411,1412,1414,1415,1416,1417,1420][i - 1017]! := by
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

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1096) :
    Artifact.submissionArtifact.instructionPC i =
      [1421,1422,1425,1426,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1446,1447,1448,1449,1451,1452,1453,1454,1455,1456,1458,1459,1460,1461,1462,1463,1465,1466,1467,1468][i - 1057]! := by
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

@[simp] theorem fastPC3 (i : Nat) (hi : 1097 ≤ i) (hii : i ≤ 1136) :
    Artifact.submissionArtifact.instructionPC i =
      [1469,1470,1472,1473,1474,1475,1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1507,1508,1509,1510,1512,1515,1516,1519,1522][i - 1097]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1097 + (i - 1097)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1097).take (i - 1097))).length :=
      instructionPC_add Artifact.submissionArtifact 1097 (i - 1097)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1137 ≤ i) (hii : i ≤ 1176) :
    Artifact.submissionArtifact.instructionPC i =
      [1525,1526,1527,1530,1531,1534,1537,1538,1541,1544,1547,1548,1549,1552,1553,1556,1559,1560,1562,1563,1566,1569,1572,1575,1578,1579,1580,1581,1582,1583,1585,1586,1589,1590,1593,1594,1597,1598,1599,1600][i - 1137]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1137 + (i - 1137)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1137).take (i - 1137))).length :=
      instructionPC_add Artifact.submissionArtifact 1137 (i - 1137)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1177 ≤ i) (hii : i ≤ 1216) :
    Artifact.submissionArtifact.instructionPC i =
      [1601,1602,1603,1604,1605,1606,1609,1610,1611,1612,1613,1617,1618,1619,1620,1621,1622,1625,1626,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649][i - 1177]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1177 + (i - 1177)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1177).take (i - 1177))).length :=
      instructionPC_add Artifact.submissionArtifact 1177 (i - 1177)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1217 ≤ i) (hii : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1650,1651,1652,1653,1654,1657,1658,1661,1664,1667,1670,1673,1674,1675,1676,1677,1678,1680,1681,1682,1683,1685,1686,1687,1688,1691,1692,1693,1696,1699,1702,1705,1708,1709,1710,1712,1713,1716,1717,1718][i - 1217]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1217 + (i - 1217)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1217).take (i - 1217))).length :=
      instructionPC_add Artifact.submissionArtifact 1217 (i - 1217)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1257 ≤ i) (hii : i ≤ 1296) :
    Artifact.submissionArtifact.instructionPC i =
      [1719,1720,1723,1726,1729,1732,1735,1736,1737,1738,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1754,1755,1758,1759,1760,1761,1762,1763,1764,1766,1767,1770,1773,1776,1779,1782,1783,1784,1785][i - 1257]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1257 + (i - 1257)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1257).take (i - 1257))).length :=
      instructionPC_add Artifact.submissionArtifact 1257 (i - 1257)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1297 ≤ i) (hii : i ≤ 1336) :
    Artifact.submissionArtifact.instructionPC i =
      [1786,1787,1788,1791,1792,1795,1798,1801,1804,1807,1808,1809,1810,1812,1813,1814,1817,1818,1819,1820,1822,1823,1826,1827,1828,1829,1831,1832,1835,1836,1837,1840,1843,1846,1849,1852,1853,1854,1855,1856][i - 1297]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1297 + (i - 1297)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1297).take (i - 1297))).length :=
      instructionPC_add Artifact.submissionArtifact 1297 (i - 1297)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1337 ≤ i) (hii : i ≤ 1376) :
    Artifact.submissionArtifact.instructionPC i =
      [1857,1860,1861,1862,1863,1864,1865,1868,1869,1870,1871,1872,1873,1876,1877,1878,1879,1880,1881,1882,1883,1884,1887,1888,1889,1892,1893,1896,1897,1898,1899,1902,1903,1904,1906,1907,1908,1909,1912,1913][i - 1337]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1337 + (i - 1337)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1337).take (i - 1337))).length :=
      instructionPC_add Artifact.submissionArtifact 1337 (i - 1337)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1415) :
    Artifact.submissionArtifact.instructionPC i =
      [1914,1915,1916,1917,1920,1921,1922,1924,1925,1926,1929,1930,1931,1932,1933,1935,1936,1937,1939,1940,1941,1942,1943,1944,1945,1947,1948,1949,1950,1951,1952,1953,1954,1955,1958,1959,1960,1963,1964][i - 1377]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1377 + (i - 1377)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1377).take (i - 1377))).length :=
      instructionPC_add Artifact.submissionArtifact 1377 (i - 1377)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1416 ≤ i) (hii : i ≤ 1452) :
    Artifact.submissionArtifact.instructionPC i =
      [1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001][i - 1416]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1416 + (i - 1416)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1416 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1416).take (i - 1416))).length :=
      instructionPC_add Artifact.submissionArtifact 1416 (i - 1416)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1453 ≤ i) (hii : i ≤ 1495) :
    Artifact.submissionArtifact.instructionPC i =
      [2002,2003,2005,2006,2007,2008,2010,2011,2012,2013,2014,2015,2016,2019,2020,2021,2022,2023,2026,2027,2028,2029,2032,2033,2034,2037,2038,2041,2042,2043,2046,2047,2048,2049,2052,2053,2054,2055,2056,2057,2058,2059,2060][i - 1453]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1453 + (i - 1453)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1453 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1453).take (i - 1453))).length :=
      instructionPC_add Artifact.submissionArtifact 1453 (i - 1453)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1496 ≤ i) (hii : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2076,2077,2079,2080,2081,2084,2085,2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107][i - 1496]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1496 + (i - 1496)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1496 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1496).take (i - 1496))).length :=
      instructionPC_add Artifact.submissionArtifact 1496 (i - 1496)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1537 ≤ i) (hii : i ≤ 1573) :
    Artifact.submissionArtifact.instructionPC i =
      [2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2123,2124,2126,2127,2128,2129,2130,2131,2133,2134,2135,2138,2139,2140,2143,2144,2145,2146,2147,2148,2149,2150,2151][i - 1537]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1537 + (i - 1537)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1537 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1537).take (i - 1537))).length :=
      instructionPC_add Artifact.submissionArtifact 1537 (i - 1537)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1574 ≤ i) (hii : i ≤ 1614) :
    Artifact.submissionArtifact.instructionPC i =
      [2154,2155,2156,2157,2160,2161,2162,2165,2166,2167,2170,2171,2173,2174,2175,2176,2177,2178,2181,2182,2183,2184,2185,2188,2189,2190,2193,2194,2195,2196,2197,2199,2200,2201,2202,2203,2204,2206,2207,2208,2209][i - 1574]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1574 + (i - 1574)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1574 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1574).take (i - 1574))).length :=
      instructionPC_add Artifact.submissionArtifact 1574 (i - 1574)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1615 ≤ i) (hii : i ≤ 1657) :
    Artifact.submissionArtifact.instructionPC i =
      [2210,2211,2212,2213,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2244,2245,2246,2247,2249,2250,2251,2252,2253,2255,2256,2257][i - 1615]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1615 + (i - 1615)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1615 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1615).take (i - 1615))).length :=
      instructionPC_add Artifact.submissionArtifact 1615 (i - 1615)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1658 ≤ i) (hii : i ≤ 1697) :
    Artifact.submissionArtifact.instructionPC i =
      [2258,2261,2262,2263,2266,2267,2268,2269,2270,2273,2274,2275,2278,2279,2282,2283,2284,2287,2288,2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311][i - 1658]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1658 + (i - 1658)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1658 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1658).take (i - 1658))).length :=
      instructionPC_add Artifact.submissionArtifact 1658 (i - 1658)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1698 ≤ i) (hii : i ≤ 1737) :
    Artifact.submissionArtifact.instructionPC i =
      [2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2357,2358,2359,2392,2393,2394,2395,2428,2429,2430,2433,2434,2435,2438,2439,2440,2441,2442,2443,2446,2447,2448,2481,2482,2485,2486,2489][i - 1698]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1698 + (i - 1698)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1698 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1698).take (i - 1698))).length :=
      instructionPC_add Artifact.submissionArtifact 1698 (i - 1698)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1738 ≤ i) (hii : i ≤ 1742) :
    Artifact.submissionArtifact.instructionPC i =
      [2490,2491,2492,2493,2494][i - 1738]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1738 + (i - 1738)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1738 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1738).take (i - 1738))).length :=
      instructionPC_add Artifact.submissionArtifact 1738 (i - 1738)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1743 ≤ i) (hii : i ≤ 1768) :
    Artifact.submissionArtifact.instructionPC i =
      [2495,2496,2499,2500,2501,2502,2505,2506,2507,2509,2510,2513,2514,2515,2516,2519,2520,2521,2522,2523,2524,2525,2529,2530,2531,2532][i - 1743]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1743 + (i - 1743)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1743 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1743).take (i - 1743))).length :=
      instructionPC_add Artifact.submissionArtifact 1743 (i - 1743)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1769 ≤ i) (hii : i ≤ 1781) :
    Artifact.submissionArtifact.instructionPC i =
      [2533,2534,2535,2536,2538,2539,2540,2543,2544,2546,2549,2550,2553][i - 1769]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1769 + (i - 1769)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1769 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1769).take (i - 1769))).length :=
      instructionPC_add Artifact.submissionArtifact 1769 (i - 1769)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1782 ≤ i) (hii : i ≤ 1816) :
    Artifact.submissionArtifact.instructionPC i =
      [2554,2555,2556,2559,2560,2561,2562,2563,2564,2565,2566,2569,2570,2572,2575,2576,2577,2578,2579,2581,2582,2583,2584,2586,2587,2588,2589,2591,2592,2593,2595,2596,2598,2599,2602][i - 1782]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1782 + (i - 1782)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1782 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1782).take (i - 1782))).length :=
      instructionPC_add Artifact.submissionArtifact 1782 (i - 1782)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1817 ≤ i) (hii : i ≤ 1831) :
    Artifact.submissionArtifact.instructionPC i =
      [2603,2604,2605,2608,2609,2612,2613,2616,2619,2620,2623,2626,2627,2628,2631][i - 1817]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1817 + (i - 1817)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1817 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1817).take (i - 1817))).length :=
      instructionPC_add Artifact.submissionArtifact 1817 (i - 1817)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat)
    (hi : 2466 ≤ i) (hii : i ≤ 2518) :
    Artifact.submissionArtifact.instructionPC i =
      ([3349,3350,3351,3352,3353,3354,3355,3357,3358,3359,3360,3363,3364,3365,3367,3370,3371,3374,3377,3380,3383,3386,3387,3388,3391,3394,3397,3400,3403,3404,3405,3406,3408,3409,3411,3412,3413,3414,3416,3417,3418,3420,3421,3423,3424,3425,3426,3427,3430,3431,3432,3434,3437] : List Nat)[i - 2466]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1526 = true :=
  Artifact.isValidJumpDest_index 1138 (by rfl)

theorem jumpDest1555 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1548 = true :=
  Artifact.isValidJumpDest_index 1148 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1562 = true :=
  Artifact.isValidJumpDest_index 1155 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1579 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1602 = true :=
  Artifact.isValidJumpDest_index 1178 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1618 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1649 = true :=
  Artifact.isValidJumpDest_index 1216 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1674 = true :=
  Artifact.isValidJumpDest_index 1229 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1709 = true :=
  Artifact.isValidJumpDest_index 1250 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1717 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1736 = true :=
  Artifact.isValidJumpDest_index 1264 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1265 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1746 = true :=
  Artifact.isValidJumpDest_index 1272 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1766 = true :=
  Artifact.isValidJumpDest_index 1287 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1783 = true :=
  Artifact.isValidJumpDest_index 1294 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1808 = true :=
  Artifact.isValidJumpDest_index 1307 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1809 = true :=
  Artifact.isValidJumpDest_index 1308 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1827 = true :=
  Artifact.isValidJumpDest_index 1320 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1853 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1863 = true :=
  Artifact.isValidJumpDest_index 1341 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1869 = true :=
  Artifact.isValidJumpDest_index 1345 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1877 = true :=
  Artifact.isValidJumpDest_index 1351 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1888 = true :=
  Artifact.isValidJumpDest_index 1360 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1892 = true :=
  Artifact.isValidJumpDest_index 1362 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1903 = true :=
  Artifact.isValidJumpDest_index 1369 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1916 = true :=
  Artifact.isValidJumpDest_index 1379 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1951 = true :=
  Artifact.isValidJumpDest_index 1406 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1965 = true :=
  Artifact.isValidJumpDest_index 1416 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2089 = true :=
  Artifact.isValidJumpDest_index 1518 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2189 = true :=
  Artifact.isValidJumpDest_index 1598 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2222 = true :=
  Artifact.isValidJumpDest_index 1625 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2274 = true :=
  Artifact.isValidJumpDest_index 1668 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2298 = true :=
  Artifact.isValidJumpDest_index 1684 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2495 = true :=
  Artifact.isValidJumpDest_index 1743 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2506 = true :=
  Artifact.isValidJumpDest_index 1750 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2509 = true :=
  Artifact.isValidJumpDest_index 1752 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2520 = true :=
  Artifact.isValidJumpDest_index 1759 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2533 = true :=
  Artifact.isValidJumpDest_index 1769 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2554 = true :=
  Artifact.isValidJumpDest_index 1782 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2576 = true :=
  Artifact.isValidJumpDest_index 1797 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2603 = true :=
  Artifact.isValidJumpDest_index 1817 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2627 = true :=
  Artifact.isValidJumpDest_index 1829 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3314 = true :=
  Artifact.isValidJumpDest_index 2443 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3349 = true :=
  Artifact.isValidJumpDest_index 2466 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3387 = true :=
  Artifact.isValidJumpDest_index 2488 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3404 = true :=
  Artifact.isValidJumpDest_index 2495 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
