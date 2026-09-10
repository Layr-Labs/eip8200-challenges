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
    Artifact.submissionArtifact.instructionPC 1089 = 1476 := by
  calc
    Artifact.submissionArtifact.instructionPC 1089 =
        Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1057).take 32)).length :=
      instructionPC_add Artifact.submissionArtifact 1057 32
    _ = 1476 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1129 = 1532 := by
  calc
    Artifact.submissionArtifact.instructionPC 1129 =
        Artifact.submissionArtifact.instructionPC 1089 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1089).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1089 40
    _ = 1532 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1169 = 1612 := by
  calc
    Artifact.submissionArtifact.instructionPC 1169 =
        Artifact.submissionArtifact.instructionPC 1129 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1129).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1129 40
    _ = 1612 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1209 = 1669 := by
  calc
    Artifact.submissionArtifact.instructionPC 1209 =
        Artifact.submissionArtifact.instructionPC 1169 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1169).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1169 40
    _ = 1669 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1249 = 1738 := by
  calc
    Artifact.submissionArtifact.instructionPC 1249 =
        Artifact.submissionArtifact.instructionPC 1209 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1209).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1209 40
    _ = 1738 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1289 = 1809 := by
  calc
    Artifact.submissionArtifact.instructionPC 1289 =
        Artifact.submissionArtifact.instructionPC 1249 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1249).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1249 40
    _ = 1809 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1329 = 1880 := by
  calc
    Artifact.submissionArtifact.instructionPC 1329 =
        Artifact.submissionArtifact.instructionPC 1289 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1289).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1289 40
    _ = 1880 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1369 = 1937 := by
  calc
    Artifact.submissionArtifact.instructionPC 1369 =
        Artifact.submissionArtifact.instructionPC 1329 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1329).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1329 40
    _ = 1937 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1408 = 1995 := by
  calc
    Artifact.submissionArtifact.instructionPC 1408 =
        Artifact.submissionArtifact.instructionPC 1369 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1369).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1369 39
    _ = 1995 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1445 = 2032 := by
  calc
    Artifact.submissionArtifact.instructionPC 1445 =
        Artifact.submissionArtifact.instructionPC 1408 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1408).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1408 37
    _ = 2032 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1488 = 2091 := by
  calc
    Artifact.submissionArtifact.instructionPC 1488 =
        Artifact.submissionArtifact.instructionPC 1445 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1445).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1445 43
    _ = 2091 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1529 = 2138 := by
  calc
    Artifact.submissionArtifact.instructionPC 1529 =
        Artifact.submissionArtifact.instructionPC 1488 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1488).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1488 41
    _ = 2138 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1566 = 2184 := by
  calc
    Artifact.submissionArtifact.instructionPC 1566 =
        Artifact.submissionArtifact.instructionPC 1529 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1529).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1529 37
    _ = 2184 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1607 = 2240 := by
  calc
    Artifact.submissionArtifact.instructionPC 1607 =
        Artifact.submissionArtifact.instructionPC 1566 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1566).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1566 41
    _ = 2240 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1650 = 2288 := by
  calc
    Artifact.submissionArtifact.instructionPC 1650 =
        Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1607).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1607 43
    _ = 2288 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1690 = 2426 := by
  calc
    Artifact.submissionArtifact.instructionPC 1690 =
        Artifact.submissionArtifact.instructionPC 1650 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1650).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1650 40
    _ = 2426 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1711 = 2491 := by
  calc
    Artifact.submissionArtifact.instructionPC 1711 =
        Artifact.submissionArtifact.instructionPC 1690 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1690).take 21)).length :=
      instructionPC_add Artifact.submissionArtifact 1690 21
    _ = 2491 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1716 = 2496 := by
  calc
    Artifact.submissionArtifact.instructionPC 1716 =
        Artifact.submissionArtifact.instructionPC 1711 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1711).take 5)).length :=
      instructionPC_add Artifact.submissionArtifact 1711 5
    _ = 2496 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1742 = 2534 := by
  calc
    Artifact.submissionArtifact.instructionPC 1742 =
        Artifact.submissionArtifact.instructionPC 1716 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1716).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 1716 26
    _ = 2534 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1755 = 2555 := by
  calc
    Artifact.submissionArtifact.instructionPC 1755 =
        Artifact.submissionArtifact.instructionPC 1742 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1742).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1742 13
    _ = 2555 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1790 = 2604 := by
  calc
    Artifact.submissionArtifact.instructionPC 1790 =
        Artifact.submissionArtifact.instructionPC 1755 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1755).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1755 35
    _ = 2604 := by
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
      [1371,1372,1373,1375,1376,1377,1378,1379,1380,1381,1384,1385,1387,1388,1389,1390,1391,1392,1394,1395,1396,1399,1400,1401,1404,1405,1406,1409,1410,1411,1413,1414,1417,1418,1419,1421,1422,1423,1424,1427][i - 1017]! := by
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

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1088) :
    Artifact.submissionArtifact.instructionPC i =
      [1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1463,1464,1466,1467,1468,1469,1470,1472,1473,1474,1475][i - 1057]! := by
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

@[simp] theorem fastPC3 (i : Nat) (hi : 1089 ≤ i) (hii : i ≤ 1128) :
    Artifact.submissionArtifact.instructionPC i =
      [1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1505,1507,1508,1509,1510,1511,1514,1515,1516,1517,1519,1522,1523,1526,1529][i - 1089]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1089 + (i - 1089)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1089 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1089).take (i - 1089))).length :=
      instructionPC_add Artifact.submissionArtifact 1089 (i - 1089)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1129 ≤ i) (hii : i ≤ 1168) :
    Artifact.submissionArtifact.instructionPC i =
      [1532,1533,1534,1537,1538,1541,1544,1545,1548,1551,1554,1555,1556,1559,1560,1563,1566,1567,1569,1570,1573,1576,1579,1582,1585,1586,1587,1588,1589,1590,1592,1593,1596,1597,1600,1601,1604,1605,1606,1609][i - 1129]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1129 + (i - 1129)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1129 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1129).take (i - 1129))).length :=
      instructionPC_add Artifact.submissionArtifact 1129 (i - 1129)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1169 ≤ i) (hii : i ≤ 1208) :
    Artifact.submissionArtifact.instructionPC i =
      [1612,1615,1616,1617,1618,1619,1622,1623,1624,1625,1626,1630,1631,1632,1633,1634,1635,1638,1639,1642,1643,1645,1647,1649,1651,1653,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668][i - 1169]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1169 + (i - 1169)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1169 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1169).take (i - 1169))).length :=
      instructionPC_add Artifact.submissionArtifact 1169 (i - 1169)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1209 ≤ i) (hii : i ≤ 1248) :
    Artifact.submissionArtifact.instructionPC i =
      [1669,1670,1671,1672,1673,1676,1677,1680,1683,1686,1689,1692,1693,1694,1695,1696,1697,1699,1700,1701,1702,1704,1705,1706,1707,1710,1711,1712,1715,1718,1721,1724,1727,1728,1729,1731,1732,1735,1736,1737][i - 1209]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1209 + (i - 1209)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1209 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1209).take (i - 1209))).length :=
      instructionPC_add Artifact.submissionArtifact 1209 (i - 1209)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1249 ≤ i) (hii : i ≤ 1288) :
    Artifact.submissionArtifact.instructionPC i =
      [1738,1739,1742,1745,1748,1751,1754,1755,1756,1757,1760,1761,1763,1765,1767,1769,1770,1771,1772,1773,1774,1777,1778,1781,1782,1783,1784,1785,1786,1787,1789,1790,1793,1796,1799,1802,1805,1806,1807,1808][i - 1249]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1249 + (i - 1249)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1249 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1249).take (i - 1249))).length :=
      instructionPC_add Artifact.submissionArtifact 1249 (i - 1249)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1289 ≤ i) (hii : i ≤ 1328) :
    Artifact.submissionArtifact.instructionPC i =
      [1809,1810,1811,1814,1815,1818,1821,1824,1827,1830,1831,1832,1833,1835,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1852,1854,1855,1858,1859,1860,1863,1866,1869,1872,1875,1876,1877,1878,1879][i - 1289]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1289 + (i - 1289)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1289 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1289).take (i - 1289))).length :=
      instructionPC_add Artifact.submissionArtifact 1289 (i - 1289)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1329 ≤ i) (hii : i ≤ 1368) :
    Artifact.submissionArtifact.instructionPC i =
      [1880,1883,1884,1885,1886,1887,1888,1891,1892,1893,1894,1895,1896,1899,1900,1901,1902,1903,1904,1905,1906,1907,1910,1911,1912,1915,1916,1919,1920,1921,1922,1925,1926,1927,1929,1930,1931,1932,1935,1936][i - 1329]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1329 + (i - 1329)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1329 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1329).take (i - 1329))).length :=
      instructionPC_add Artifact.submissionArtifact 1329 (i - 1329)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1369 ≤ i) (hii : i ≤ 1407) :
    Artifact.submissionArtifact.instructionPC i =
      [1937,1938,1939,1940,1943,1944,1945,1947,1948,1949,1952,1953,1954,1955,1956,1958,1959,1960,1962,1963,1964,1965,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1977,1978,1983,1984,1985,1993,1994][i - 1369]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1369 + (i - 1369)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1369 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1369).take (i - 1369))).length :=
      instructionPC_add Artifact.submissionArtifact 1369 (i - 1369)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1408 ≤ i) (hii : i ≤ 1444) :
    Artifact.submissionArtifact.instructionPC i =
      [1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031][i - 1408]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1408 + (i - 1408)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1408 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1408).take (i - 1408))).length :=
      instructionPC_add Artifact.submissionArtifact 1408 (i - 1408)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1445 ≤ i) (hii : i ≤ 1487) :
    Artifact.submissionArtifact.instructionPC i =
      [2032,2033,2035,2036,2037,2038,2040,2041,2042,2043,2044,2045,2046,2049,2050,2051,2052,2053,2056,2057,2058,2059,2062,2063,2064,2067,2068,2071,2072,2073,2076,2077,2078,2079,2082,2083,2084,2085,2086,2087,2088,2089,2090][i - 1445]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1445 + (i - 1445)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1445 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1445).take (i - 1445))).length :=
      instructionPC_add Artifact.submissionArtifact 1445 (i - 1445)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1488 ≤ i) (hii : i ≤ 1528) :
    Artifact.submissionArtifact.instructionPC i =
      [2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2106,2107,2109,2110,2111,2114,2115,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137][i - 1488]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1488 + (i - 1488)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1488 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1488).take (i - 1488))).length :=
      instructionPC_add Artifact.submissionArtifact 1488 (i - 1488)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1529 ≤ i) (hii : i ≤ 1565) :
    Artifact.submissionArtifact.instructionPC i =
      [2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2153,2154,2156,2157,2158,2159,2160,2161,2163,2164,2165,2168,2169,2170,2173,2174,2175,2176,2177,2178,2179,2180,2181][i - 1529]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1529 + (i - 1529)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1529 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1529).take (i - 1529))).length :=
      instructionPC_add Artifact.submissionArtifact 1529 (i - 1529)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1566 ≤ i) (hii : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [2184,2185,2186,2187,2190,2191,2192,2195,2196,2197,2200,2201,2203,2204,2205,2206,2207,2208,2211,2212,2213,2214,2215,2218,2219,2220,2223,2224,2225,2226,2227,2229,2230,2231,2232,2233,2234,2236,2237,2238,2239][i - 1566]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1566 + (i - 1566)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1566 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1566).take (i - 1566))).length :=
      instructionPC_add Artifact.submissionArtifact 1566 (i - 1566)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1607 ≤ i) (hii : i ≤ 1649) :
    Artifact.submissionArtifact.instructionPC i =
      [2240,2241,2242,2243,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2274,2275,2276,2277,2279,2280,2281,2282,2283,2285,2286,2287][i - 1607]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1607 + (i - 1607)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1607).take (i - 1607))).length :=
      instructionPC_add Artifact.submissionArtifact 1607 (i - 1607)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1650 ≤ i) (hii : i ≤ 1689) :
    Artifact.submissionArtifact.instructionPC i =
      [2288,2291,2292,2293,2296,2297,2298,2299,2300,2303,2304,2305,2334,2335,2336,2337,2338,2339,2340,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2425][i - 1650]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1650 + (i - 1650)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1650 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1650).take (i - 1650))).length :=
      instructionPC_add Artifact.submissionArtifact 1650 (i - 1650)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1690 ≤ i) (hii : i ≤ 1710) :
    Artifact.submissionArtifact.instructionPC i =
      [2426,2427,2428,2461,2462,2465,2466,2467,2470,2471,2472,2473,2476,2477,2478,2481,2482,2483,2486,2487,2490][i - 1690]! := by
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

@[simp] theorem fastPC19 (i : Nat) (hi : 1711 ≤ i) (hii : i ≤ 1715) :
    Artifact.submissionArtifact.instructionPC i =
      [2491,2492,2493,2494,2495][i - 1711]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1711 + (i - 1711)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1711 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1711).take (i - 1711))).length :=
      instructionPC_add Artifact.submissionArtifact 1711 (i - 1711)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1716 ≤ i) (hii : i ≤ 1741) :
    Artifact.submissionArtifact.instructionPC i =
      [2496,2497,2500,2501,2502,2503,2506,2507,2508,2510,2511,2514,2515,2516,2517,2520,2521,2522,2523,2524,2525,2526,2530,2531,2532,2533][i - 1716]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1716 + (i - 1716)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1716 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1716).take (i - 1716))).length :=
      instructionPC_add Artifact.submissionArtifact 1716 (i - 1716)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1742 ≤ i) (hii : i ≤ 1754) :
    Artifact.submissionArtifact.instructionPC i =
      [2534,2535,2536,2537,2539,2540,2541,2544,2545,2547,2550,2551,2554][i - 1742]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1742 + (i - 1742)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1742 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1742).take (i - 1742))).length :=
      instructionPC_add Artifact.submissionArtifact 1742 (i - 1742)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1755 ≤ i) (hii : i ≤ 1789) :
    Artifact.submissionArtifact.instructionPC i =
      [2555,2556,2557,2560,2561,2562,2563,2564,2565,2566,2567,2570,2571,2573,2576,2577,2578,2579,2580,2582,2583,2584,2585,2587,2588,2589,2590,2592,2593,2594,2596,2597,2599,2600,2603][i - 1755]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1755 + (i - 1755)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1755 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1755).take (i - 1755))).length :=
      instructionPC_add Artifact.submissionArtifact 1755 (i - 1755)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1790 ≤ i) (hii : i ≤ 1804) :
    Artifact.submissionArtifact.instructionPC i =
      [2604,2605,2606,2609,2610,2613,2614,2617,2620,2621,2624,2627,2628,2629,2632][i - 1790]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1790 + (i - 1790)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1790 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1790).take (i - 1790))).length :=
      instructionPC_add Artifact.submissionArtifact 1790 (i - 1790)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl


/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2439 ≤ i) (hii : i ≤ 2491) :
    Artifact.submissionArtifact.instructionPC i =
      ([3365,3366,3367,3368,3369,3370,3371,3373,3374,3375,3376,3379,3380,3381,3383,3386,3387,3390,3393,3396,3399,3402,3403,3404,3407,3410,3413,3416,3419,3420,3421,3422,3424,3425,3427,3428,3429,3430,3432,3433,3434,3436,3437,3439,3440,3441,3442,3443,3446,3447,3448,3450,3453] : List Nat)[i - 2439]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1533 = true :=
  Artifact.isValidJumpDest_index 1130 (by rfl)

theorem jumpDest1555 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1555 = true :=
  Artifact.isValidJumpDest_index 1140 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  Artifact.isValidJumpDest_index 1147 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1586 = true :=
  Artifact.isValidJumpDest_index 1154 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1615 = true :=
  Artifact.isValidJumpDest_index 1170 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1631 = true :=
  Artifact.isValidJumpDest_index 1181 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1668 = true :=
  Artifact.isValidJumpDest_index 1208 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1693 = true :=
  Artifact.isValidJumpDest_index 1221 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1728 = true :=
  Artifact.isValidJumpDest_index 1242 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1736 = true :=
  Artifact.isValidJumpDest_index 1247 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1755 = true :=
  Artifact.isValidJumpDest_index 1256 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1756 = true :=
  Artifact.isValidJumpDest_index 1257 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1769 = true :=
  Artifact.isValidJumpDest_index 1264 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1789 = true :=
  Artifact.isValidJumpDest_index 1279 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1806 = true :=
  Artifact.isValidJumpDest_index 1286 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1831 = true :=
  Artifact.isValidJumpDest_index 1299 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1832 = true :=
  Artifact.isValidJumpDest_index 1300 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1850 = true :=
  Artifact.isValidJumpDest_index 1312 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1876 = true :=
  Artifact.isValidJumpDest_index 1325 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1886 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1892 = true :=
  Artifact.isValidJumpDest_index 1337 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1900 = true :=
  Artifact.isValidJumpDest_index 1343 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1911 = true :=
  Artifact.isValidJumpDest_index 1352 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1915 = true :=
  Artifact.isValidJumpDest_index 1354 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1926 = true :=
  Artifact.isValidJumpDest_index 1361 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1939 = true :=
  Artifact.isValidJumpDest_index 1371 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1974 = true :=
  Artifact.isValidJumpDest_index 1398 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1995 = true :=
  Artifact.isValidJumpDest_index 1408 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2119 = true :=
  Artifact.isValidJumpDest_index 1510 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2219 = true :=
  Artifact.isValidJumpDest_index 1590 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2252 = true :=
  Artifact.isValidJumpDest_index 1617 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2304 = true :=
  Artifact.isValidJumpDest_index 1660 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2337 = true :=
  Artifact.isValidJumpDest_index 1665 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2496 = true :=
  Artifact.isValidJumpDest_index 1716 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2507 = true :=
  Artifact.isValidJumpDest_index 1723 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2510 = true :=
  Artifact.isValidJumpDest_index 1725 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2521 = true :=
  Artifact.isValidJumpDest_index 1732 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2534 = true :=
  Artifact.isValidJumpDest_index 1742 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2555 = true :=
  Artifact.isValidJumpDest_index 1755 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2577 = true :=
  Artifact.isValidJumpDest_index 1770 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2604 = true :=
  Artifact.isValidJumpDest_index 1790 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2628 = true :=
  Artifact.isValidJumpDest_index 1802 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3330 = true :=
  Artifact.isValidJumpDest_index 2416 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3365 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3403 = true :=
  Artifact.isValidJumpDest_index 2461 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3420 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
