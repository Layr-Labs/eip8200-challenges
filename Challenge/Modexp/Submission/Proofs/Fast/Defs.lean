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
    Artifact.submissionArtifact.instructionPC 972 = 1309 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1011 = 1365 := by
  calc
    Artifact.submissionArtifact.instructionPC 1011 =
        Artifact.submissionArtifact.instructionPC 972 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 972).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 972 39
    _ = 1365 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1051 = 1422 := by
  calc
    Artifact.submissionArtifact.instructionPC 1051 =
        Artifact.submissionArtifact.instructionPC 1011 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1011).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1011 40
    _ = 1422 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1091 = 1470 := by
  calc
    Artifact.submissionArtifact.instructionPC 1091 =
        Artifact.submissionArtifact.instructionPC 1051 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1051).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1051 40
    _ = 1470 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1131 = 1526 := by
  calc
    Artifact.submissionArtifact.instructionPC 1131 =
        Artifact.submissionArtifact.instructionPC 1091 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1091).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1091 40
    _ = 1526 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1170 = 1605 := by
  calc
    Artifact.submissionArtifact.instructionPC 1170 =
        Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1131).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1131 39
    _ = 1605 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1210 = 1662 := by
  calc
    Artifact.submissionArtifact.instructionPC 1210 =
        Artifact.submissionArtifact.instructionPC 1170 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1170).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1170 40
    _ = 1662 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1249 = 1730 := by
  calc
    Artifact.submissionArtifact.instructionPC 1249 =
        Artifact.submissionArtifact.instructionPC 1210 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1210).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1210 39
    _ = 1730 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1288 = 1800 := by
  calc
    Artifact.submissionArtifact.instructionPC 1288 =
        Artifact.submissionArtifact.instructionPC 1249 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1249).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1249 39
    _ = 1800 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1328 = 1871 := by
  calc
    Artifact.submissionArtifact.instructionPC 1328 =
        Artifact.submissionArtifact.instructionPC 1288 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1288).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1288 40
    _ = 1871 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1368 = 1928 := by
  calc
    Artifact.submissionArtifact.instructionPC 1368 =
        Artifact.submissionArtifact.instructionPC 1328 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1328).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1328 40
    _ = 1928 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1407 = 1986 := by
  calc
    Artifact.submissionArtifact.instructionPC 1407 =
        Artifact.submissionArtifact.instructionPC 1368 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1368).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1368 39
    _ = 1986 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1444 = 2023 := by
  calc
    Artifact.submissionArtifact.instructionPC 1444 =
        Artifact.submissionArtifact.instructionPC 1407 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1407).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1407 37
    _ = 2023 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1487 = 2082 := by
  calc
    Artifact.submissionArtifact.instructionPC 1487 =
        Artifact.submissionArtifact.instructionPC 1444 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1444).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1444 43
    _ = 2082 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1528 = 2129 := by
  calc
    Artifact.submissionArtifact.instructionPC 1528 =
        Artifact.submissionArtifact.instructionPC 1487 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1487).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1487 41
    _ = 2129 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1564 = 2174 := by
  calc
    Artifact.submissionArtifact.instructionPC 1564 =
        Artifact.submissionArtifact.instructionPC 1528 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1528).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1528 36
    _ = 2174 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1605 = 2230 := by
  calc
    Artifact.submissionArtifact.instructionPC 1605 =
        Artifact.submissionArtifact.instructionPC 1564 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1564).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1564 41
    _ = 2230 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1646 = 2276 := by
  calc
    Artifact.submissionArtifact.instructionPC 1646 =
        Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1605 41
    _ = 2276 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1683 = 2327 := by
  calc
    Artifact.submissionArtifact.instructionPC 1683 =
        Artifact.submissionArtifact.instructionPC 1646 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1646).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1646 37
    _ = 2327 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1723 = 2475 := by
  calc
    Artifact.submissionArtifact.instructionPC 1723 =
        Artifact.submissionArtifact.instructionPC 1683 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1683).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1683 40
    _ = 2475 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1744 = 2505 := by
  calc
    Artifact.submissionArtifact.instructionPC 1744 =
        Artifact.submissionArtifact.instructionPC 1723 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1723).take 21)).length :=
      instructionPC_add Artifact.submissionArtifact 1723 21
    _ = 2505 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1751 = 2515 := by
  calc
    Artifact.submissionArtifact.instructionPC 1751 =
        Artifact.submissionArtifact.instructionPC 1744 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1744).take 7)).length :=
      instructionPC_add Artifact.submissionArtifact 1744 7
    _ = 2515 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1764 = 2536 := by
  calc
    Artifact.submissionArtifact.instructionPC 1764 =
        Artifact.submissionArtifact.instructionPC 1751 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1751).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1751 13
    _ = 2536 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1799 = 2585 := by
  calc
    Artifact.submissionArtifact.instructionPC 1799 =
        Artifact.submissionArtifact.instructionPC 1764 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1764).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1764 35
    _ = 2585 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 972 ≤ i) (hii : i ≤ 1010) :
    Artifact.submissionArtifact.instructionPC i =
      [1309,1310,1312,1313,1314,1316,1317,1320,1321,1323,1324,1325,1326,1327,1330,1331,1332,1335,1336,1337,1338,1341,1342,1343,1346,1347,1348,1350,1351,1353,1354,1355,1357,1358,1359,1360,1361,1363,1364][i - 972]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (972 + (i - 972)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 972 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 972).take (i - 972))).length :=
      instructionPC_add Artifact.submissionArtifact 972 (i - 972)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1011 ≤ i) (hii : i ≤ 1050) :
    Artifact.submissionArtifact.instructionPC i =
      [1365,1366,1367,1369,1370,1371,1372,1373,1374,1375,1378,1379,1381,1382,1383,1384,1385,1386,1388,1389,1390,1393,1394,1395,1398,1399,1400,1403,1404,1405,1407,1408,1411,1412,1413,1415,1416,1417,1418,1421][i - 1011]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1011 + (i - 1011)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1011 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1011).take (i - 1011))).length :=
      instructionPC_add Artifact.submissionArtifact 1011 (i - 1011)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1051 ≤ i) (hii : i ≤ 1090) :
    Artifact.submissionArtifact.instructionPC i =
      [1422,1423,1426,1427,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1447,1448,1449,1450,1452,1453,1454,1455,1456,1457,1459,1460,1461,1462,1463,1464,1466,1467,1468,1469][i - 1051]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1051 + (i - 1051)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1051 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1051).take (i - 1051))).length :=
      instructionPC_add Artifact.submissionArtifact 1051 (i - 1051)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1091 ≤ i) (hii : i ≤ 1130) :
    Artifact.submissionArtifact.instructionPC i =
      [1470,1471,1473,1474,1475,1476,1477,1478,1480,1481,1482,1483,1484,1485,1487,1488,1489,1490,1491,1492,1494,1495,1496,1497,1498,1499,1501,1502,1503,1504,1505,1508,1509,1510,1511,1513,1516,1517,1520,1523][i - 1091]! := by
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

@[simp] theorem fastPC4 (i : Nat) (hi : 1131 ≤ i) (hii : i ≤ 1169) :
    Artifact.submissionArtifact.instructionPC i =
      [1526,1527,1528,1531,1532,1535,1538,1539,1542,1545,1548,1549,1552,1553,1556,1559,1560,1562,1563,1566,1569,1572,1575,1578,1579,1580,1581,1582,1583,1585,1586,1589,1590,1593,1594,1597,1598,1599,1602][i - 1131]! := by
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

@[simp] theorem fastPC5 (i : Nat) (hi : 1170 ≤ i) (hii : i ≤ 1209) :
    Artifact.submissionArtifact.instructionPC i =
      [1605,1608,1609,1610,1611,1612,1615,1616,1617,1618,1619,1623,1624,1625,1626,1627,1628,1631,1632,1635,1636,1638,1640,1642,1644,1646,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661][i - 1170]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1170 + (i - 1170)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1170 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1170).take (i - 1170))).length :=
      instructionPC_add Artifact.submissionArtifact 1170 (i - 1170)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1210 ≤ i) (hii : i ≤ 1248) :
    Artifact.submissionArtifact.instructionPC i =
      [1662,1663,1664,1665,1668,1669,1672,1675,1678,1681,1684,1685,1686,1687,1688,1689,1691,1692,1693,1694,1696,1697,1698,1699,1702,1703,1704,1707,1710,1713,1716,1719,1720,1721,1723,1724,1727,1728,1729][i - 1210]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1210 + (i - 1210)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1210 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1210).take (i - 1210))).length :=
      instructionPC_add Artifact.submissionArtifact 1210 (i - 1210)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1249 ≤ i) (hii : i ≤ 1287) :
    Artifact.submissionArtifact.instructionPC i =
      [1730,1731,1734,1737,1740,1743,1746,1747,1748,1749,1752,1753,1755,1757,1759,1761,1762,1763,1764,1765,1768,1769,1772,1773,1774,1775,1776,1777,1778,1780,1781,1784,1787,1790,1793,1796,1797,1798,1799][i - 1249]! := by
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

@[simp] theorem fastPC8 (i : Nat) (hi : 1288 ≤ i) (hii : i ≤ 1327) :
    Artifact.submissionArtifact.instructionPC i =
      [1800,1801,1802,1805,1806,1809,1812,1815,1818,1821,1822,1823,1824,1826,1827,1828,1831,1832,1833,1834,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1854,1857,1860,1863,1866,1867,1868,1869,1870][i - 1288]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1288 + (i - 1288)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1288 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1288).take (i - 1288))).length :=
      instructionPC_add Artifact.submissionArtifact 1288 (i - 1288)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1328 ≤ i) (hii : i ≤ 1367) :
    Artifact.submissionArtifact.instructionPC i =
      [1871,1874,1875,1876,1877,1878,1879,1882,1883,1884,1885,1886,1887,1890,1891,1892,1893,1894,1895,1896,1897,1898,1901,1902,1903,1906,1907,1910,1911,1912,1913,1916,1917,1918,1920,1921,1922,1923,1926,1927][i - 1328]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1328 + (i - 1328)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1328 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1328).take (i - 1328))).length :=
      instructionPC_add Artifact.submissionArtifact 1328 (i - 1328)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1368 ≤ i) (hii : i ≤ 1406) :
    Artifact.submissionArtifact.instructionPC i =
      [1928,1929,1930,1931,1934,1935,1936,1938,1939,1940,1943,1944,1945,1946,1947,1949,1950,1951,1953,1954,1955,1956,1957,1958,1959,1961,1962,1963,1964,1965,1966,1967,1968,1969,1974,1975,1976,1984,1985][i - 1368]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1368 + (i - 1368)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1368 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1368).take (i - 1368))).length :=
      instructionPC_add Artifact.submissionArtifact 1368 (i - 1368)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1407 ≤ i) (hii : i ≤ 1443) :
    Artifact.submissionArtifact.instructionPC i =
      [1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022][i - 1407]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1407 + (i - 1407)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1407 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1407).take (i - 1407))).length :=
      instructionPC_add Artifact.submissionArtifact 1407 (i - 1407)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1444 ≤ i) (hii : i ≤ 1486) :
    Artifact.submissionArtifact.instructionPC i =
      [2023,2024,2026,2027,2028,2029,2031,2032,2033,2034,2035,2036,2037,2040,2041,2042,2043,2044,2047,2048,2049,2050,2053,2054,2055,2058,2059,2062,2063,2064,2067,2068,2069,2070,2073,2074,2075,2076,2077,2078,2079,2080,2081][i - 1444]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1444 + (i - 1444)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1444 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1444).take (i - 1444))).length :=
      instructionPC_add Artifact.submissionArtifact 1444 (i - 1444)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1487 ≤ i) (hii : i ≤ 1527) :
    Artifact.submissionArtifact.instructionPC i =
      [2082,2083,2084,2085,2086,2087,2088,2089,2090,2091,2092,2093,2094,2097,2098,2100,2101,2102,2105,2106,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128][i - 1487]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1487 + (i - 1487)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1487 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1487).take (i - 1487))).length :=
      instructionPC_add Artifact.submissionArtifact 1487 (i - 1487)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1528 ≤ i) (hii : i ≤ 1563) :
    Artifact.submissionArtifact.instructionPC i =
      [2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2144,2145,2147,2148,2149,2150,2151,2152,2154,2155,2156,2159,2160,2161,2164,2165,2166,2167,2168,2169,2170,2171][i - 1528]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1528 + (i - 1528)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1528 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1528).take (i - 1528))).length :=
      instructionPC_add Artifact.submissionArtifact 1528 (i - 1528)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1564 ≤ i) (hii : i ≤ 1604) :
    Artifact.submissionArtifact.instructionPC i =
      [2174,2175,2176,2177,2180,2181,2182,2185,2186,2187,2190,2191,2193,2194,2195,2196,2197,2198,2201,2202,2203,2204,2205,2208,2209,2210,2213,2214,2215,2216,2217,2219,2220,2221,2222,2223,2224,2226,2227,2228,2229][i - 1564]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1564 + (i - 1564)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1564 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1564).take (i - 1564))).length :=
      instructionPC_add Artifact.submissionArtifact 1564 (i - 1564)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1605 ≤ i) (hii : i ≤ 1645) :
    Artifact.submissionArtifact.instructionPC i =
      [2230,2231,2232,2233,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,2259,2260,2262,2263,2264,2265,2267,2268,2269,2270,2271,2273,2274,2275][i - 1605]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1605 + (i - 1605)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take (i - 1605))).length :=
      instructionPC_add Artifact.submissionArtifact 1605 (i - 1605)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1646 ≤ i) (hii : i ≤ 1682) :
    Artifact.submissionArtifact.instructionPC i =
      [2276,2279,2280,2281,2284,2285,2286,2287,2288,2291,2292,2293,2296,2297,2300,2301,2302,2305,2306,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2325,2326][i - 1646]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1646 + (i - 1646)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1646 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1646).take (i - 1646))).length :=
      instructionPC_add Artifact.submissionArtifact 1646 (i - 1646)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1683 ≤ i) (hii : i ≤ 1722) :
    Artifact.submissionArtifact.instructionPC i =
      [2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2371,2372,2373,2406,2407,2408,2409,2442,2443,2444,2447,2448,2449,2452,2453,2454,2455,2456,2457,2460,2461,2462,2465,2466,2467,2470,2471,2474][i - 1683]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1683 + (i - 1683)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1683 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1683).take (i - 1683))).length :=
      instructionPC_add Artifact.submissionArtifact 1683 (i - 1683)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1723 ≤ i) (hii : i ≤ 1725) :
    Artifact.submissionArtifact.instructionPC i =
      [2475,2476,2477][i - 1723]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1723 + (i - 1723)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1723 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1723).take (i - 1723))).length :=
      instructionPC_add Artifact.submissionArtifact 1723 (i - 1723)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1726 ≤ i) (hii : i ≤ 1750) :
    Artifact.submissionArtifact.instructionPC i =
      [2478,2481,2482,2483,2484,2487,2488,2489,2491,2492,2495,2496,2497,2498,2501,2502,2503,2504,2505,2506,2507,2511,2512,2513,2514][i - 1726]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1723 + (i - 1723)) := by
      rw [Nat.add_sub_of_le (by omega : 1723 ≤ i)]
    _ = Artifact.submissionArtifact.instructionPC 1723 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1723).take (i - 1723))).length :=
      instructionPC_add Artifact.submissionArtifact 1723 (i - 1723)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1751 ≤ i) (hii : i ≤ 1763) :
    Artifact.submissionArtifact.instructionPC i =
      [2515,2516,2517,2518,2520,2521,2522,2525,2526,2528,2531,2532,2535][i - 1751]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1751 + (i - 1751)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1751 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1751).take (i - 1751))).length :=
      instructionPC_add Artifact.submissionArtifact 1751 (i - 1751)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1764 ≤ i) (hii : i ≤ 1798) :
    Artifact.submissionArtifact.instructionPC i =
      [2536,2537,2538,2541,2542,2543,2544,2545,2546,2547,2548,2551,2552,2554,2557,2558,2559,2560,2561,2563,2564,2565,2566,2568,2569,2570,2571,2573,2574,2575,2577,2578,2580,2581,2584][i - 1764]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1764 + (i - 1764)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1764 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1764).take (i - 1764))).length :=
      instructionPC_add Artifact.submissionArtifact 1764 (i - 1764)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1799 ≤ i) (hii : i ≤ 1812) :
    Artifact.submissionArtifact.instructionPC i =
      [2585,2586,2587,2590,2591,2594,2595,2598,2601,2602,2605,2608,2609,2612][i - 1799]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1799 + (i - 1799)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1799 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1799).take (i - 1799))).length :=
      instructionPC_add Artifact.submissionArtifact 1799 (i - 1799)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl
/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2203 ≤ i) (hii : i ≤ 2254) :
    Artifact.submissionArtifact.instructionPC i =
      [3089,3090,3091,3092,3093,3094,3095,3097,3098,3099,3100,3103,3104,3105,3107,3110,3111,3114,3117,3120,3123,3126,3127,3130,3133,3136,3139,3142,3143,3144,3145,3147,3148,3150,3151,3152,3153,3155,3156,3157,3159,3160,3162,3163,3164,3165,3166,3169,3170,3171,3173,3176][i - 2203]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1192 = true :=
  Artifact.isValidJumpDest_index 895 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1527 = true :=
  Artifact.isValidJumpDest_index 1132 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1562 = true :=
  Artifact.isValidJumpDest_index 1148 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1579 = true :=
  Artifact.isValidJumpDest_index 1155 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1608 = true :=
  Artifact.isValidJumpDest_index 1171 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1624 = true :=
  Artifact.isValidJumpDest_index 1182 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1661 = true :=
  Artifact.isValidJumpDest_index 1209 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1685 = true :=
  Artifact.isValidJumpDest_index 1221 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1720 = true :=
  Artifact.isValidJumpDest_index 1242 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1728 = true :=
  Artifact.isValidJumpDest_index 1247 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1747 = true :=
  Artifact.isValidJumpDest_index 1256 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1748 = true :=
  Artifact.isValidJumpDest_index 1257 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1761 = true :=
  Artifact.isValidJumpDest_index 1264 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1780 = true :=
  Artifact.isValidJumpDest_index 1278 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1797 = true :=
  Artifact.isValidJumpDest_index 1285 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1822 = true :=
  Artifact.isValidJumpDest_index 1298 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1823 = true :=
  Artifact.isValidJumpDest_index 1299 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1841 = true :=
  Artifact.isValidJumpDest_index 1311 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1867 = true :=
  Artifact.isValidJumpDest_index 1324 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1877 = true :=
  Artifact.isValidJumpDest_index 1332 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1883 = true :=
  Artifact.isValidJumpDest_index 1336 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1891 = true :=
  Artifact.isValidJumpDest_index 1342 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1902 = true :=
  Artifact.isValidJumpDest_index 1351 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1906 = true :=
  Artifact.isValidJumpDest_index 1353 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1917 = true :=
  Artifact.isValidJumpDest_index 1360 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1930 = true :=
  Artifact.isValidJumpDest_index 1370 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1965 = true :=
  Artifact.isValidJumpDest_index 1397 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1986 = true :=
  Artifact.isValidJumpDest_index 1407 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2110 = true :=
  Artifact.isValidJumpDest_index 1509 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2209 = true :=
  Artifact.isValidJumpDest_index 1588 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2240 = true :=
  Artifact.isValidJumpDest_index 1613 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2292 = true :=
  Artifact.isValidJumpDest_index 1656 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2315 = true :=
  Artifact.isValidJumpDest_index 1671 (by rfl)


theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2488 = true :=
  Artifact.isValidJumpDest_index 1732 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2491 = true :=
  Artifact.isValidJumpDest_index 1734 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2502 = true :=
  Artifact.isValidJumpDest_index 1741 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2515 = true :=
  Artifact.isValidJumpDest_index 1751 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2536 = true :=
  Artifact.isValidJumpDest_index 1764 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2558 = true :=
  Artifact.isValidJumpDest_index 1779 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2585 = true :=
  Artifact.isValidJumpDest_index 1799 (by rfl)


theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3054 = true :=
  Artifact.isValidJumpDest_index 2180 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3089 = true :=
  Artifact.isValidJumpDest_index 2203 (by rfl)


theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3143 = true :=
  Artifact.isValidJumpDest_index 2231 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
