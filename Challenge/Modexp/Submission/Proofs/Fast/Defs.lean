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
    Artifact.submissionArtifact.instructionPC 973 = 1309 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1012 = 1365 := by
  calc
    Artifact.submissionArtifact.instructionPC 1012 =
        Artifact.submissionArtifact.instructionPC 973 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 973).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 973 39
    _ = 1365 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1052 = 1422 := by
  calc
    Artifact.submissionArtifact.instructionPC 1052 =
        Artifact.submissionArtifact.instructionPC 1012 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1012).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1012 40
    _ = 1422 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1092 = 1470 := by
  calc
    Artifact.submissionArtifact.instructionPC 1092 =
        Artifact.submissionArtifact.instructionPC 1052 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1052).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1052 40
    _ = 1470 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1132 = 1526 := by
  calc
    Artifact.submissionArtifact.instructionPC 1132 =
        Artifact.submissionArtifact.instructionPC 1092 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1092).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1092 40
    _ = 1526 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1172 = 1602 := by
  calc
    Artifact.submissionArtifact.instructionPC 1172 =
        Artifact.submissionArtifact.instructionPC 1132 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1132).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1132 40
    _ = 1602 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1212 = 1651 := by
  calc
    Artifact.submissionArtifact.instructionPC 1212 =
        Artifact.submissionArtifact.instructionPC 1172 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1172).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1172 40
    _ = 1651 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1251 = 1719 := by
  calc
    Artifact.submissionArtifact.instructionPC 1251 =
        Artifact.submissionArtifact.instructionPC 1212 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1212).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1212 39
    _ = 1719 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1290 = 1785 := by
  calc
    Artifact.submissionArtifact.instructionPC 1290 =
        Artifact.submissionArtifact.instructionPC 1251 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1251).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1251 39
    _ = 1785 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1330 = 1856 := by
  calc
    Artifact.submissionArtifact.instructionPC 1330 =
        Artifact.submissionArtifact.instructionPC 1290 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1290).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1290 40
    _ = 1856 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1370 = 1913 := by
  calc
    Artifact.submissionArtifact.instructionPC 1370 =
        Artifact.submissionArtifact.instructionPC 1330 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1330).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1330 40
    _ = 1913 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1409 = 1971 := by
  calc
    Artifact.submissionArtifact.instructionPC 1409 =
        Artifact.submissionArtifact.instructionPC 1370 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1370).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1370 39
    _ = 1971 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1445 = 2039 := by
  calc
    Artifact.submissionArtifact.instructionPC 1445 =
        Artifact.submissionArtifact.instructionPC 1409 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1409).take
              36)).length :=
      instructionPC_add Artifact.submissionArtifact 1409 36
    _ = 2039 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1485 = 2189 := by
  calc
    Artifact.submissionArtifact.instructionPC 1485 =
        Artifact.submissionArtifact.instructionPC 1445 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1445).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1445 40
    _ = 2189 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1525 = 2267 := by
  calc
    Artifact.submissionArtifact.instructionPC 1525 =
        Artifact.submissionArtifact.instructionPC 1485 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1485).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1485 40
    _ = 2267 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1559 = 2372 := by
  calc
    Artifact.submissionArtifact.instructionPC 1559 =
        Artifact.submissionArtifact.instructionPC 1525 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1525).take
              34)).length :=
      instructionPC_add Artifact.submissionArtifact 1525 34
    _ = 2372 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1599 = 2458 := by
  calc
    Artifact.submissionArtifact.instructionPC 1599 =
        Artifact.submissionArtifact.instructionPC 1559 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1559).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1559 40
    _ = 2458 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1637 = 2594 := by
  calc
    Artifact.submissionArtifact.instructionPC 1637 =
        Artifact.submissionArtifact.instructionPC 1599 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1599).take
              38)).length :=
      instructionPC_add Artifact.submissionArtifact 1599 38
    _ = 2594 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1674 = 2645 := by
  calc
    Artifact.submissionArtifact.instructionPC 1674 =
        Artifact.submissionArtifact.instructionPC 1637 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1637).take
              37)).length :=
      instructionPC_add Artifact.submissionArtifact 1637 37
    _ = 2645 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1713 = 2822 := by
  calc
    Artifact.submissionArtifact.instructionPC 1713 =
        Artifact.submissionArtifact.instructionPC 1674 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1674).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1674 39
    _ = 2822 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1716 = 2825 := by
  calc
    Artifact.submissionArtifact.instructionPC 1716 =
        Artifact.submissionArtifact.instructionPC 1713 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1713).take
              3)).length :=
      instructionPC_add Artifact.submissionArtifact 1713 3
    _ = 2825 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1742 = 2863 := by
  calc
    Artifact.submissionArtifact.instructionPC 1742 =
        Artifact.submissionArtifact.instructionPC 1716 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1716).take
              26)).length :=
      instructionPC_add Artifact.submissionArtifact 1716 26
    _ = 2863 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1755 = 2884 := by
  calc
    Artifact.submissionArtifact.instructionPC 1755 =
        Artifact.submissionArtifact.instructionPC 1742 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1742).take
              13)).length :=
      instructionPC_add Artifact.submissionArtifact 1742 13
    _ = 2884 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1790 = 2933 := by
  calc
    Artifact.submissionArtifact.instructionPC 1790 =
        Artifact.submissionArtifact.instructionPC 1755 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1755).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 1755 35
    _ = 2933 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 973 ≤ i) (hii : i ≤ 1011) :
    Artifact.submissionArtifact.instructionPC i =
      [1309,1310,1312,1313,1314,1316,1317,1320,1321,1323,1324,1325,1326,1327,1330,1331,1332,1335,1336,1337,1338,1341,1342,1343,1346,1347,1348,1350,1351,1353,1354,1355,1357,1358,1359,1360,1361,1363,1364][i - 973]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (973 + (i - 973)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 973 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 973).take (i - 973))).length :=
      instructionPC_add Artifact.submissionArtifact 973 (i - 973)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 1012 ≤ i) (hii : i ≤ 1051) :
    Artifact.submissionArtifact.instructionPC i =
      [1365,1366,1367,1369,1370,1371,1372,1373,1374,1375,1378,1379,1381,1382,1383,1384,1385,1386,1388,1389,1390,1393,1394,1395,1398,1399,1400,1403,1404,1405,1407,1408,1411,1412,1413,1415,1416,1417,1418,1421][i - 1012]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1012 + (i - 1012)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1012 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1012).take (i - 1012))).length :=
      instructionPC_add Artifact.submissionArtifact 1012 (i - 1012)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1052 ≤ i) (hii : i ≤ 1091) :
    Artifact.submissionArtifact.instructionPC i =
      [1422,1423,1426,1427,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1447,1448,1449,1450,1452,1453,1454,1455,1456,1457,1459,1460,1461,1462,1463,1464,1466,1467,1468,1469][i - 1052]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1052 + (i - 1052)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1052 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1052).take (i - 1052))).length :=
      instructionPC_add Artifact.submissionArtifact 1052 (i - 1052)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1092 ≤ i) (hii : i ≤ 1131) :
    Artifact.submissionArtifact.instructionPC i =
      [1470,1471,1473,1474,1475,1476,1477,1478,1480,1481,1482,1483,1484,1485,1487,1488,1489,1490,1491,1492,1494,1495,1496,1497,1498,1499,1501,1502,1503,1504,1505,1508,1509,1510,1511,1513,1516,1517,1520,1523][i - 1092]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1092 + (i - 1092)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1092 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1092).take (i - 1092))).length :=
      instructionPC_add Artifact.submissionArtifact 1092 (i - 1092)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1132 ≤ i) (hii : i ≤ 1171) :
    Artifact.submissionArtifact.instructionPC i =
      [1526,1527,1528,1531,1532,1535,1538,1539,1542,1545,1548,1549,1550,1553,1554,1557,1560,1561,1563,1564,1567,1570,1573,1576,1579,1580,1581,1582,1583,1584,1586,1587,1590,1591,1594,1595,1598,1599,1600,1601][i - 1132]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1132 + (i - 1132)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1132 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1132).take (i - 1132))).length :=
      instructionPC_add Artifact.submissionArtifact 1132 (i - 1132)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1172 ≤ i) (hii : i ≤ 1211) :
    Artifact.submissionArtifact.instructionPC i =
      [1602,1603,1604,1605,1606,1607,1610,1611,1612,1613,1614,1618,1619,1620,1621,1622,1623,1626,1627,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650][i - 1172]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1172 + (i - 1172)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1172 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1172).take (i - 1172))).length :=
      instructionPC_add Artifact.submissionArtifact 1172 (i - 1172)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1212 ≤ i) (hii : i ≤ 1250) :
    Artifact.submissionArtifact.instructionPC i =
      [1651,1652,1653,1654,1657,1658,1661,1664,1667,1670,1673,1674,1675,1676,1677,1678,1680,1681,1682,1683,1685,1686,1687,1688,1691,1692,1693,1696,1699,1702,1705,1708,1709,1710,1712,1713,1716,1717,1718][i - 1212]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1212 + (i - 1212)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1212 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1212).take (i - 1212))).length :=
      instructionPC_add Artifact.submissionArtifact 1212 (i - 1212)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1251 ≤ i) (hii : i ≤ 1289) :
    Artifact.submissionArtifact.instructionPC i =
      [1719,1720,1723,1726,1729,1732,1735,1736,1737,1738,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1753,1754,1757,1758,1759,1760,1761,1762,1763,1765,1766,1769,1772,1775,1778,1781,1782,1783,1784][i - 1251]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1251 + (i - 1251)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1251 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1251).take (i - 1251))).length :=
      instructionPC_add Artifact.submissionArtifact 1251 (i - 1251)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1290 ≤ i) (hii : i ≤ 1329) :
    Artifact.submissionArtifact.instructionPC i =
      [1785,1786,1787,1790,1791,1794,1797,1800,1803,1806,1807,1808,1809,1811,1812,1813,1816,1817,1818,1819,1821,1822,1825,1826,1827,1828,1830,1831,1834,1835,1836,1839,1842,1845,1848,1851,1852,1853,1854,1855][i - 1290]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1290 + (i - 1290)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1290 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1290).take (i - 1290))).length :=
      instructionPC_add Artifact.submissionArtifact 1290 (i - 1290)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1330 ≤ i) (hii : i ≤ 1369) :
    Artifact.submissionArtifact.instructionPC i =
      [1856,1859,1860,1861,1862,1863,1864,1867,1868,1869,1870,1871,1872,1875,1876,1877,1878,1879,1880,1881,1882,1883,1886,1887,1888,1891,1892,1895,1896,1897,1898,1901,1902,1903,1905,1906,1907,1908,1911,1912][i - 1330]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1330 + (i - 1330)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1330 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1330).take (i - 1330))).length :=
      instructionPC_add Artifact.submissionArtifact 1330 (i - 1330)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1370 ≤ i) (hii : i ≤ 1408) :
    Artifact.submissionArtifact.instructionPC i =
      [1913,1914,1915,1916,1919,1920,1921,1923,1924,1925,1928,1929,1930,1931,1932,1934,1935,1936,1938,1939,1940,1941,1942,1943,1944,1946,1947,1948,1949,1950,1951,1952,1953,1954,1959,1960,1961,1969,1970][i - 1370]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1370 + (i - 1370)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1370 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1370).take (i - 1370))).length :=
      instructionPC_add Artifact.submissionArtifact 1370 (i - 1370)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1409 ≤ i) (hii : i ≤ 1444) :
    Artifact.submissionArtifact.instructionPC i =
      [1971,1972,1973,1974,1975,1976,1977,1978,1979,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038][i - 1409]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1409 + (i - 1409)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1409 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1409).take (i - 1409))).length :=
      instructionPC_add Artifact.submissionArtifact 1409 (i - 1409)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1445 ≤ i) (hii : i ≤ 1484) :
    Artifact.submissionArtifact.instructionPC i =
      [2039,2040,2073,2074,2075,2108,2109,2110,2111,2112,2113,2116,2117,2118,2119,2120,2123,2124,2125,2126,2129,2130,2131,2134,2135,2138,2139,2140,2143,2144,2145,2146,2149,2150,2151,2152,2153,2154,2155,2188][i - 1445]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1445 + (i - 1445)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1445 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1445).take (i - 1445))).length :=
      instructionPC_add Artifact.submissionArtifact 1445 (i - 1445)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1485 ≤ i) (hii : i ≤ 1524) :
    Artifact.submissionArtifact.instructionPC i =
      [2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2204,2205,2207,2208,2209,2212,2213,2215,2216,2217,2218,2219,2220,2253,2254,2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266][i - 1485]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1485 + (i - 1485)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1485 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1485).take (i - 1485))).length :=
      instructionPC_add Artifact.submissionArtifact 1485 (i - 1485)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1525 ≤ i) (hii : i ≤ 1558) :
    Artifact.submissionArtifact.instructionPC i =
      [2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2282,2283,2316,2317,2318,2319,2320,2353,2354,2357,2358,2359,2362,2363,2364,2365,2366,2367,2368,2369][i - 1525]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1525 + (i - 1525)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1525 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1525).take (i - 1525))).length :=
      instructionPC_add Artifact.submissionArtifact 1525 (i - 1525)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1559 ≤ i) (hii : i ≤ 1598) :
    Artifact.submissionArtifact.instructionPC i =
      [2372,2373,2374,2375,2378,2379,2380,2383,2384,2385,2388,2389,2422,2423,2424,2425,2426,2429,2430,2431,2432,2433,2436,2437,2438,2441,2442,2443,2444,2445,2447,2448,2449,2450,2451,2452,2454,2455,2456,2457][i - 1559]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1559 + (i - 1559)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1559 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1559).take (i - 1559))).length :=
      instructionPC_add Artifact.submissionArtifact 1559 (i - 1559)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1599 ≤ i) (hii : i ≤ 1636) :
    Artifact.submissionArtifact.instructionPC i =
      [2458,2459,2460,2461,2464,2465,2466,2467,2468,2469,2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,2480,2481,2482,2483,2484,2485,2486,2487,2488,2521,2522,2523,2556,2557,2558,2559,2592,2593][i - 1599]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1599 + (i - 1599)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1599 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1599).take (i - 1599))).length :=
      instructionPC_add Artifact.submissionArtifact 1599 (i - 1599)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1637 ≤ i) (hii : i ≤ 1673) :
    Artifact.submissionArtifact.instructionPC i =
      [2594,2597,2598,2599,2602,2603,2604,2605,2606,2609,2610,2611,2614,2615,2618,2619,2620,2623,2624,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644][i - 1637]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1637 + (i - 1637)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1637 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1637).take (i - 1637))).length :=
      instructionPC_add Artifact.submissionArtifact 1637 (i - 1637)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1674 ≤ i) (hii : i ≤ 1712) :
    Artifact.submissionArtifact.instructionPC i =
      [2645,2646,2647,2648,2649,2650,2651,2652,2653,2654,2655,2656,2689,2690,2691,2724,2725,2726,2727,2760,2761,2762,2765,2766,2767,2770,2771,2772,2773,2774,2775,2778,2779,2780,2813,2814,2817,2818,2821][i - 1674]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1674 + (i - 1674)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1674 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1674).take (i - 1674))).length :=
      instructionPC_add Artifact.submissionArtifact 1674 (i - 1674)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1713 ≤ i) (hii : i ≤ 1715) :
    Artifact.submissionArtifact.instructionPC i =
      [2822,2823,2824][i - 1713]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1713 + (i - 1713)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1713 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1713).take (i - 1713))).length :=
      instructionPC_add Artifact.submissionArtifact 1713 (i - 1713)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1716 ≤ i) (hii : i ≤ 1741) :
    Artifact.submissionArtifact.instructionPC i =
      [2825,2826,2829,2830,2831,2832,2835,2836,2837,2839,2840,2843,2844,2845,2846,2849,2850,2851,2852,2853,2854,2855,2859,2860,2861,2862][i - 1716]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1716 + (i - 1716)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1716 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1716).take (i - 1716))).length :=
      instructionPC_add Artifact.submissionArtifact 1716 (i - 1716)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1742 ≤ i) (hii : i ≤ 1754) :
    Artifact.submissionArtifact.instructionPC i =
      [2863,2864,2865,2866,2868,2869,2870,2873,2874,2876,2879,2880,2883][i - 1742]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1742 + (i - 1742)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1742 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1742).take (i - 1742))).length :=
      instructionPC_add Artifact.submissionArtifact 1742 (i - 1742)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1755 ≤ i) (hii : i ≤ 1789) :
    Artifact.submissionArtifact.instructionPC i =
      [2884,2885,2886,2889,2890,2891,2892,2893,2894,2895,2896,2899,2900,2902,2905,2906,2907,2908,2909,2911,2912,2913,2914,2916,2917,2918,2919,2921,2922,2923,2925,2926,2928,2929,2932][i - 1755]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1755 + (i - 1755)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1755 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1755).take (i - 1755))).length :=
      instructionPC_add Artifact.submissionArtifact 1755 (i - 1755)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1790 ≤ i) (hii : i ≤ 1804) :
    Artifact.submissionArtifact.instructionPC i =
      [2933,2934,2935,2938,2939,2942,2943,2946,2949,2950,2953,2956,2957,2958,2961][i - 1790]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1790 + (i - 1790)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1790 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1790).take (i - 1790))).length :=
      instructionPC_add Artifact.submissionArtifact 1790 (i - 1790)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2179 ≤ i) (hii : i ≤ 2231) :
    Artifact.submissionArtifact.instructionPC i =
      [3568,3569,3570,3571,3572,3573,3574,3576,3577,3578,3579,3582,3583,3584,3586,3589,3590,3593,3596,3599,3602,3605,3606,3607,3610,3613,3616,3619,3622,3623,3624,3625,3627,3628,3630,3631,3632,3633,3635,3636,3637,3639,3640,3642,3643,3644,3645,3646,3649,3650,3651,3653,3656][i - 2179]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1192 = true :=
  Artifact.isValidJumpDest_index 896 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1527 = true :=
  Artifact.isValidJumpDest_index 1133 (by rfl)

theorem jumpDest1555 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1549 = true :=
  Artifact.isValidJumpDest_index 1143 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1563 = true :=
  Artifact.isValidJumpDest_index 1150 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1580 = true :=
  Artifact.isValidJumpDest_index 1157 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1603 = true :=
  Artifact.isValidJumpDest_index 1173 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1619 = true :=
  Artifact.isValidJumpDest_index 1184 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1650 = true :=
  Artifact.isValidJumpDest_index 1211 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1674 = true :=
  Artifact.isValidJumpDest_index 1223 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1709 = true :=
  Artifact.isValidJumpDest_index 1244 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1717 = true :=
  Artifact.isValidJumpDest_index 1249 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1736 = true :=
  Artifact.isValidJumpDest_index 1258 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1259 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1746 = true :=
  Artifact.isValidJumpDest_index 1266 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1765 = true :=
  Artifact.isValidJumpDest_index 1280 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1782 = true :=
  Artifact.isValidJumpDest_index 1287 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1807 = true :=
  Artifact.isValidJumpDest_index 1300 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1808 = true :=
  Artifact.isValidJumpDest_index 1301 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1826 = true :=
  Artifact.isValidJumpDest_index 1313 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1852 = true :=
  Artifact.isValidJumpDest_index 1326 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1862 = true :=
  Artifact.isValidJumpDest_index 1334 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1868 = true :=
  Artifact.isValidJumpDest_index 1338 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1876 = true :=
  Artifact.isValidJumpDest_index 1344 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1887 = true :=
  Artifact.isValidJumpDest_index 1353 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1891 = true :=
  Artifact.isValidJumpDest_index 1355 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1902 = true :=
  Artifact.isValidJumpDest_index 1362 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1915 = true :=
  Artifact.isValidJumpDest_index 1372 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1950 = true :=
  Artifact.isValidJumpDest_index 1399 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1971 = true :=
  Artifact.isValidJumpDest_index 1409 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2217 = true :=
  Artifact.isValidJumpDest_index 1507 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2437 = true :=
  Artifact.isValidJumpDest_index 1582 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2468 = true :=
  Artifact.isValidJumpDest_index 1607 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2610 = true :=
  Artifact.isValidJumpDest_index 1647 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2633 = true :=
  Artifact.isValidJumpDest_index 1662 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2825 = true :=
  Artifact.isValidJumpDest_index 1716 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2836 = true :=
  Artifact.isValidJumpDest_index 1723 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2839 = true :=
  Artifact.isValidJumpDest_index 1725 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2850 = true :=
  Artifact.isValidJumpDest_index 1732 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2863 = true :=
  Artifact.isValidJumpDest_index 1742 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2884 = true :=
  Artifact.isValidJumpDest_index 1755 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2906 = true :=
  Artifact.isValidJumpDest_index 1770 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2933 = true :=
  Artifact.isValidJumpDest_index 1790 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2957 = true :=
  Artifact.isValidJumpDest_index 1802 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3533 = true :=
  Artifact.isValidJumpDest_index 2156 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3568 = true :=
  Artifact.isValidJumpDest_index 2179 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3606 = true :=
  Artifact.isValidJumpDest_index 2201 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3623 = true :=
  Artifact.isValidJumpDest_index 2208 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
