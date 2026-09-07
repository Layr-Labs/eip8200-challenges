import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The appended Montgomery path occupies instruction indices 977..1736
(pc 1314..2855).  This module fixes the `Located` constructors, the
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
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 977).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 977 40
    _ = 1371 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1057 = 1428 := by
  calc
    Artifact.submissionArtifact.instructionPC 1057 =
        Artifact.submissionArtifact.instructionPC 1017 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1017).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1017 40
    _ = 1428 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1097 = 1476 := by
  calc
    Artifact.submissionArtifact.instructionPC 1097 =
        Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1057).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1057 40
    _ = 1476 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1137 = 1532 := by
  calc
    Artifact.submissionArtifact.instructionPC 1137 =
        Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1097).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1097 40
    _ = 1532 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1177 = 1612 := by
  calc
    Artifact.submissionArtifact.instructionPC 1177 =
        Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1137).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1137 40
    _ = 1612 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1217 = 1669 := by
  calc
    Artifact.submissionArtifact.instructionPC 1217 =
        Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1177).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1177 40
    _ = 1669 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1257 = 1738 := by
  calc
    Artifact.submissionArtifact.instructionPC 1257 =
        Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1217).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1217 40
    _ = 1738 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1297 = 1809 := by
  calc
    Artifact.submissionArtifact.instructionPC 1297 =
        Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1257).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1257 40
    _ = 1809 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1337 = 1880 := by
  calc
    Artifact.submissionArtifact.instructionPC 1337 =
        Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1297).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1297 40
    _ = 1880 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1377 = 1937 := by
  calc
    Artifact.submissionArtifact.instructionPC 1377 =
        Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1337).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1337 40
    _ = 1937 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1415 = 1987 := by
  calc
    Artifact.submissionArtifact.instructionPC 1415 =
        Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1377).take
              38)).length :=
      instructionPC_add Artifact.submissionArtifact 1377 38
    _ = 1987 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1452 = 2056 := by
  calc
    Artifact.submissionArtifact.instructionPC 1452 =
        Artifact.submissionArtifact.instructionPC 1415 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1415).take
              37)).length :=
      instructionPC_add Artifact.submissionArtifact 1415 37
    _ = 2056 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1492 = 2206 := by
  calc
    Artifact.submissionArtifact.instructionPC 1492 =
        Artifact.submissionArtifact.instructionPC 1452 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1452).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1452 40
    _ = 2206 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1532 = 2284 := by
  calc
    Artifact.submissionArtifact.instructionPC 1532 =
        Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1492).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1492 40
    _ = 2284 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1572 = 2395 := by
  calc
    Artifact.submissionArtifact.instructionPC 1572 =
        Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1532).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1532 40
    _ = 2395 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1612 = 2481 := by
  calc
    Artifact.submissionArtifact.instructionPC 1612 =
        Artifact.submissionArtifact.instructionPC 1572 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1572).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1572 40
    _ = 2481 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1652 = 2619 := by
  calc
    Artifact.submissionArtifact.instructionPC 1652 =
        Artifact.submissionArtifact.instructionPC 1612 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1612).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1612 40
    _ = 2619 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1692 = 2673 := by
  calc
    Artifact.submissionArtifact.instructionPC 1692 =
        Artifact.submissionArtifact.instructionPC 1652 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1652).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1652 40
    _ = 2673 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1732 = 2851 := by
  calc
    Artifact.submissionArtifact.instructionPC 1732 =
        Artifact.submissionArtifact.instructionPC 1692 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1692).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1692 40
    _ = 2851 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1737 = 2856 := by
  calc
    Artifact.submissionArtifact.instructionPC 1737 =
        Artifact.submissionArtifact.instructionPC 1732 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1732).take
              5)).length :=
      instructionPC_add Artifact.submissionArtifact 1732 5
    _ = 2856 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1763 = 2894 := by
  calc
    Artifact.submissionArtifact.instructionPC 1763 =
        Artifact.submissionArtifact.instructionPC 1737 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1737).take
              26)).length :=
      instructionPC_add Artifact.submissionArtifact 1737 26
    _ = 2894 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1776 = 2915 := by
  calc
    Artifact.submissionArtifact.instructionPC 1776 =
        Artifact.submissionArtifact.instructionPC 1763 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1763).take
              13)).length :=
      instructionPC_add Artifact.submissionArtifact 1763 13
    _ = 2915 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1811 = 2964 := by
  calc
    Artifact.submissionArtifact.instructionPC 1811 =
        Artifact.submissionArtifact.instructionPC 1776 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1776).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 1776 35
    _ = 2964 := by
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
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 977).take
              (i - 977))).length :=
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
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1017).take
              (i - 1017))).length :=
      instructionPC_add Artifact.submissionArtifact 1017 (i - 1017)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1096) :
    Artifact.submissionArtifact.instructionPC i =
      [1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1453,1454,1455,1456,1458,1459,1460,1461,1462,1463,1465,1466,1467,1468,1469,1470,1472,1473,1474,1475][i - 1057]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1057 + (i - 1057)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1057 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1057).take
              (i - 1057))).length :=
      instructionPC_add Artifact.submissionArtifact 1057 (i - 1057)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1097 ≤ i) (hii : i ≤ 1136) :
    Artifact.submissionArtifact.instructionPC i =
      [1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1505,1507,1508,1509,1510,1511,1514,1515,1516,1517,1519,1522,1523,1526,1529][i - 1097]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1097 + (i - 1097)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1097 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1097).take
              (i - 1097))).length :=
      instructionPC_add Artifact.submissionArtifact 1097 (i - 1097)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1137 ≤ i) (hii : i ≤ 1176) :
    Artifact.submissionArtifact.instructionPC i =
      [1532,1533,1534,1537,1538,1541,1544,1545,1548,1551,1554,1555,1556,1559,1560,1563,1566,1567,1569,1570,1573,1576,1579,1582,1585,1586,1587,1588,1589,1590,1592,1593,1596,1597,1600,1601,1604,1605,1606,1609][i - 1137]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1137 + (i - 1137)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1137 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1137).take
              (i - 1137))).length :=
      instructionPC_add Artifact.submissionArtifact 1137 (i - 1137)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1177 ≤ i) (hii : i ≤ 1216) :
    Artifact.submissionArtifact.instructionPC i =
      [1612,1615,1616,1617,1618,1619,1622,1623,1624,1625,1626,1630,1631,1632,1633,1634,1635,1638,1639,1642,1643,1645,1647,1649,1651,1653,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668][i - 1177]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1177 + (i - 1177)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1177 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1177).take
              (i - 1177))).length :=
      instructionPC_add Artifact.submissionArtifact 1177 (i - 1177)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1217 ≤ i) (hii : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1669,1670,1671,1672,1673,1676,1677,1680,1683,1686,1689,1692,1693,1694,1695,1696,1697,1699,1700,1701,1702,1704,1705,1706,1707,1710,1711,1712,1715,1718,1721,1724,1727,1728,1729,1731,1732,1735,1736,1737][i - 1217]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1217 + (i - 1217)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1217 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1217).take
              (i - 1217))).length :=
      instructionPC_add Artifact.submissionArtifact 1217 (i - 1217)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1257 ≤ i) (hii : i ≤ 1296) :
    Artifact.submissionArtifact.instructionPC i =
      [1738,1739,1742,1745,1748,1751,1754,1755,1756,1757,1760,1761,1764,1767,1768,1769,1770,1771,1772,1773,1774,1777,1778,1781,1782,1783,1784,1785,1786,1787,1789,1790,1793,1796,1799,1802,1805,1806,1807,1808][i - 1257]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1257 + (i - 1257)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1257).take
              (i - 1257))).length :=
      instructionPC_add Artifact.submissionArtifact 1257 (i - 1257)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1297 ≤ i) (hii : i ≤ 1336) :
    Artifact.submissionArtifact.instructionPC i =
      [1809,1810,1811,1814,1815,1818,1821,1824,1827,1830,1831,1832,1833,1835,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1852,1854,1855,1858,1859,1860,1863,1866,1869,1872,1875,1876,1877,1878,1879][i - 1297]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1297 + (i - 1297)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1297 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1297).take
              (i - 1297))).length :=
      instructionPC_add Artifact.submissionArtifact 1297 (i - 1297)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1337 ≤ i) (hii : i ≤ 1376) :
    Artifact.submissionArtifact.instructionPC i =
      [1880,1883,1884,1885,1886,1887,1888,1891,1892,1893,1894,1895,1896,1899,1900,1901,1902,1903,1904,1905,1906,1907,1910,1911,1912,1915,1916,1919,1920,1921,1922,1925,1926,1927,1929,1930,1931,1932,1935,1936][i - 1337]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1337 + (i - 1337)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1337 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1337).take
              (i - 1337))).length :=
      instructionPC_add Artifact.submissionArtifact 1337 (i - 1337)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1414) :
    Artifact.submissionArtifact.instructionPC i =
      [1937,1938,1939,1940,1943,1944,1945,1947,1948,1949,1952,1953,1954,1955,1956,1958,1959,1960,1962,1963,1964,1965,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1977,1978,1981,1982,1983,1986][i - 1377]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1377 + (i - 1377)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1377).take
              (i - 1377))).length :=
      instructionPC_add Artifact.submissionArtifact 1377 (i - 1377)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1415 ≤ i) (hii : i ≤ 1451) :
    Artifact.submissionArtifact.instructionPC i =
      [1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055][i - 1415]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1415 + (i - 1415)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1415 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1415).take
              (i - 1415))).length :=
      instructionPC_add Artifact.submissionArtifact 1415 (i - 1415)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1452 ≤ i) (hii : i ≤ 1491) :
    Artifact.submissionArtifact.instructionPC i =
      [2056,2057,2090,2091,2092,2125,2126,2127,2128,2129,2130,2133,2134,2135,2136,2137,2140,2141,2142,2143,2146,2147,2148,2151,2152,2155,2156,2157,2160,2161,2162,2163,2166,2167,2168,2169,2170,2171,2172,2205][i - 1452]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1452 + (i - 1452)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1452 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1452).take
              (i - 1452))).length :=
      instructionPC_add Artifact.submissionArtifact 1452 (i - 1452)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1492 ≤ i) (hii : i ≤ 1531) :
    Artifact.submissionArtifact.instructionPC i =
      [2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2221,2222,2224,2225,2226,2229,2230,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2275,2276,2277,2278,2279,2280,2281,2282,2283][i - 1492]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1492 + (i - 1492)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1492).take
              (i - 1492))).length :=
      instructionPC_add Artifact.submissionArtifact 1492 (i - 1492)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1532 ≤ i) (hii : i ≤ 1571) :
    Artifact.submissionArtifact.instructionPC i =
      [2284,2285,2286,2287,2288,2289,2290,2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2304,2305,2306,2339,2340,2341,2374,2375,2376,2379,2380,2381,2384,2385,2386,2387,2388,2389,2390,2391,2392][i - 1532]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1532 + (i - 1532)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1532).take
              (i - 1532))).length :=
      instructionPC_add Artifact.submissionArtifact 1532 (i - 1532)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1572 ≤ i) (hii : i ≤ 1611) :
    Artifact.submissionArtifact.instructionPC i =
      [2395,2396,2397,2398,2401,2402,2403,2406,2407,2408,2411,2412,2445,2446,2447,2448,2449,2452,2453,2454,2455,2456,2459,2460,2461,2464,2465,2466,2467,2468,2470,2471,2472,2473,2474,2475,2477,2478,2479,2480][i - 1572]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1572 + (i - 1572)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1572 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1572).take
              (i - 1572))).length :=
      instructionPC_add Artifact.submissionArtifact 1572 (i - 1572)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1612 ≤ i) (hii : i ≤ 1651) :
    Artifact.submissionArtifact.instructionPC i =
      [2481,2482,2483,2484,2487,2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2546,2547,2548,2581,2582,2583,2584,2617,2618][i - 1612]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1612 + (i - 1612)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1612 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1612).take
              (i - 1612))).length :=
      instructionPC_add Artifact.submissionArtifact 1612 (i - 1612)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1652 ≤ i) (hii : i ≤ 1691) :
    Artifact.submissionArtifact.instructionPC i =
      [2619,2622,2623,2624,2627,2628,2629,2630,2631,2634,2635,2636,2639,2640,2643,2644,2645,2648,2649,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672][i - 1652]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1652 + (i - 1652)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1652 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1652).take
              (i - 1652))).length :=
      instructionPC_add Artifact.submissionArtifact 1652 (i - 1652)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1692 ≤ i) (hii : i ≤ 1731) :
    Artifact.submissionArtifact.instructionPC i =
      [2673,2674,2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2718,2719,2720,2753,2754,2755,2756,2789,2790,2791,2794,2795,2796,2799,2800,2801,2802,2803,2804,2807,2808,2809,2842,2843,2846,2847,2850][i - 1692]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1692 + (i - 1692)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1692 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1692).take
              (i - 1692))).length :=
      instructionPC_add Artifact.submissionArtifact 1692 (i - 1692)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1732 ≤ i) (hii : i ≤ 1736) :
    Artifact.submissionArtifact.instructionPC i =
      [2851,2852,2853,2854,2855][i - 1732]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1732 + (i - 1732)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1732 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1732).take
              (i - 1732))).length :=
      instructionPC_add Artifact.submissionArtifact 1732 (i - 1732)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1737 ≤ i) (hii : i ≤ 1762) :
    Artifact.submissionArtifact.instructionPC i =
      [2856,2857,2860,2861,2862,2863,2866,2867,2868,2870,2871,2874,2875,2876,2877,2880,2881,2882,2883,2884,2885,2886,2890,2891,2892,2893][i - 1737]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1737 + (i - 1737)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1737 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1737).take
              (i - 1737))).length :=
      instructionPC_add Artifact.submissionArtifact 1737 (i - 1737)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1763 ≤ i) (hii : i ≤ 1775) :
    Artifact.submissionArtifact.instructionPC i =
      [2894,2895,2896,2897,2899,2900,2901,2904,2905,2907,2910,2911,2914][i - 1763]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1763 + (i - 1763)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1763 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1763).take
              (i - 1763))).length :=
      instructionPC_add Artifact.submissionArtifact 1763 (i - 1763)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1776 ≤ i) (hii : i ≤ 1810) :
    Artifact.submissionArtifact.instructionPC i =
      [2915,2916,2917,2920,2921,2922,2923,2924,2925,2926,2927,2930,2931,2933,2936,2937,2938,2939,2940,2942,2943,2944,2945,2947,2948,2949,2950,2952,2953,2954,2956,2957,2959,2960,2963][i - 1776]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1776 + (i - 1776)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1776 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1776).take
              (i - 1776))).length :=
      instructionPC_add Artifact.submissionArtifact 1776 (i - 1776)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1811 ≤ i) (hii : i ≤ 1825) :
    Artifact.submissionArtifact.instructionPC i =
      [2964,2965,2966,2969,2970,2973,2974,2977,2980,2981,2984,2987,2988,2989,2992][i - 1811]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1811 + (i - 1811)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1811 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1811).take
              (i - 1811))).length :=
      instructionPC_add Artifact.submissionArtifact 1811 (i - 1811)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl
/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 2356..2830 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat) (hi : 2356 ≤ i) (hii : i ≤ 2408) :
    Artifact.submissionArtifact.instructionPC i =
      [3599,3600,3601,3602,3603,3604,3605,3607,3608,3609,3610,3613,3614,3615,
       3617,3620,3621,3624,3627,3630,3633,3636,3637,3638,3641,3644,3647,3650,
       3653,3654,3655,3656,3658,3659,3661,3662,3663,3664,3666,3667,3668,3670,
       3671,3673,3674,3675,3676,3677,3680,3681,3682,3684,3687][i - 2356]! := by
  interval_cases i <;> decide

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1988 = true :=
  Artifact.isValidJumpDest_index 1416 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2234 = true :=
  Artifact.isValidJumpDest_index 1514 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2460 = true :=
  Artifact.isValidJumpDest_index 1595 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2493 = true :=
  Artifact.isValidJumpDest_index 1622 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2635 = true :=
  Artifact.isValidJumpDest_index 1662 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2659 = true :=
  Artifact.isValidJumpDest_index 1678 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2856 = true :=
  Artifact.isValidJumpDest_index 1737 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2867 = true :=
  Artifact.isValidJumpDest_index 1744 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2870 = true :=
  Artifact.isValidJumpDest_index 1746 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2881 = true :=
  Artifact.isValidJumpDest_index 1753 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2894 = true :=
  Artifact.isValidJumpDest_index 1763 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2915 = true :=
  Artifact.isValidJumpDest_index 1776 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2937 = true :=
  Artifact.isValidJumpDest_index 1791 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2964 = true :=
  Artifact.isValidJumpDest_index 1811 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2988 = true :=
  Artifact.isValidJumpDest_index 1823 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3564 = true :=
  Artifact.isValidJumpDest_index 2333 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3599 = true :=
  Artifact.isValidJumpDest_index 2356 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3637 = true :=
  Artifact.isValidJumpDest_index 2378 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3654 = true :=
  Artifact.isValidJumpDest_index 2385 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
