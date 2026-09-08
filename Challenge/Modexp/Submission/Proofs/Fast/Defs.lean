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
    Artifact.submissionArtifact.instructionPC 1416 = 1995 := by
  calc
    Artifact.submissionArtifact.instructionPC 1416 =
        Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1377).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1377 39
    _ = 1995 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1452 = 2128 := by
  calc
    Artifact.submissionArtifact.instructionPC 1452 =
        Artifact.submissionArtifact.instructionPC 1416 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1416).take
              36)).length :=
      instructionPC_add Artifact.submissionArtifact 1416 36
    _ = 2128 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1492 = 2213 := by
  calc
    Artifact.submissionArtifact.instructionPC 1492 =
        Artifact.submissionArtifact.instructionPC 1452 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1452).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1452 40
    _ = 2213 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1532 = 2291 := by
  calc
    Artifact.submissionArtifact.instructionPC 1532 =
        Artifact.submissionArtifact.instructionPC 1492 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1492).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1492 40
    _ = 2291 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1567 = 2397 := by
  calc
    Artifact.submissionArtifact.instructionPC 1567 =
        Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1532).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 1532 35
    _ = 2397 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1607 = 2483 := by
  calc
    Artifact.submissionArtifact.instructionPC 1607 =
        Artifact.submissionArtifact.instructionPC 1567 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1567).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1567 40
    _ = 2483 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1647 = 2621 := by
  calc
    Artifact.submissionArtifact.instructionPC 1647 =
        Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1607).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1607 40
    _ = 2621 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1686 = 2675 := by
  calc
    Artifact.submissionArtifact.instructionPC 1686 =
        Artifact.submissionArtifact.instructionPC 1647 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1647).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1647 39
    _ = 2675 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1726 = 2853 := by
  calc
    Artifact.submissionArtifact.instructionPC 1726 =
        Artifact.submissionArtifact.instructionPC 1686 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1686).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1686 40
    _ = 2853 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1731 = 2858 := by
  calc
    Artifact.submissionArtifact.instructionPC 1731 =
        Artifact.submissionArtifact.instructionPC 1726 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1726).take
              5)).length :=
      instructionPC_add Artifact.submissionArtifact 1726 5
    _ = 2858 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1757 = 2896 := by
  calc
    Artifact.submissionArtifact.instructionPC 1757 =
        Artifact.submissionArtifact.instructionPC 1731 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1731).take
              26)).length :=
      instructionPC_add Artifact.submissionArtifact 1731 26
    _ = 2896 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1770 = 2917 := by
  calc
    Artifact.submissionArtifact.instructionPC 1770 =
        Artifact.submissionArtifact.instructionPC 1757 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1757).take
              13)).length :=
      instructionPC_add Artifact.submissionArtifact 1757 13
    _ = 2917 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1805 = 2966 := by
  calc
    Artifact.submissionArtifact.instructionPC 1805 =
        Artifact.submissionArtifact.instructionPC 1770 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1770).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 1770 35
    _ = 2966 := by
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
      [1738,1739,1742,1745,1748,1751,1754,1755,1756,1757,1760,1761,1763,1765,1767,1769,1770,1771,1772,1773,1774,1777,1778,1781,1782,1783,1784,1785,1786,1787,1789,1790,1793,1796,1799,1802,1805,1806,1807,1808][i - 1257]! := by
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

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1415) :
    Artifact.submissionArtifact.instructionPC i =
      [1937,1938,1939,1940,1943,1944,1945,1947,1948,1949,1952,1953,1954,1955,1956,1958,1959,1960,1962,1963,1964,1965,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1977,1978,1983,1984,1985,1993,1994][i - 1377]! := by
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

@[simp] theorem fastPC11 (i : Nat) (hi : 1416 ≤ i) (hii : i ≤ 1451) :
    Artifact.submissionArtifact.instructionPC i =
      [1995,1996,1999,2000,2033,2066,2068,2070,2072,2074,2076,2078,2080,2082,2084,2086,2088,2090,2092,2094,2096,2098,2100,2102,2104,2106,2108,2110,2112,2114,2116,2118,2120,2122,2124,2126][i - 1416]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1416 + (i - 1416)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1416 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1416).take
              (i - 1416))).length :=
      instructionPC_add Artifact.submissionArtifact 1416 (i - 1416)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1452 ≤ i) (hii : i ≤ 1491) :
    Artifact.submissionArtifact.instructionPC i =
      [2128,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2147,2148,2149,2150,2153,2154,2155,2158,2159,2162,2163,2164,2167,2168,2169,2170,2173,2174,2175,2176,2177,2178,2179,2212][i - 1452]! := by
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
      [2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2228,2229,2231,2232,2233,2236,2237,2239,2240,2241,2242,2243,2244,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290][i - 1492]! := by
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

@[simp] theorem fastPC14 (i : Nat) (hi : 1532 ≤ i) (hii : i ≤ 1566) :
    Artifact.submissionArtifact.instructionPC i =
      [2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2306,2307,2340,2341,2342,2343,2344,2377,2378,2381,2382,2383,2386,2387,2388,2389,2390,2391,2392,2393,2394][i - 1532]! := by
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

@[simp] theorem fastPC15 (i : Nat) (hi : 1567 ≤ i) (hii : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [2397,2398,2399,2400,2403,2404,2405,2408,2409,2410,2413,2414,2447,2448,2449,2450,2451,2454,2455,2456,2457,2458,2461,2462,2463,2466,2467,2468,2469,2470,2472,2473,2474,2475,2476,2477,2479,2480,2481,2482][i - 1567]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1567 + (i - 1567)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1567 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1567).take
              (i - 1567))).length :=
      instructionPC_add Artifact.submissionArtifact 1567 (i - 1567)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1607 ≤ i) (hii : i ≤ 1646) :
    Artifact.submissionArtifact.instructionPC i =
      [2483,2484,2485,2486,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2548,2549,2550,2583,2584,2585,2586,2619,2620][i - 1607]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1607 + (i - 1607)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1607).take
              (i - 1607))).length :=
      instructionPC_add Artifact.submissionArtifact 1607 (i - 1607)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1647 ≤ i) (hii : i ≤ 1685) :
    Artifact.submissionArtifact.instructionPC i =
      [2621,2624,2625,2626,2629,2630,2631,2632,2633,2636,2637,2638,2641,2642,2645,2646,2647,2650,2651,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674][i - 1647]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1647 + (i - 1647)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1647 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1647).take
              (i - 1647))).length :=
      instructionPC_add Artifact.submissionArtifact 1647 (i - 1647)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1686 ≤ i) (hii : i ≤ 1725) :
    Artifact.submissionArtifact.instructionPC i =
      [2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2720,2721,2722,2755,2756,2757,2758,2791,2792,2793,2796,2797,2798,2801,2802,2803,2804,2805,2806,2809,2810,2811,2844,2845,2848,2849,2852][i - 1686]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1686 + (i - 1686)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1686 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1686).take
              (i - 1686))).length :=
      instructionPC_add Artifact.submissionArtifact 1686 (i - 1686)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1726 ≤ i) (hii : i ≤ 1730) :
    Artifact.submissionArtifact.instructionPC i =
      [2853,2854,2855,2856,2857][i - 1726]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1726 + (i - 1726)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1726 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1726).take
              (i - 1726))).length :=
      instructionPC_add Artifact.submissionArtifact 1726 (i - 1726)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1731 ≤ i) (hii : i ≤ 1756) :
    Artifact.submissionArtifact.instructionPC i =
      [2858,2859,2862,2863,2864,2865,2868,2869,2870,2872,2873,2876,2877,2878,2879,2882,2883,2884,2885,2886,2887,2888,2892,2893,2894,2895][i - 1731]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1731 + (i - 1731)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1731 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1731).take
              (i - 1731))).length :=
      instructionPC_add Artifact.submissionArtifact 1731 (i - 1731)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1757 ≤ i) (hii : i ≤ 1769) :
    Artifact.submissionArtifact.instructionPC i =
      [2896,2897,2898,2899,2901,2902,2903,2906,2907,2909,2912,2913,2916][i - 1757]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1757 + (i - 1757)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1757 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1757).take
              (i - 1757))).length :=
      instructionPC_add Artifact.submissionArtifact 1757 (i - 1757)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1770 ≤ i) (hii : i ≤ 1804) :
    Artifact.submissionArtifact.instructionPC i =
      [2917,2918,2919,2922,2923,2924,2925,2926,2927,2928,2929,2932,2933,2935,2938,2939,2940,2941,2942,2944,2945,2946,2947,2949,2950,2951,2952,2954,2955,2956,2958,2959,2961,2962,2965][i - 1770]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1770 + (i - 1770)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1770 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1770).take
              (i - 1770))).length :=
      instructionPC_add Artifact.submissionArtifact 1770 (i - 1770)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1805 ≤ i) (hii : i ≤ 1819) :
    Artifact.submissionArtifact.instructionPC i =
      [2966,2967,2968,2971,2972,2975,2976,2979,2982,2983,2986,2989,2990,2991,2994][i - 1805]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1805 + (i - 1805)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1805 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1805).take
              (i - 1805))).length :=
      instructionPC_add Artifact.submissionArtifact 1805 (i - 1805)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2194 ≤ i) (hii : i ≤ 2246) :
    Artifact.submissionArtifact.instructionPC i =
      ([3601,3602,3603,3604,3605,3606,3607,3609,3610,3611,3612,3615,3616,3617,3619,3622,3623,3626,3629,3632,3635,3638,3639,3640,3643,3646,3649,3652,3655,3656,3657,3658,3660,3661,3663,3664,3665,3666,3668,3669,3670,3672,3673,3675,3676,3677,3678,3679,3682,3683,3684,3686,3689] : List Nat)[i - 2194]! := by
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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1995 = true :=
  Artifact.isValidJumpDest_index 1416 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2241 = true :=
  Artifact.isValidJumpDest_index 1514 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2462 = true :=
  Artifact.isValidJumpDest_index 1590 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2495 = true :=
  Artifact.isValidJumpDest_index 1617 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2637 = true :=
  Artifact.isValidJumpDest_index 1657 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2661 = true :=
  Artifact.isValidJumpDest_index 1672 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2858 = true :=
  Artifact.isValidJumpDest_index 1731 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2869 = true :=
  Artifact.isValidJumpDest_index 1738 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2872 = true :=
  Artifact.isValidJumpDest_index 1740 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2883 = true :=
  Artifact.isValidJumpDest_index 1747 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2896 = true :=
  Artifact.isValidJumpDest_index 1757 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2917 = true :=
  Artifact.isValidJumpDest_index 1770 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2939 = true :=
  Artifact.isValidJumpDest_index 1785 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2966 = true :=
  Artifact.isValidJumpDest_index 1805 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2990 = true :=
  Artifact.isValidJumpDest_index 1817 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3566 = true :=
  Artifact.isValidJumpDest_index 2171 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3601 = true :=
  Artifact.isValidJumpDest_index 2194 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3639 = true :=
  Artifact.isValidJumpDest_index 2216 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3656 = true :=
  Artifact.isValidJumpDest_index 2223 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
