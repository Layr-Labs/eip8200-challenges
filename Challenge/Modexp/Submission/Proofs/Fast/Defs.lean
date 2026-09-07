import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The appended Montgomery path occupies instruction indices 977..1855
(pc 1314..3028), with later helper blocks covered by the tables below.  This
module fixes the `Located` constructors, the program-counter table and the
jump-destination facts those blocks need.
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
    Artifact.submissionArtifact.instructionPC 1417 = 1987 := by
  calc
    Artifact.submissionArtifact.instructionPC 1417 =
        Artifact.submissionArtifact.instructionPC 1377 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1377).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1377 40
    _ = 1987 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1457 = 2066 := by
  calc
    Artifact.submissionArtifact.instructionPC 1457 =
        Artifact.submissionArtifact.instructionPC 1417 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1417).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1417 40
    _ = 2066 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1497 = 2180 := by
  calc
    Artifact.submissionArtifact.instructionPC 1497 =
        Artifact.submissionArtifact.instructionPC 1457 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1457).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1457 40
    _ = 2180 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1537 = 2261 := by
  calc
    Artifact.submissionArtifact.instructionPC 1537 =
        Artifact.submissionArtifact.instructionPC 1497 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1497).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1497 40
    _ = 2261 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1577 = 2336 := by
  calc
    Artifact.submissionArtifact.instructionPC 1577 =
        Artifact.submissionArtifact.instructionPC 1537 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1537).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1537 40
    _ = 2336 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1617 = 2486 := by
  calc
    Artifact.submissionArtifact.instructionPC 1617 =
        Artifact.submissionArtifact.instructionPC 1577 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1577).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1577 40
    _ = 2486 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1657 = 2534 := by
  calc
    Artifact.submissionArtifact.instructionPC 1657 =
        Artifact.submissionArtifact.instructionPC 1617 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1617).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1617 40
    _ = 2534 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1697 = 2680 := by
  calc
    Artifact.submissionArtifact.instructionPC 1697 =
        Artifact.submissionArtifact.instructionPC 1657 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1657).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1657 40
    _ = 2680 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1737 = 2756 := by
  calc
    Artifact.submissionArtifact.instructionPC 1737 =
        Artifact.submissionArtifact.instructionPC 1697 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1697).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1697 40
    _ = 2756 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1767 = 2892 := by
  calc
    Artifact.submissionArtifact.instructionPC 1767 =
        Artifact.submissionArtifact.instructionPC 1737 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1737).take
              30)).length :=
      instructionPC_add Artifact.submissionArtifact 1737 30
    _ = 2892 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1793 = 2930 := by
  calc
    Artifact.submissionArtifact.instructionPC 1793 =
        Artifact.submissionArtifact.instructionPC 1767 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1767).take
              26)).length :=
      instructionPC_add Artifact.submissionArtifact 1767 26
    _ = 2930 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1806 = 2951 := by
  calc
    Artifact.submissionArtifact.instructionPC 1806 =
        Artifact.submissionArtifact.instructionPC 1793 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1793).take
              13)).length :=
      instructionPC_add Artifact.submissionArtifact 1793 13
    _ = 2951 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1841 = 3000 := by
  calc
    Artifact.submissionArtifact.instructionPC 1841 =
        Artifact.submissionArtifact.instructionPC 1806 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1806).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 1806 35
    _ = 3000 := by
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

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1416) :
    Artifact.submissionArtifact.instructionPC i =
      [1937,1938,1939,1940,1943,1944,1945,1946,1947,1948,1951,1952,1953,1955,1956,1957,1960,1961,1962,1963,1964,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1978,1979,1980,1981,1982,1983,1984,1985,1986][i - 1377]! := by
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

@[simp] theorem fastPC11 (i : Nat) (hi : 1417 ≤ i) (hii : i ≤ 1456) :
    Artifact.submissionArtifact.instructionPC i =
      [1987,1988,1991,1992,1993,1994,1997,1998,1999,2001,2002,2003,2004,2005,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065][i - 1417]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1417 + (i - 1417)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1417 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1417).take
              (i - 1417))).length :=
      instructionPC_add Artifact.submissionArtifact 1417 (i - 1417)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1457 ≤ i) (hii : i ≤ 1496) :
    Artifact.submissionArtifact.instructionPC i =
      [2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2111,2112,2113,2146,2147,2148,2149,2150,2151,2154,2155,2156,2157,2158,2159,2162,2163,2164,2165,2168,2169,2170,2173,2174,2175,2176,2179][i - 1457]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1457 + (i - 1457)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1457 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1457).take
              (i - 1457))).length :=
      instructionPC_add Artifact.submissionArtifact 1457 (i - 1457)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1497 ≤ i) (hii : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2180,2181,2182,2185,2186,2187,2188,2189,2190,2191,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2240,2241,2242,2245,2246,2248,2249,2250,2251,2254,2255,2256,2258,2259,2260][i - 1497]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1497 + (i - 1497)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1497 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1497).take
              (i - 1497))).length :=
      instructionPC_add Artifact.submissionArtifact 1497 (i - 1497)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1537 ≤ i) (hii : i ≤ 1576) :
    Artifact.submissionArtifact.instructionPC i =
      [2261,2262,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334][i - 1537]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1537 + (i - 1537)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1537 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1537).take
              (i - 1537))).length :=
      instructionPC_add Artifact.submissionArtifact 1537 (i - 1537)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1577 ≤ i) (hii : i ≤ 1616) :
    Artifact.submissionArtifact.instructionPC i =
      [2336,2337,2338,2371,2372,2373,2406,2407,2408,2411,2412,2413,2416,2417,2418,2419,2420,2421,2422,2423,2424,2425,2428,2429,2430,2431,2434,2435,2436,2439,2440,2441,2444,2445,2478,2479,2480,2481,2482,2485][i - 1577]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1577 + (i - 1577)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1577 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1577).take
              (i - 1577))).length :=
      instructionPC_add Artifact.submissionArtifact 1577 (i - 1577)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1617 ≤ i) (hii : i ≤ 1656) :
    Artifact.submissionArtifact.instructionPC i =
      [2486,2487,2488,2489,2490,2491,2492,2495,2496,2497,2500,2501,2502,2503,2504,2506,2507,2508,2509,2510,2511,2513,2514,2515,2516,2517,2518,2519,2520,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533][i - 1617]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1617 + (i - 1617)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1617 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1617).take
              (i - 1617))).length :=
      instructionPC_add Artifact.submissionArtifact 1617 (i - 1617)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1657 ≤ i) (hii : i ≤ 1696) :
    Artifact.submissionArtifact.instructionPC i =
      [2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549,2582,2583,2584,2617,2618,2619,2620,2653,2654,2655,2658,2659,2660,2663,2664,2665,2666,2667,2670,2671,2672,2675,2676,2679][i - 1657]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1657 + (i - 1657)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1657 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1657).take
              (i - 1657))).length :=
      instructionPC_add Artifact.submissionArtifact 1657 (i - 1657)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1697 ≤ i) (hii : i ≤ 1736) :
    Artifact.submissionArtifact.instructionPC i =
      [2680,2681,2684,2685,2688,2689,2690,2691,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712,2713,2714,2715,2716,2717,2718,2719,2720,2721,2754,2755][i - 1697]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1697 + (i - 1697)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1697 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1697).take
              (i - 1697))).length :=
      instructionPC_add Artifact.submissionArtifact 1697 (i - 1697)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1737 ≤ i) (hii : i ≤ 1766) :
    Artifact.submissionArtifact.instructionPC i =
      [2756,2789,2790,2791,2792,2825,2826,2827,2830,2831,2832,2835,2836,2837,2838,2839,2840,2843,2844,2845,2878,2879,2882,2883,2886,2887,2888,2889,2890,2891][i - 1737]! := by
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
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1767 ≤ i) (hii : i ≤ 1792) :
    Artifact.submissionArtifact.instructionPC i =
      [2892,2893,2896,2897,2898,2899,2902,2903,2904,2906,2907,2910,2911,2912,2913,2916,2917,2918,2919,2920,2921,2922,2926,2927,2928,2929][i - 1767]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1767 + (i - 1767)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1767 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1767).take
              (i - 1767))).length :=
      instructionPC_add Artifact.submissionArtifact 1767 (i - 1767)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1793 ≤ i) (hii : i ≤ 1805) :
    Artifact.submissionArtifact.instructionPC i =
      [2930,2931,2932,2933,2935,2936,2937,2940,2941,2943,2946,2947,2950][i - 1793]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1793 + (i - 1793)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1793 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1793).take
              (i - 1793))).length :=
      instructionPC_add Artifact.submissionArtifact 1793 (i - 1793)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1806 ≤ i) (hii : i ≤ 1840) :
    Artifact.submissionArtifact.instructionPC i =
      [2951,2952,2953,2956,2957,2958,2959,2960,2961,2962,2963,2966,2967,2969,2972,2973,2974,2975,2976,2978,2979,2980,2981,2983,2984,2985,2986,2988,2989,2990,2992,2993,2995,2996,2999][i - 1806]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1806 + (i - 1806)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1806 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1806).take
              (i - 1806))).length :=
      instructionPC_add Artifact.submissionArtifact 1806 (i - 1806)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1841 ≤ i) (hii : i ≤ 1855) :
    Artifact.submissionArtifact.instructionPC i =
      [3000,3001,3002,3005,3006,3009,3010,3013,3016,3017,3020,3023,3024,3025,3028][i - 1841]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1841 + (i - 1841)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1841 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1841).take
              (i - 1841))).length :=
      instructionPC_add Artifact.submissionArtifact 1841 (i - 1841)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1856..2385 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat) (hi : 2386 ≤ i) (hii : i ≤ 2438) :
    Artifact.submissionArtifact.instructionPC i =
      [3635,3636,3637,3638,3639,3640,3641,3643,3644,3645,
       3646,3649,3650,3651,3653,3656,3657,3660,3663,3666,
       3669,3672,3673,3674,3677,3680,3683,3686,3689,3690,
       3691,3692,3694,3695,3697,3698,3699,3700,3702,3703,
       3704,3706,3707,3709,3710,3711,3712,3713,3716,3717,
       3718,3720,3723][i - 2386]! := by
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

theorem jumpDest1982 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1982 = true :=
  Artifact.isValidJumpDest_index 1412 (by rfl)

theorem jumpDest1993 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1993 = true :=
  Artifact.isValidJumpDest_index 1421 (by rfl)

theorem jumpDest2009 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2009 = true :=
  Artifact.isValidJumpDest_index 1432 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1982 = true :=
  Artifact.isValidJumpDest_index 1412 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2009 = true :=
  Artifact.isValidJumpDest_index 1432 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2266 = true :=
  Artifact.isValidJumpDest_index 1540 (by rfl)

theorem jumpDest2250 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2250 = true :=
  Artifact.isValidJumpDest_index 1529 (by rfl)

theorem jumpDest2266 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2266 = true :=
  Artifact.isValidJumpDest_index 1540 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2496 = true :=
  Artifact.isValidJumpDest_index 1625 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2529 = true :=
  Artifact.isValidJumpDest_index 1652 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2671 = true :=
  Artifact.isValidJumpDest_index 1692 (by rfl)

theorem jumpDest2671 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2671 = true :=
  Artifact.isValidJumpDest_index 1692 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2695 = true :=
  Artifact.isValidJumpDest_index 1708 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2892 = true :=
  Artifact.isValidJumpDest_index 1767 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2903 = true :=
  Artifact.isValidJumpDest_index 1774 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2906 = true :=
  Artifact.isValidJumpDest_index 1776 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2917 = true :=
  Artifact.isValidJumpDest_index 1783 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2930 = true :=
  Artifact.isValidJumpDest_index 1793 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 1806 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2973 = true :=
  Artifact.isValidJumpDest_index 1821 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3000 = true :=
  Artifact.isValidJumpDest_index 1841 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 1853 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3600 = true :=
  Artifact.isValidJumpDest_index 2363 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3635 = true :=
  Artifact.isValidJumpDest_index 2386 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3673 = true :=
  Artifact.isValidJumpDest_index 2408 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2415 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
