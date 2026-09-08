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
    Artifact.submissionArtifact.instructionPC 972 = 1302 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 1011 = 1358 := by
  calc
    Artifact.submissionArtifact.instructionPC 1011 =
        Artifact.submissionArtifact.instructionPC 972 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 972).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 972 39
    _ = 1358 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1051 = 1415 := by
  calc
    Artifact.submissionArtifact.instructionPC 1051 =
        Artifact.submissionArtifact.instructionPC 1011 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1011).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1011 40
    _ = 1415 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1091 = 1463 := by
  calc
    Artifact.submissionArtifact.instructionPC 1091 =
        Artifact.submissionArtifact.instructionPC 1051 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1051).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1051 40
    _ = 1463 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1131 = 1519 := by
  calc
    Artifact.submissionArtifact.instructionPC 1131 =
        Artifact.submissionArtifact.instructionPC 1091 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1091).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1091 40
    _ = 1519 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1171 = 1595 := by
  calc
    Artifact.submissionArtifact.instructionPC 1171 =
        Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1131).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1131 40
    _ = 1595 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1211 = 1644 := by
  calc
    Artifact.submissionArtifact.instructionPC 1211 =
        Artifact.submissionArtifact.instructionPC 1171 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1171).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1171 40
    _ = 1644 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1250 = 1712 := by
  calc
    Artifact.submissionArtifact.instructionPC 1250 =
        Artifact.submissionArtifact.instructionPC 1211 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1211).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1211 39
    _ = 1712 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1289 = 1778 := by
  calc
    Artifact.submissionArtifact.instructionPC 1289 =
        Artifact.submissionArtifact.instructionPC 1250 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1250).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1250 39
    _ = 1778 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1329 = 1849 := by
  calc
    Artifact.submissionArtifact.instructionPC 1329 =
        Artifact.submissionArtifact.instructionPC 1289 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1289).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1289 40
    _ = 1849 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1369 = 1906 := by
  calc
    Artifact.submissionArtifact.instructionPC 1369 =
        Artifact.submissionArtifact.instructionPC 1329 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1329).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1329 40
    _ = 1906 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1408 = 1964 := by
  calc
    Artifact.submissionArtifact.instructionPC 1408 =
        Artifact.submissionArtifact.instructionPC 1369 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1369).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1369 39
    _ = 1964 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1444 = 2002 := by
  calc
    Artifact.submissionArtifact.instructionPC 1444 =
        Artifact.submissionArtifact.instructionPC 1408 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1408).take
              36)).length :=
      instructionPC_add Artifact.submissionArtifact 1408 36
    _ = 2002 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1474 = 2076 := by
  calc
    Artifact.submissionArtifact.instructionPC 1474 =
        Artifact.submissionArtifact.instructionPC 1444 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1444).take
              30)).length :=
      instructionPC_add Artifact.submissionArtifact 1444 30
    _ = 2076 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1514 = 2154 := by
  calc
    Artifact.submissionArtifact.instructionPC 1514 =
        Artifact.submissionArtifact.instructionPC 1474 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1474).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1474 40
    _ = 2154 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1548 = 2259 := by
  calc
    Artifact.submissionArtifact.instructionPC 1548 =
        Artifact.submissionArtifact.instructionPC 1514 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1514).take
              34)).length :=
      instructionPC_add Artifact.submissionArtifact 1514 34
    _ = 2259 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1588 = 2345 := by
  calc
    Artifact.submissionArtifact.instructionPC 1588 =
        Artifact.submissionArtifact.instructionPC 1548 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1548).take
              40)).length :=
      instructionPC_add Artifact.submissionArtifact 1548 40
    _ = 2345 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1626 = 2481 := by
  calc
    Artifact.submissionArtifact.instructionPC 1626 =
        Artifact.submissionArtifact.instructionPC 1588 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1588).take
              38)).length :=
      instructionPC_add Artifact.submissionArtifact 1588 38
    _ = 2481 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1663 = 2532 := by
  calc
    Artifact.submissionArtifact.instructionPC 1663 =
        Artifact.submissionArtifact.instructionPC 1626 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1626).take
              37)).length :=
      instructionPC_add Artifact.submissionArtifact 1626 37
    _ = 2532 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1702 = 2709 := by
  calc
    Artifact.submissionArtifact.instructionPC 1702 =
        Artifact.submissionArtifact.instructionPC 1663 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1663).take
              39)).length :=
      instructionPC_add Artifact.submissionArtifact 1663 39
    _ = 2709 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1705 = 2712 := by
  calc
    Artifact.submissionArtifact.instructionPC 1705 =
        Artifact.submissionArtifact.instructionPC 1702 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1702).take
              3)).length :=
      instructionPC_add Artifact.submissionArtifact 1702 3
    _ = 2712 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1731 = 2750 := by
  calc
    Artifact.submissionArtifact.instructionPC 1731 =
        Artifact.submissionArtifact.instructionPC 1705 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1705).take
              26)).length :=
      instructionPC_add Artifact.submissionArtifact 1705 26
    _ = 2750 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1744 = 2771 := by
  calc
    Artifact.submissionArtifact.instructionPC 1744 =
        Artifact.submissionArtifact.instructionPC 1731 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1731).take
              13)).length :=
      instructionPC_add Artifact.submissionArtifact 1731 13
    _ = 2771 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1779 = 2820 := by
  calc
    Artifact.submissionArtifact.instructionPC 1779 =
        Artifact.submissionArtifact.instructionPC 1744 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1744).take
              35)).length :=
      instructionPC_add Artifact.submissionArtifact 1744 35
    _ = 2820 := by
      rw [fastPCAnchor22]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 972 ≤ i) (hii : i ≤ 1010) :
    Artifact.submissionArtifact.instructionPC i =
      [1302,1303,1305,1306,1307,1309,1310,1313,1314,1316,1317,1318,1319,1320,1323,1324,1325,1328,1329,1330,1331,1334,1335,1336,1339,1340,1341,1343,1344,1346,1347,1348,1350,1351,1352,1353,1354,1356,1357][i - 972]! := by
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

@[simp] theorem fastPC1 (i : Nat) (hi : 1011 ≤ i) (hii : i ≤ 1050) :
    Artifact.submissionArtifact.instructionPC i =
      [1358,1359,1360,1362,1363,1364,1365,1366,1367,1368,1371,1372,1374,1375,1376,1377,1378,1379,1381,1382,1383,1386,1387,1388,1391,1392,1393,1396,1397,1398,1400,1401,1404,1405,1406,1408,1409,1410,1411,1414][i - 1011]! := by
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

@[simp] theorem fastPC2 (i : Nat) (hi : 1051 ≤ i) (hii : i ≤ 1090) :
    Artifact.submissionArtifact.instructionPC i =
      [1415,1416,1419,1420,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1440,1441,1442,1443,1445,1446,1447,1448,1449,1450,1452,1453,1454,1455,1456,1457,1459,1460,1461,1462][i - 1051]! := by
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

@[simp] theorem fastPC3 (i : Nat) (hi : 1091 ≤ i) (hii : i ≤ 1130) :
    Artifact.submissionArtifact.instructionPC i =
      [1463,1464,1466,1467,1468,1469,1470,1471,1473,1474,1475,1476,1477,1478,1480,1481,1482,1483,1484,1485,1487,1488,1489,1490,1491,1492,1494,1495,1496,1497,1498,1501,1502,1503,1504,1506,1509,1510,1513,1516][i - 1091]! := by
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

@[simp] theorem fastPC4 (i : Nat) (hi : 1131 ≤ i) (hii : i ≤ 1170) :
    Artifact.submissionArtifact.instructionPC i =
      [1519,1520,1521,1524,1525,1528,1531,1532,1535,1538,1541,1542,1543,1546,1547,1550,1553,1554,1556,1557,1560,1563,1566,1569,1572,1573,1574,1575,1576,1577,1579,1580,1583,1584,1587,1588,1591,1592,1593,1594][i - 1131]! := by
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

@[simp] theorem fastPC5 (i : Nat) (hi : 1171 ≤ i) (hii : i ≤ 1210) :
    Artifact.submissionArtifact.instructionPC i =
      [1595,1596,1597,1598,1599,1600,1603,1604,1605,1606,1607,1611,1612,1613,1614,1615,1616,1619,1620,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643][i - 1171]! := by
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

@[simp] theorem fastPC6 (i : Nat) (hi : 1211 ≤ i) (hii : i ≤ 1249) :
    Artifact.submissionArtifact.instructionPC i =
      [1644,1645,1646,1647,1650,1651,1654,1657,1660,1663,1666,1667,1668,1669,1670,1671,1673,1674,1675,1676,1678,1679,1680,1681,1684,1685,1686,1689,1692,1695,1698,1701,1702,1703,1705,1706,1709,1710,1711][i - 1211]! := by
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

@[simp] theorem fastPC7 (i : Nat) (hi : 1250 ≤ i) (hii : i ≤ 1288) :
    Artifact.submissionArtifact.instructionPC i =
      [1712,1713,1716,1719,1722,1725,1728,1729,1730,1731,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1746,1747,1750,1751,1752,1753,1754,1755,1756,1758,1759,1762,1765,1768,1771,1774,1775,1776,1777][i - 1250]! := by
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

@[simp] theorem fastPC8 (i : Nat) (hi : 1289 ≤ i) (hii : i ≤ 1328) :
    Artifact.submissionArtifact.instructionPC i =
      [1778,1779,1780,1783,1784,1787,1790,1793,1796,1799,1800,1801,1802,1804,1805,1806,1809,1810,1811,1812,1814,1815,1818,1819,1820,1821,1823,1824,1827,1828,1829,1832,1835,1838,1841,1844,1845,1846,1847,1848][i - 1289]! := by
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

@[simp] theorem fastPC9 (i : Nat) (hi : 1329 ≤ i) (hii : i ≤ 1368) :
    Artifact.submissionArtifact.instructionPC i =
      [1849,1852,1853,1854,1855,1856,1857,1860,1861,1862,1863,1864,1865,1868,1869,1870,1871,1872,1873,1874,1875,1876,1879,1880,1881,1884,1885,1888,1889,1890,1891,1894,1895,1896,1898,1899,1900,1901,1904,1905][i - 1329]! := by
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

@[simp] theorem fastPC10 (i : Nat) (hi : 1369 ≤ i) (hii : i ≤ 1407) :
    Artifact.submissionArtifact.instructionPC i =
      [1906,1907,1908,1909,1912,1913,1914,1916,1917,1918,1921,1922,1923,1924,1925,1927,1928,1929,1931,1932,1933,1934,1935,1936,1937,1939,1940,1941,1942,1943,1944,1945,1946,1947,1952,1953,1954,1962,1963][i - 1369]! := by
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

@[simp] theorem fastPC11 (i : Nat) (hi : 1408 ≤ i) (hii : i ≤ 1443) :
    Artifact.submissionArtifact.instructionPC i =
      [1964,1965,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001][i - 1408]! := by
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

@[simp] theorem fastPC12 (i : Nat) (hi : 1444 ≤ i) (hii : i ≤ 1473) :
    Artifact.submissionArtifact.instructionPC i =
      [2002,2003,2004,2005,2006,2007,2010,2011,2012,2013,2016,2017,2018,2021,2022,2025,2026,2027,2030,2031,2032,2033,2036,2037,2038,2039,2040,2041,2042,2075][i - 1444]! := by
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

@[simp] theorem fastPC13 (i : Nat) (hi : 1474 ≤ i) (hii : i ≤ 1513) :
    Artifact.submissionArtifact.instructionPC i =
      [2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2088,2091,2092,2094,2095,2096,2099,2100,2102,2103,2104,2105,2106,2107,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2152,2153][i - 1474]! := by
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

@[simp] theorem fastPC14 (i : Nat) (hi : 1514 ≤ i) (hii : i ≤ 1547) :
    Artifact.submissionArtifact.instructionPC i =
      [2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2169,2170,2203,2204,2205,2206,2207,2240,2241,2244,2245,2246,2249,2250,2251,2252,2253,2254,2255,2256][i - 1514]! := by
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

@[simp] theorem fastPC15 (i : Nat) (hi : 1548 ≤ i) (hii : i ≤ 1587) :
    Artifact.submissionArtifact.instructionPC i =
      [2259,2260,2261,2262,2265,2266,2267,2270,2271,2272,2275,2276,2309,2310,2311,2312,2313,2316,2317,2318,2319,2320,2323,2324,2325,2328,2329,2330,2331,2332,2334,2335,2336,2337,2338,2339,2341,2342,2343,2344][i - 1548]! := by
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

@[simp] theorem fastPC16 (i : Nat) (hi : 1588 ≤ i) (hii : i ≤ 1625) :
    Artifact.submissionArtifact.instructionPC i =
      [2345,2346,2347,2348,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2408,2409,2410,2443,2444,2445,2446,2479,2480][i - 1588]! := by
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

@[simp] theorem fastPC17 (i : Nat) (hi : 1626 ≤ i) (hii : i ≤ 1662) :
    Artifact.submissionArtifact.instructionPC i =
      [2481,2484,2485,2486,2489,2490,2491,2492,2493,2496,2497,2498,2501,2502,2505,2506,2507,2510,2511,2514,2515,2516,2517,2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531][i - 1626]! := by
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

@[simp] theorem fastPC18 (i : Nat) (hi : 1663 ≤ i) (hii : i ≤ 1701) :
    Artifact.submissionArtifact.instructionPC i =
      [2532,2533,2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2576,2577,2578,2611,2612,2613,2614,2647,2648,2649,2652,2653,2654,2657,2658,2659,2660,2661,2662,2665,2666,2667,2700,2701,2704,2705,2708][i - 1663]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1687 + (i - 1687)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1687 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1687).take
              (i - 1687))).length :=
      instructionPC_add Artifact.submissionArtifact 1687 (i - 1687)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1702 ≤ i) (hii : i ≤ 1704) :
    Artifact.submissionArtifact.instructionPC i =
      [2709,2710,2711][i - 1702]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1727 + (i - 1727)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1727 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1727).take
              (i - 1727))).length :=
      instructionPC_add Artifact.submissionArtifact 1727 (i - 1727)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1705 ≤ i) (hii : i ≤ 1730) :
    Artifact.submissionArtifact.instructionPC i =
      [2712,2713,2716,2717,2718,2719,2722,2723,2724,2726,2727,2730,2731,2732,2733,2736,2737,2738,2739,2740,2741,2742,2746,2747,2748,2749][i - 1705]! := by
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
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1731 ≤ i) (hii : i ≤ 1743) :
    Artifact.submissionArtifact.instructionPC i =
      [2750,2751,2752,2753,2755,2756,2757,2760,2761,2763,2766,2767,2770][i - 1731]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1758 + (i - 1758)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1758 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1758).take
              (i - 1758))).length :=
      instructionPC_add Artifact.submissionArtifact 1758 (i - 1758)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1744 ≤ i) (hii : i ≤ 1778) :
    Artifact.submissionArtifact.instructionPC i =
      [2771,2772,2773,2776,2777,2778,2779,2780,2781,2782,2783,2786,2787,2789,2792,2793,2794,2795,2796,2798,2799,2800,2801,2803,2804,2805,2806,2808,2809,2810,2812,2813,2815,2816,2819][i - 1744]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1771 + (i - 1771)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1771 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 1771).take
              (i - 1771))).length :=
      instructionPC_add Artifact.submissionArtifact 1771 (i - 1771)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1779 ≤ i) (hii : i ≤ 1793) :
    Artifact.submissionArtifact.instructionPC i =
      [2820,2821,2822,2825,2826,2829,2830,2833,2836,2837,2840,2843,2844,2845,2848][i - 1779]! := by
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
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

/-- PC table for the appended full-width-base helper. The intervening window
and direct-RR helpers occupy indices 1831..2360 and receive their own tables in
their proof modules. -/
@[simp] theorem fullBasePC (i : Nat)
    (hi : 2253 ≤ i) (hii : i ≤ 2305) :
    Artifact.submissionArtifact.instructionPC i =
      ([3601,3602,3603,3604,3605,3606,3607,3609,3610,3611,3612,3615,3616,3617,3619,3622,3623,3626,3629,3632,3635,3638,3639,3640,3643,3646,3649,3652,3655,3656,3657,3658,3660,3661,3663,3664,3665,3666,3668,3669,3670,3672,3673,3675,3676,3677,3678,3679,3682,3683,3684,3686,3689] : List Nat)[i - 2253]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1185 = true :=
  Artifact.isValidJumpDest_index 895 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1520 = true :=
  Artifact.isValidJumpDest_index 1132 (by rfl)

theorem jumpDest1555 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1542 = true :=
  Artifact.isValidJumpDest_index 1142 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1556 = true :=
  Artifact.isValidJumpDest_index 1149 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1573 = true :=
  Artifact.isValidJumpDest_index 1156 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1596 = true :=
  Artifact.isValidJumpDest_index 1172 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1612 = true :=
  Artifact.isValidJumpDest_index 1183 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1643 = true :=
  Artifact.isValidJumpDest_index 1210 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1667 = true :=
  Artifact.isValidJumpDest_index 1222 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1702 = true :=
  Artifact.isValidJumpDest_index 1243 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1710 = true :=
  Artifact.isValidJumpDest_index 1248 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1729 = true :=
  Artifact.isValidJumpDest_index 1257 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1730 = true :=
  Artifact.isValidJumpDest_index 1258 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1739 = true :=
  Artifact.isValidJumpDest_index 1265 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1758 = true :=
  Artifact.isValidJumpDest_index 1279 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1775 = true :=
  Artifact.isValidJumpDest_index 1286 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1800 = true :=
  Artifact.isValidJumpDest_index 1299 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1801 = true :=
  Artifact.isValidJumpDest_index 1300 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1819 = true :=
  Artifact.isValidJumpDest_index 1312 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1845 = true :=
  Artifact.isValidJumpDest_index 1325 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1855 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1861 = true :=
  Artifact.isValidJumpDest_index 1337 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1869 = true :=
  Artifact.isValidJumpDest_index 1343 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1880 = true :=
  Artifact.isValidJumpDest_index 1352 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1884 = true :=
  Artifact.isValidJumpDest_index 1354 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1895 = true :=
  Artifact.isValidJumpDest_index 1361 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1908 = true :=
  Artifact.isValidJumpDest_index 1371 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1943 = true :=
  Artifact.isValidJumpDest_index 1398 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1964 = true :=
  Artifact.isValidJumpDest_index 1408 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2104 = true :=
  Artifact.isValidJumpDest_index 1496 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2324 = true :=
  Artifact.isValidJumpDest_index 1571 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2355 = true :=
  Artifact.isValidJumpDest_index 1596 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2497 = true :=
  Artifact.isValidJumpDest_index 1636 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2520 = true :=
  Artifact.isValidJumpDest_index 1651 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2712 = true :=
  Artifact.isValidJumpDest_index 1705 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2723 = true :=
  Artifact.isValidJumpDest_index 1712 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2726 = true :=
  Artifact.isValidJumpDest_index 1714 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2737 = true :=
  Artifact.isValidJumpDest_index 1721 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2750 = true :=
  Artifact.isValidJumpDest_index 1731 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2771 = true :=
  Artifact.isValidJumpDest_index 1744 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2793 = true :=
  Artifact.isValidJumpDest_index 1759 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2820 = true :=
  Artifact.isValidJumpDest_index 1779 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2844 = true :=
  Artifact.isValidJumpDest_index 1791 (by rfl)

theorem jumpDest3571 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3420 = true :=
  Artifact.isValidJumpDest_index 2203 (by rfl)

theorem jumpDest3606 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3455 = true :=
  Artifact.isValidJumpDest_index 2226 (by rfl)

theorem jumpDest3644 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3493 = true :=
  Artifact.isValidJumpDest_index 2248 (by rfl)

theorem jumpDest3661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3510 = true :=
  Artifact.isValidJumpDest_index 2255 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
