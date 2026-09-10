import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The tables and jump facts below describe the selected round06 layout.
Each table uses a proved prefix-sum anchor and a bounded local slice.
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


/-! Submission-local prefix-sum PC certificates. -/

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
    Artifact.submissionArtifact.instructionPC 1016 = 1370 := by
  calc
    Artifact.submissionArtifact.instructionPC 1016 =
        Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 977 39
    _ = 1370 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1055 = 1426 := by
  calc
    Artifact.submissionArtifact.instructionPC 1055 =
        Artifact.submissionArtifact.instructionPC 1016 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1016).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1016 39
    _ = 1426 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1091 = 1469 := by
  calc
    Artifact.submissionArtifact.instructionPC 1091 =
        Artifact.submissionArtifact.instructionPC 1055 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1055).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1055 36
    _ = 1469 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1131 = 1525 := by
  calc
    Artifact.submissionArtifact.instructionPC 1131 =
        Artifact.submissionArtifact.instructionPC 1091 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1091).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1091 40
    _ = 1525 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1161 = 1584 := by
  calc
    Artifact.submissionArtifact.instructionPC 1161 =
        Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1131).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1131 30
    _ = 1584 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1181 = 1612 := by
  calc
    Artifact.submissionArtifact.instructionPC 1181 =
        Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1161 20
    _ = 1612 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1220 = 1680 := by
  calc
    Artifact.submissionArtifact.instructionPC 1220 =
        Artifact.submissionArtifact.instructionPC 1181 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1181).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1181 39
    _ = 1680 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1249 = 1735 := by
  calc
    Artifact.submissionArtifact.instructionPC 1249 =
        Artifact.submissionArtifact.instructionPC 1220 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1220).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 1220 29
    _ = 1735 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1289 = 1806 := by
  calc
    Artifact.submissionArtifact.instructionPC 1289 =
        Artifact.submissionArtifact.instructionPC 1249 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1249).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1249 40
    _ = 1806 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1329 = 1863 := by
  calc
    Artifact.submissionArtifact.instructionPC 1329 =
        Artifact.submissionArtifact.instructionPC 1289 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1289).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1289 40
    _ = 1863 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1368 = 1914 := by
  calc
    Artifact.submissionArtifact.instructionPC 1368 =
        Artifact.submissionArtifact.instructionPC 1329 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1329).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1329 39
    _ = 1914 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1405 = 1951 := by
  calc
    Artifact.submissionArtifact.instructionPC 1405 =
        Artifact.submissionArtifact.instructionPC 1368 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1368).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1368 37
    _ = 1951 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1448 = 2010 := by
  calc
    Artifact.submissionArtifact.instructionPC 1448 =
        Artifact.submissionArtifact.instructionPC 1405 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1405).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1405 43
    _ = 2010 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1489 = 2057 := by
  calc
    Artifact.submissionArtifact.instructionPC 1489 =
        Artifact.submissionArtifact.instructionPC 1448 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1448).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1448 41
    _ = 2057 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1525 = 2102 := by
  calc
    Artifact.submissionArtifact.instructionPC 1525 =
        Artifact.submissionArtifact.instructionPC 1489 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1489).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1489 36
    _ = 2102 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1566 = 2158 := by
  calc
    Artifact.submissionArtifact.instructionPC 1566 =
        Artifact.submissionArtifact.instructionPC 1525 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1525).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1525 41
    _ = 2158 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1607 = 2204 := by
  calc
    Artifact.submissionArtifact.instructionPC 1607 =
        Artifact.submissionArtifact.instructionPC 1566 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1566).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1566 41
    _ = 2204 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1632 = 2237 := by
  calc
    Artifact.submissionArtifact.instructionPC 1632 =
        Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1607).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 1607 25
    _ = 2237 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1675 = 2295 := by
  calc
    Artifact.submissionArtifact.instructionPC 1675 =
        Artifact.submissionArtifact.instructionPC 1632 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1632).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1632 43
    _ = 2295 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1678 = 2298 := by
  calc
    Artifact.submissionArtifact.instructionPC 1678 =
        Artifact.submissionArtifact.instructionPC 1675 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1675).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1675 3
    _ = 2298 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1696 = 2322 := by
  calc
    Artifact.submissionArtifact.instructionPC 1696 =
        Artifact.submissionArtifact.instructionPC 1678 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1678).take 18)).length :=
      instructionPC_add Artifact.submissionArtifact 1678 18
    _ = 2322 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1709 = 2343 := by
  calc
    Artifact.submissionArtifact.instructionPC 1709 =
        Artifact.submissionArtifact.instructionPC 1696 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1696).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1696 13
    _ = 2343 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1744 = 2392 := by
  calc
    Artifact.submissionArtifact.instructionPC 1744 =
        Artifact.submissionArtifact.instructionPC 1709 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1709).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1709 35
    _ = 2392 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2399 = 3146 := by
  calc
    Artifact.submissionArtifact.instructionPC 2399 =
        Artifact.submissionArtifact.instructionPC 1744 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1744).take 655)).length :=
      instructionPC_add Artifact.submissionArtifact 1744 655
    _ = 3146 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 977 ≤ i) (hii : i ≤ 1015) :
    Artifact.submissionArtifact.instructionPC i =
      [1314,1315,1317,1318,1319,1321,1322,1325,1326,1328,1329,1330,1331,1332,1335,1336,1337,1340,1341,1342,1343,1346,1347,1348,1351,1352,1353,1355,1356,1358,1359,1360,1362,1363,1364,1365,1366,1368,1369][i - 977]! := by
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

@[simp] theorem fastPC1 (i : Nat) (hi : 1016 ≤ i) (hii : i ≤ 1054) :
    Artifact.submissionArtifact.instructionPC i =
      [1370,1371,1372,1374,1375,1376,1377,1378,1379,1380,1383,1384,1386,1387,1388,1389,1390,1391,1393,1394,1395,1398,1399,1400,1403,1404,1405,1408,1409,1410,1412,1413,1416,1417,1419,1420,1421,1422,1425][i - 1016]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1016 + (i - 1016)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1016 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1016).take (i - 1016))).length :=
      instructionPC_add Artifact.submissionArtifact 1016 (i - 1016)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1055 ≤ i) (hii : i ≤ 1090) :
    Artifact.submissionArtifact.instructionPC i =
      [1426,1427,1430,1431,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1452,1453,1454,1455,1456,1458,1459,1460,1461,1462,1463,1465,1466,1467,1468][i - 1055]! := by
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
      [1469,1470,1472,1473,1474,1475,1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1507,1508,1509,1510,1512,1515,1516,1519,1522][i - 1091]! := by
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

@[simp] theorem fastPC4 (i : Nat) (hi : 1131 ≤ i) (hii : i ≤ 1160) :
    Artifact.submissionArtifact.instructionPC i =
      [1525,1526,1527,1530,1531,1534,1537,1538,1541,1544,1547,1548,1549,1552,1555,1558,1561,1564,1565,1566,1567,1568,1569,1571,1572,1575,1576,1579,1580,1583][i - 1131]! := by
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

@[simp] theorem fastPC5 (i : Nat) (hi : 1161 ≤ i) (hii : i ≤ 1180) :
    Artifact.submissionArtifact.instructionPC i =
      [1584,1585,1586,1587,1588,1591,1592,1593,1594,1595,1598,1599,1600,1601,1602,1603,1606,1607,1610,1611][i - 1161]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1161 + (i - 1161)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take (i - 1161))).length :=
      instructionPC_add Artifact.submissionArtifact 1161 (i - 1161)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1181 ≤ i) (hii : i ≤ 1219) :
    Artifact.submissionArtifact.instructionPC i =
      [1612,1613,1614,1615,1618,1619,1622,1625,1628,1631,1634,1635,1636,1637,1638,1639,1641,1642,1643,1644,1646,1647,1648,1649,1652,1653,1654,1657,1660,1663,1666,1669,1670,1671,1673,1674,1677,1678,1679][i - 1181]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1181 + (i - 1181)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1181 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1181).take (i - 1181))).length :=
      instructionPC_add Artifact.submissionArtifact 1181 (i - 1181)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1220 ≤ i) (hii : i ≤ 1248) :
    Artifact.submissionArtifact.instructionPC i =
      [1680,1681,1684,1687,1690,1693,1696,1697,1698,1699,1702,1703,1704,1705,1706,1707,1710,1711,1714,1715,1716,1719,1722,1725,1728,1731,1732,1733,1734][i - 1220]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1220 + (i - 1220)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1220 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1220).take (i - 1220))).length :=
      instructionPC_add Artifact.submissionArtifact 1220 (i - 1220)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1249 ≤ i) (hii : i ≤ 1288) :
    Artifact.submissionArtifact.instructionPC i =
      [1735,1736,1737,1740,1741,1744,1747,1750,1753,1756,1757,1758,1759,1761,1762,1763,1766,1767,1768,1769,1771,1772,1775,1776,1777,1778,1780,1781,1784,1785,1786,1789,1792,1795,1798,1801,1802,1803,1804,1805][i - 1249]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1249 + (i - 1249)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1249 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1249).take (i - 1249))).length :=
      instructionPC_add Artifact.submissionArtifact 1249 (i - 1249)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1289 ≤ i) (hii : i ≤ 1328) :
    Artifact.submissionArtifact.instructionPC i =
      [1806,1809,1810,1811,1812,1813,1814,1817,1818,1819,1820,1821,1822,1825,1826,1827,1828,1829,1830,1831,1832,1833,1836,1837,1838,1841,1842,1845,1846,1847,1848,1851,1852,1853,1855,1856,1857,1858,1861,1862][i - 1289]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1289 + (i - 1289)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1289 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1289).take (i - 1289))).length :=
      instructionPC_add Artifact.submissionArtifact 1289 (i - 1289)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1329 ≤ i) (hii : i ≤ 1367) :
    Artifact.submissionArtifact.instructionPC i =
      [1863,1864,1865,1866,1869,1870,1871,1873,1874,1875,1878,1879,1880,1881,1882,1884,1885,1886,1888,1889,1890,1891,1892,1893,1894,1896,1897,1898,1899,1900,1901,1902,1903,1904,1907,1908,1909,1912,1913][i - 1329]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1329 + (i - 1329)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1329 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1329).take (i - 1329))).length :=
      instructionPC_add Artifact.submissionArtifact 1329 (i - 1329)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1368 ≤ i) (hii : i ≤ 1404) :
    Artifact.submissionArtifact.instructionPC i =
      [1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950][i - 1368]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1368 + (i - 1368)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1368 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1368).take (i - 1368))).length :=
      instructionPC_add Artifact.submissionArtifact 1368 (i - 1368)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1405 ≤ i) (hii : i ≤ 1447) :
    Artifact.submissionArtifact.instructionPC i =
      [1951,1952,1954,1955,1956,1957,1959,1960,1961,1962,1963,1964,1965,1968,1969,1970,1971,1972,1975,1976,1977,1978,1981,1982,1983,1986,1987,1990,1991,1992,1995,1996,1997,1998,2001,2002,2003,2004,2005,2006,2007,2008,2009][i - 1405]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1405 + (i - 1405)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1405 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1405).take (i - 1405))).length :=
      instructionPC_add Artifact.submissionArtifact 1405 (i - 1405)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1448 ≤ i) (hii : i ≤ 1488) :
    Artifact.submissionArtifact.instructionPC i =
      [2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2025,2026,2028,2029,2030,2033,2034,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056][i - 1448]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1448 + (i - 1448)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1448 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1448).take (i - 1448))).length :=
      instructionPC_add Artifact.submissionArtifact 1448 (i - 1448)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1489 ≤ i) (hii : i ≤ 1524) :
    Artifact.submissionArtifact.instructionPC i =
      [2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2072,2073,2075,2076,2077,2078,2079,2080,2082,2083,2084,2087,2088,2089,2092,2093,2094,2095,2096,2097,2098,2099][i - 1489]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1489 + (i - 1489)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1489 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1489).take (i - 1489))).length :=
      instructionPC_add Artifact.submissionArtifact 1489 (i - 1489)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1525 ≤ i) (hii : i ≤ 1565) :
    Artifact.submissionArtifact.instructionPC i =
      [2102,2103,2104,2105,2108,2109,2110,2113,2114,2115,2118,2119,2121,2122,2123,2124,2125,2126,2129,2130,2131,2132,2133,2136,2137,2138,2141,2142,2143,2144,2145,2147,2148,2149,2150,2151,2152,2154,2155,2156,2157][i - 1525]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1525 + (i - 1525)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1525 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1525).take (i - 1525))).length :=
      instructionPC_add Artifact.submissionArtifact 1525 (i - 1525)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1566 ≤ i) (hii : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [2158,2159,2160,2161,2164,2165,2166,2167,2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2190,2191,2192,2193,2195,2196,2197,2198,2199,2201,2202,2203][i - 1566]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1566 + (i - 1566)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1566 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1566).take (i - 1566))).length :=
      instructionPC_add Artifact.submissionArtifact 1566 (i - 1566)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1607 ≤ i) (hii : i ≤ 1631) :
    Artifact.submissionArtifact.instructionPC i =
      [2204,2207,2208,2209,2212,2213,2214,2215,2216,2219,2220,2221,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236][i - 1607]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1607 + (i - 1607)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1607).take (i - 1607))).length :=
      instructionPC_add Artifact.submissionArtifact 1607 (i - 1607)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1632 ≤ i) (hii : i ≤ 1674) :
    Artifact.submissionArtifact.instructionPC i =
      [2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2250,2251,2252,2253,2255,2256,2257,2258,2259,2261,2262,2263,2264,2267,2268,2269,2272,2273,2274,2275,2276,2277,2280,2281,2282,2285,2286,2287,2290,2291,2294][i - 1632]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1632 + (i - 1632)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1632 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1632).take (i - 1632))).length :=
      instructionPC_add Artifact.submissionArtifact 1632 (i - 1632)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1675 ≤ i) (hii : i ≤ 1677) :
    Artifact.submissionArtifact.instructionPC i =
      [2295,2296,2297][i - 1675]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1675 + (i - 1675)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1675 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1675).take (i - 1675))).length :=
      instructionPC_add Artifact.submissionArtifact 1675 (i - 1675)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1678 ≤ i) (hii : i ≤ 1695) :
    Artifact.submissionArtifact.instructionPC i =
      [2298,2299,2300,2303,2304,2305,2306,2309,2310,2311,2312,2313,2314,2315,2318,2319,2320,2321][i - 1678]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1678 + (i - 1678)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1678 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1678).take (i - 1678))).length :=
      instructionPC_add Artifact.submissionArtifact 1678 (i - 1678)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1696 ≤ i) (hii : i ≤ 1708) :
    Artifact.submissionArtifact.instructionPC i =
      [2322,2323,2324,2325,2327,2328,2329,2332,2333,2335,2338,2339,2342][i - 1696]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1696 + (i - 1696)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1696 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1696).take (i - 1696))).length :=
      instructionPC_add Artifact.submissionArtifact 1696 (i - 1696)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1709 ≤ i) (hii : i ≤ 1743) :
    Artifact.submissionArtifact.instructionPC i =
      [2343,2344,2345,2348,2349,2350,2351,2352,2353,2354,2355,2358,2359,2361,2364,2365,2366,2367,2368,2370,2371,2372,2373,2375,2376,2377,2378,2380,2381,2382,2384,2385,2387,2388,2391][i - 1709]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1709 + (i - 1709)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1709 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1709).take (i - 1709))).length :=
      instructionPC_add Artifact.submissionArtifact 1709 (i - 1709)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1744 ≤ i) (hii : i ≤ 1755) :
    Artifact.submissionArtifact.instructionPC i =
      [2392,2393,2394,2397,2398,2401,2402,2405,2408,2409,2412,2415][i - 1744]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1744 + (i - 1744)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1744 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1744).take (i - 1744))).length :=
      instructionPC_add Artifact.submissionArtifact 1744 (i - 1744)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2399 ≤ i) (hii : i ≤ 2444) :
    Artifact.submissionArtifact.instructionPC i =
      [3146,3147,3148,3149,3150,3151,3152,3154,3155,3156,3157,3160,3161,3162,3164,3167,3168,3171,3174,3177,3180,3183,3184,3185,3186,3188,3189,3191,3192,3193,3194,3196,3197,3198,3200,3201,3203,3204,3205,3206,3207,3210,3211,3212,3214,3217][i - 2399]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2399 + (i - 2399)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2399 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2399).take (i - 2399))).length :=
      instructionPC_add Artifact.submissionArtifact 2399 (i - 2399)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1526 = true :=
  Artifact.isValidJumpDest_index 1132 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1548 = true :=
  Artifact.isValidJumpDest_index 1142 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1565 = true :=
  Artifact.isValidJumpDest_index 1149 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1584 = true :=
  Artifact.isValidJumpDest_index 1161 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1172 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1611 = true :=
  Artifact.isValidJumpDest_index 1180 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1635 = true :=
  Artifact.isValidJumpDest_index 1192 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1670 = true :=
  Artifact.isValidJumpDest_index 1213 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1678 = true :=
  Artifact.isValidJumpDest_index 1218 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1697 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

theorem jumpDest1698 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1698 = true :=
  Artifact.isValidJumpDest_index 1228 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3412 = true :=
  Artifact.isValidJumpDest_index 2601 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1703 = true :=
  Artifact.isValidJumpDest_index 1231 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1715 = true :=
  Artifact.isValidJumpDest_index 1239 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1732 = true :=
  Artifact.isValidJumpDest_index 1246 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1757 = true :=
  Artifact.isValidJumpDest_index 1259 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1758 = true :=
  Artifact.isValidJumpDest_index 1260 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1776 = true :=
  Artifact.isValidJumpDest_index 1272 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1802 = true :=
  Artifact.isValidJumpDest_index 1285 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1812 = true :=
  Artifact.isValidJumpDest_index 1293 (by rfl)

theorem jumpDest1818 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1818 = true :=
  Artifact.isValidJumpDest_index 1297 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1826 = true :=
  Artifact.isValidJumpDest_index 1303 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1837 = true :=
  Artifact.isValidJumpDest_index 1312 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1841 = true :=
  Artifact.isValidJumpDest_index 1314 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1852 = true :=
  Artifact.isValidJumpDest_index 1321 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1865 = true :=
  Artifact.isValidJumpDest_index 1331 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1900 = true :=
  Artifact.isValidJumpDest_index 1358 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1914 = true :=
  Artifact.isValidJumpDest_index 1368 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2038 = true :=
  Artifact.isValidJumpDest_index 1470 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2137 = true :=
  Artifact.isValidJumpDest_index 1549 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2168 = true :=
  Artifact.isValidJumpDest_index 1574 (by rfl)

theorem jumpDest2220 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2220 = true :=
  Artifact.isValidJumpDest_index 1617 (by rfl)

theorem jumpDest4976 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4976 = true :=
  Artifact.isValidJumpDest_index 3778 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2225 = true :=
  Artifact.isValidJumpDest_index 1620 (by rfl)

theorem jumpDest2298 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2298 = true :=
  Artifact.isValidJumpDest_index 1678 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2299 = true :=
  Artifact.isValidJumpDest_index 1679 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2310 = true :=
  Artifact.isValidJumpDest_index 1686 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2322 = true :=
  Artifact.isValidJumpDest_index 1696 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2343 = true :=
  Artifact.isValidJumpDest_index 1709 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2365 = true :=
  Artifact.isValidJumpDest_index 1724 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2392 = true :=
  Artifact.isValidJumpDest_index 1744 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3111 = true :=
  Artifact.isValidJumpDest_index 2376 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2399 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3184 = true :=
  Artifact.isValidJumpDest_index 2421 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
