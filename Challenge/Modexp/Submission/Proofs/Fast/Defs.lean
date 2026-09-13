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
    Artifact.submissionArtifact.instructionPC 932 = 1251 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 961 = 1290 := by
  calc
    Artifact.submissionArtifact.instructionPC 961 =
        Artifact.submissionArtifact.instructionPC 932 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 932).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 932 29
    _ = 1290 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 998 = 1342 := by
  calc
    Artifact.submissionArtifact.instructionPC 998 =
        Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 961 37
    _ = 1342 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1034 = 1385 := by
  calc
    Artifact.submissionArtifact.instructionPC 1034 =
        Artifact.submissionArtifact.instructionPC 998 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 998).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 998 36
    _ = 1385 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1069 = 1429 := by
  calc
    Artifact.submissionArtifact.instructionPC 1069 =
        Artifact.submissionArtifact.instructionPC 1034 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1034).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1034 35
    _ = 1429 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1099 = 1486 := by
  calc
    Artifact.submissionArtifact.instructionPC 1099 =
        Artifact.submissionArtifact.instructionPC 1069 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1069).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1069 30
    _ = 1486 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1119 = 1514 := by
  calc
    Artifact.submissionArtifact.instructionPC 1119 =
        Artifact.submissionArtifact.instructionPC 1099 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1099).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1099 20
    _ = 1514 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1158 = 1582 := by
  calc
    Artifact.submissionArtifact.instructionPC 1158 =
        Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1119 39
    _ = 1582 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1183 = 1629 := by
  calc
    Artifact.submissionArtifact.instructionPC 1183 =
        Artifact.submissionArtifact.instructionPC 1158 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1158).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 1158 25
    _ = 1629 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1223 = 1700 := by
  calc
    Artifact.submissionArtifact.instructionPC 1223 =
        Artifact.submissionArtifact.instructionPC 1183 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1183).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1183 40
    _ = 1700 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1257 = 1749 := by
  calc
    Artifact.submissionArtifact.instructionPC 1257 =
        Artifact.submissionArtifact.instructionPC 1223 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1223).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1223 34
    _ = 1749 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1296 = 1800 := by
  calc
    Artifact.submissionArtifact.instructionPC 1296 =
        Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1257).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1257 39
    _ = 1800 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1333 = 1837 := by
  calc
    Artifact.submissionArtifact.instructionPC 1333 =
        Artifact.submissionArtifact.instructionPC 1296 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1296).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1296 37
    _ = 1837 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1376 = 1896 := by
  calc
    Artifact.submissionArtifact.instructionPC 1376 =
        Artifact.submissionArtifact.instructionPC 1333 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1333).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1333 43
    _ = 1896 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1417 = 1943 := by
  calc
    Artifact.submissionArtifact.instructionPC 1417 =
        Artifact.submissionArtifact.instructionPC 1376 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1376).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1376 41
    _ = 1943 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1453 = 1988 := by
  calc
    Artifact.submissionArtifact.instructionPC 1453 =
        Artifact.submissionArtifact.instructionPC 1417 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1417).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1417 36
    _ = 1988 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1494 = 2044 := by
  calc
    Artifact.submissionArtifact.instructionPC 1494 =
        Artifact.submissionArtifact.instructionPC 1453 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1453).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1453 41
    _ = 2044 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1535 = 2090 := by
  calc
    Artifact.submissionArtifact.instructionPC 1535 =
        Artifact.submissionArtifact.instructionPC 1494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1494).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1494 41
    _ = 2090 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1559 = 2122 := by
  calc
    Artifact.submissionArtifact.instructionPC 1559 =
        Artifact.submissionArtifact.instructionPC 1535 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1535).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1535 24
    _ = 2122 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1602 = 2180 := by
  calc
    Artifact.submissionArtifact.instructionPC 1602 =
        Artifact.submissionArtifact.instructionPC 1559 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1559).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1559 43
    _ = 2180 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1605 = 2183 := by
  calc
    Artifact.submissionArtifact.instructionPC 1605 =
        Artifact.submissionArtifact.instructionPC 1602 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1602).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1602 3
    _ = 2183 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1622 = 2206 := by
  calc
    Artifact.submissionArtifact.instructionPC 1622 =
        Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1605 17
    _ = 2206 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1635 = 2227 := by
  calc
    Artifact.submissionArtifact.instructionPC 1635 =
        Artifact.submissionArtifact.instructionPC 1622 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1622).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1622 13
    _ = 2227 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1670 = 2276 := by
  calc
    Artifact.submissionArtifact.instructionPC 1670 =
        Artifact.submissionArtifact.instructionPC 1635 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1635).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1635 35
    _ = 2276 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2282 = 3005 := by
  calc
    Artifact.submissionArtifact.instructionPC 2282 =
        Artifact.submissionArtifact.instructionPC 1670 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1670).take 612)).length :=
      instructionPC_add Artifact.submissionArtifact 1670 612
    _ = 3005 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 932 ≤ i) (hii : i ≤ 960) :
    Artifact.submissionArtifact.instructionPC i =
      [1251,1252,1254,1255,1256,1258,1259,1260,1262,1263,1266,1267,1269,1270,1271,1272,1273,1275,1276,1278,1279,1280,1282,1283,1284,1285,1286,1288,1289][i - 932]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (932 + (i - 932)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 932 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 932).take (i - 932))).length :=
      instructionPC_add Artifact.submissionArtifact 932 (i - 932)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 961 ≤ i) (hii : i ≤ 997) :
    Artifact.submissionArtifact.instructionPC i =
      [1290,1291,1292,1294,1295,1296,1297,1298,1299,1300,1303,1304,1306,1307,1308,1309,1310,1311,1313,1314,1315,1318,1319,1320,1323,1324,1325,1326,1328,1329,1332,1333,1335,1336,1337,1338,1341][i - 961]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (961 + (i - 961)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take (i - 961))).length :=
      instructionPC_add Artifact.submissionArtifact 961 (i - 961)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 998 ≤ i) (hii : i ≤ 1033) :
    Artifact.submissionArtifact.instructionPC i =
      [1342,1343,1346,1347,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1368,1369,1370,1371,1372,1374,1375,1376,1377,1378,1379,1381,1382,1383,1384][i - 998]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (998 + (i - 998)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 998 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 998).take (i - 998))).length :=
      instructionPC_add Artifact.submissionArtifact 998 (i - 998)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1034 ≤ i) (hii : i ≤ 1068) :
    Artifact.submissionArtifact.instructionPC i =
      [1385,1386,1388,1389,1390,1391,1392,1393,1395,1396,1397,1398,1399,1400,1402,1403,1404,1405,1406,1407,1409,1410,1411,1412,1413,1414,1416,1417,1418,1419,1420,1423,1424,1425,1426][i - 1034]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1034 + (i - 1034)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1034 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1034).take (i - 1034))).length :=
      instructionPC_add Artifact.submissionArtifact 1034 (i - 1034)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1069 ≤ i) (hii : i ≤ 1098) :
    Artifact.submissionArtifact.instructionPC i =
      [1429,1430,1431,1434,1435,1438,1441,1442,1445,1448,1451,1452,1453,1456,1459,1460,1463,1466,1467,1468,1469,1470,1471,1473,1474,1477,1478,1481,1482,1485][i - 1069]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1069 + (i - 1069)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1069 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1069).take (i - 1069))).length :=
      instructionPC_add Artifact.submissionArtifact 1069 (i - 1069)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1099 ≤ i) (hii : i ≤ 1118) :
    Artifact.submissionArtifact.instructionPC i =
      [1486,1487,1488,1489,1490,1493,1494,1495,1496,1497,1500,1501,1502,1503,1504,1505,1508,1509,1512,1513][i - 1099]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1099 + (i - 1099)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1099 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1099).take (i - 1099))).length :=
      instructionPC_add Artifact.submissionArtifact 1099 (i - 1099)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1119 ≤ i) (hii : i ≤ 1157) :
    Artifact.submissionArtifact.instructionPC i =
      [1514,1515,1516,1517,1520,1521,1524,1527,1530,1533,1536,1537,1538,1539,1540,1541,1543,1544,1545,1546,1548,1549,1550,1551,1554,1555,1556,1559,1562,1565,1568,1571,1572,1573,1575,1576,1579,1580,1581][i - 1119]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1119 + (i - 1119)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take (i - 1119))).length :=
      instructionPC_add Artifact.submissionArtifact 1119 (i - 1119)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1158 ≤ i) (hii : i ≤ 1182) :
    Artifact.submissionArtifact.instructionPC i =
      [1582,1583,1586,1589,1592,1595,1598,1599,1600,1601,1602,1603,1606,1607,1610,1611,1612,1615,1618,1619,1622,1625,1626,1627,1628][i - 1158]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1158 + (i - 1158)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1158 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1158).take (i - 1158))).length :=
      instructionPC_add Artifact.submissionArtifact 1158 (i - 1158)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1183 ≤ i) (hii : i ≤ 1222) :
    Artifact.submissionArtifact.instructionPC i =
      [1629,1630,1631,1634,1635,1638,1641,1644,1647,1650,1651,1652,1653,1655,1656,1657,1660,1661,1662,1663,1665,1666,1669,1670,1671,1672,1674,1675,1678,1679,1680,1683,1686,1689,1692,1695,1696,1697,1698,1699][i - 1183]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1183 + (i - 1183)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1183 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1183).take (i - 1183))).length :=
      instructionPC_add Artifact.submissionArtifact 1183 (i - 1183)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1223 ≤ i) (hii : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1700,1703,1704,1705,1706,1707,1708,1711,1712,1713,1714,1715,1716,1717,1718,1719,1722,1723,1724,1727,1728,1731,1732,1733,1734,1737,1738,1739,1741,1742,1743,1744,1747,1748][i - 1223]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1223 + (i - 1223)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1223 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1223).take (i - 1223))).length :=
      instructionPC_add Artifact.submissionArtifact 1223 (i - 1223)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1257 ≤ i) (hii : i ≤ 1295) :
    Artifact.submissionArtifact.instructionPC i =
      [1749,1750,1751,1752,1755,1756,1757,1759,1760,1761,1764,1765,1766,1767,1768,1770,1771,1772,1774,1775,1776,1777,1778,1779,1780,1782,1783,1784,1785,1786,1787,1788,1789,1790,1793,1794,1795,1798,1799][i - 1257]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1257 + (i - 1257)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1257 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1257).take (i - 1257))).length :=
      instructionPC_add Artifact.submissionArtifact 1257 (i - 1257)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1296 ≤ i) (hii : i ≤ 1332) :
    Artifact.submissionArtifact.instructionPC i =
      [1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836][i - 1296]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1296 + (i - 1296)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1296 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1296).take (i - 1296))).length :=
      instructionPC_add Artifact.submissionArtifact 1296 (i - 1296)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1333 ≤ i) (hii : i ≤ 1375) :
    Artifact.submissionArtifact.instructionPC i =
      [1837,1838,1840,1841,1842,1843,1845,1846,1847,1848,1849,1850,1851,1854,1855,1856,1857,1858,1861,1862,1863,1864,1867,1868,1869,1872,1873,1876,1877,1878,1881,1882,1883,1884,1887,1888,1889,1890,1891,1892,1893,1894,1895][i - 1333]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1333 + (i - 1333)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1333 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1333).take (i - 1333))).length :=
      instructionPC_add Artifact.submissionArtifact 1333 (i - 1333)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1376 ≤ i) (hii : i ≤ 1416) :
    Artifact.submissionArtifact.instructionPC i =
      [1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1911,1912,1914,1915,1916,1919,1920,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942][i - 1376]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1376 + (i - 1376)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1376 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1376).take (i - 1376))).length :=
      instructionPC_add Artifact.submissionArtifact 1376 (i - 1376)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1417 ≤ i) (hii : i ≤ 1452) :
    Artifact.submissionArtifact.instructionPC i =
      [1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1958,1959,1961,1962,1963,1964,1965,1966,1968,1969,1970,1973,1974,1975,1978,1979,1980,1981,1982,1983,1984,1985][i - 1417]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1417 + (i - 1417)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1417 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1417).take (i - 1417))).length :=
      instructionPC_add Artifact.submissionArtifact 1417 (i - 1417)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1453 ≤ i) (hii : i ≤ 1493) :
    Artifact.submissionArtifact.instructionPC i =
      [1988,1989,1990,1991,1994,1995,1996,1999,2000,2001,2004,2005,2007,2008,2009,2010,2011,2012,2015,2016,2017,2018,2019,2022,2023,2024,2027,2028,2029,2030,2031,2033,2034,2035,2036,2037,2038,2040,2041,2042,2043][i - 1453]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1453 + (i - 1453)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1453 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1453).take (i - 1453))).length :=
      instructionPC_add Artifact.submissionArtifact 1453 (i - 1453)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1494 ≤ i) (hii : i ≤ 1534) :
    Artifact.submissionArtifact.instructionPC i =
      [2044,2045,2046,2047,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2076,2077,2078,2079,2081,2082,2083,2084,2085,2087,2088,2089][i - 1494]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1494 + (i - 1494)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1494).take (i - 1494))).length :=
      instructionPC_add Artifact.submissionArtifact 1494 (i - 1494)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1535 ≤ i) (hii : i ≤ 1558) :
    Artifact.submissionArtifact.instructionPC i =
      [2090,2093,2094,2095,2098,2099,2100,2101,2102,2105,2106,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121][i - 1535]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1535 + (i - 1535)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1535 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1535).take (i - 1535))).length :=
      instructionPC_add Artifact.submissionArtifact 1535 (i - 1535)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1559 ≤ i) (hii : i ≤ 1601) :
    Artifact.submissionArtifact.instructionPC i =
      [2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2135,2136,2137,2138,2140,2141,2142,2143,2144,2146,2147,2148,2149,2152,2153,2154,2157,2158,2159,2160,2161,2162,2165,2166,2167,2170,2171,2172,2175,2176,2179][i - 1559]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1559 + (i - 1559)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1559 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1559).take (i - 1559))).length :=
      instructionPC_add Artifact.submissionArtifact 1559 (i - 1559)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1602 ≤ i) (hii : i ≤ 1604) :
    Artifact.submissionArtifact.instructionPC i =
      [2180,2181,2182][i - 1602]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1602 + (i - 1602)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1602 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1602).take (i - 1602))).length :=
      instructionPC_add Artifact.submissionArtifact 1602 (i - 1602)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1605 ≤ i) (hii : i ≤ 1621) :
    Artifact.submissionArtifact.instructionPC i =
      [2183,2184,2187,2188,2189,2190,2193,2194,2195,2196,2197,2198,2199,2202,2203,2204,2205][i - 1605]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1605 + (i - 1605)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take (i - 1605))).length :=
      instructionPC_add Artifact.submissionArtifact 1605 (i - 1605)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1622 ≤ i) (hii : i ≤ 1634) :
    Artifact.submissionArtifact.instructionPC i =
      [2206,2207,2208,2209,2211,2212,2213,2216,2217,2219,2222,2223,2226][i - 1622]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1622 + (i - 1622)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1622 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1622).take (i - 1622))).length :=
      instructionPC_add Artifact.submissionArtifact 1622 (i - 1622)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1635 ≤ i) (hii : i ≤ 1669) :
    Artifact.submissionArtifact.instructionPC i =
      [2227,2228,2229,2232,2233,2234,2235,2236,2237,2238,2239,2242,2243,2245,2248,2249,2250,2251,2252,2254,2255,2256,2257,2259,2260,2261,2262,2264,2265,2266,2268,2269,2271,2272,2275][i - 1635]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1635 + (i - 1635)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1635 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1635).take (i - 1635))).length :=
      instructionPC_add Artifact.submissionArtifact 1635 (i - 1635)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1670 ≤ i) (hii : i ≤ 1681) :
    Artifact.submissionArtifact.instructionPC i =
      [2276,2277,2278,2281,2282,2285,2286,2289,2292,2293,2296,2299][i - 1670]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1670 + (i - 1670)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1670 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1670).take (i - 1670))).length :=
      instructionPC_add Artifact.submissionArtifact 1670 (i - 1670)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2282 ≤ i) (hii : i ≤ 2327) :
    Artifact.submissionArtifact.instructionPC i =
      [3005,3006,3007,3008,3009,3010,3011,3013,3014,3015,3016,3019,3020,3021,3023,3026,3027,3030,3033,3036,3039,3042,3043,3044,3045,3047,3048,3050,3051,3052,3053,3055,3056,3057,3059,3060,3062,3063,3064,3065,3066,3068,3069,3070,3072,3075][i - 2282]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2282 + (i - 2282)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2282 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2282).take (i - 2282))).length :=
      instructionPC_add Artifact.submissionArtifact 2282 (i - 2282)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 888 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1430 = true :=
  Artifact.isValidJumpDest_index 1070 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1452 = true :=
  Artifact.isValidJumpDest_index 1080 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  Artifact.isValidJumpDest_index 1087 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1486 = true :=
  Artifact.isValidJumpDest_index 1099 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1501 = true :=
  Artifact.isValidJumpDest_index 1110 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1513 = true :=
  Artifact.isValidJumpDest_index 1118 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1537 = true :=
  Artifact.isValidJumpDest_index 1130 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1572 = true :=
  Artifact.isValidJumpDest_index 1151 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1580 = true :=
  Artifact.isValidJumpDest_index 1156 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1165 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3265 = true :=
  Artifact.isValidJumpDest_index 2481 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1165 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1611 = true :=
  Artifact.isValidJumpDest_index 1173 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1626 = true :=
  Artifact.isValidJumpDest_index 1180 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1651 = true :=
  Artifact.isValidJumpDest_index 1193 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1652 = true :=
  Artifact.isValidJumpDest_index 1194 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1670 = true :=
  Artifact.isValidJumpDest_index 1206 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1696 = true :=
  Artifact.isValidJumpDest_index 1219 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1706 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1712 = true :=
  Artifact.isValidJumpDest_index 1231 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1723 = true :=
  Artifact.isValidJumpDest_index 1240 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1727 = true :=
  Artifact.isValidJumpDest_index 1242 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1738 = true :=
  Artifact.isValidJumpDest_index 1249 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1751 = true :=
  Artifact.isValidJumpDest_index 1259 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1786 = true :=
  Artifact.isValidJumpDest_index 1286 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1800 = true :=
  Artifact.isValidJumpDest_index 1296 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1924 = true :=
  Artifact.isValidJumpDest_index 1398 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2023 = true :=
  Artifact.isValidJumpDest_index 1477 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2054 = true :=
  Artifact.isValidJumpDest_index 1502 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2110 = true :=
  Artifact.isValidJumpDest_index 1547 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2183 = true :=
  Artifact.isValidJumpDest_index 1605 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2194 = true :=
  Artifact.isValidJumpDest_index 1612 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2206 = true :=
  Artifact.isValidJumpDest_index 1622 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2227 = true :=
  Artifact.isValidJumpDest_index 1635 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2249 = true :=
  Artifact.isValidJumpDest_index 1650 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2276 = true :=
  Artifact.isValidJumpDest_index 1670 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2970 = true :=
  Artifact.isValidJumpDest_index 2259 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3005 = true :=
  Artifact.isValidJumpDest_index 2282 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3043 = true :=
  Artifact.isValidJumpDest_index 2304 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4875 = true :=
  Artifact.isValidJumpDest_index 3734 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5030 = true :=
  Artifact.isValidJumpDest_index 3848 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5281 = true :=
  Artifact.isValidJumpDest_index 4029 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5270 = true :=
  Artifact.isValidJumpDest_index 4022 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
