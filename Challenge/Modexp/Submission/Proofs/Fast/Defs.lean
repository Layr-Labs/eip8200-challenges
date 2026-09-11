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
    Artifact.submissionArtifact.instructionPC 935 = 1233 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 974 = 1289 := by
  calc
    Artifact.submissionArtifact.instructionPC 974 =
        Artifact.submissionArtifact.instructionPC 935 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 935).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 935 39
    _ = 1289 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1013 = 1345 := by
  calc
    Artifact.submissionArtifact.instructionPC 1013 =
        Artifact.submissionArtifact.instructionPC 974 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 974).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 974 39
    _ = 1345 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1049 = 1388 := by
  calc
    Artifact.submissionArtifact.instructionPC 1049 =
        Artifact.submissionArtifact.instructionPC 1013 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1013).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1013 36
    _ = 1388 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1089 = 1444 := by
  calc
    Artifact.submissionArtifact.instructionPC 1089 =
        Artifact.submissionArtifact.instructionPC 1049 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1049).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1049 40
    _ = 1444 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1119 = 1503 := by
  calc
    Artifact.submissionArtifact.instructionPC 1119 =
        Artifact.submissionArtifact.instructionPC 1089 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1089).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1089 30
    _ = 1503 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1139 = 1531 := by
  calc
    Artifact.submissionArtifact.instructionPC 1139 =
        Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1119 20
    _ = 1531 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1178 = 1599 := by
  calc
    Artifact.submissionArtifact.instructionPC 1178 =
        Artifact.submissionArtifact.instructionPC 1139 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1139).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1139 39
    _ = 1599 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1207 = 1654 := by
  calc
    Artifact.submissionArtifact.instructionPC 1207 =
        Artifact.submissionArtifact.instructionPC 1178 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1178).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 1178 29
    _ = 1654 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1247 = 1725 := by
  calc
    Artifact.submissionArtifact.instructionPC 1247 =
        Artifact.submissionArtifact.instructionPC 1207 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1207).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1207 40
    _ = 1725 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1287 = 1782 := by
  calc
    Artifact.submissionArtifact.instructionPC 1287 =
        Artifact.submissionArtifact.instructionPC 1247 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1247).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1247 40
    _ = 1782 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1326 = 1833 := by
  calc
    Artifact.submissionArtifact.instructionPC 1326 =
        Artifact.submissionArtifact.instructionPC 1287 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1287).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1287 39
    _ = 1833 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1363 = 1870 := by
  calc
    Artifact.submissionArtifact.instructionPC 1363 =
        Artifact.submissionArtifact.instructionPC 1326 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1326).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1326 37
    _ = 1870 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1406 = 1929 := by
  calc
    Artifact.submissionArtifact.instructionPC 1406 =
        Artifact.submissionArtifact.instructionPC 1363 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1363).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1363 43
    _ = 1929 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1447 = 1976 := by
  calc
    Artifact.submissionArtifact.instructionPC 1447 =
        Artifact.submissionArtifact.instructionPC 1406 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1406).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1406 41
    _ = 1976 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1483 = 2021 := by
  calc
    Artifact.submissionArtifact.instructionPC 1483 =
        Artifact.submissionArtifact.instructionPC 1447 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1447).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1447 36
    _ = 2021 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1524 = 2077 := by
  calc
    Artifact.submissionArtifact.instructionPC 1524 =
        Artifact.submissionArtifact.instructionPC 1483 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1483).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1483 41
    _ = 2077 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1565 = 2123 := by
  calc
    Artifact.submissionArtifact.instructionPC 1565 =
        Artifact.submissionArtifact.instructionPC 1524 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1524).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1524 41
    _ = 2123 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1590 = 2156 := by
  calc
    Artifact.submissionArtifact.instructionPC 1590 =
        Artifact.submissionArtifact.instructionPC 1565 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1565).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 1565 25
    _ = 2156 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1633 = 2214 := by
  calc
    Artifact.submissionArtifact.instructionPC 1633 =
        Artifact.submissionArtifact.instructionPC 1590 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1590).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1590 43
    _ = 2214 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1636 = 2217 := by
  calc
    Artifact.submissionArtifact.instructionPC 1636 =
        Artifact.submissionArtifact.instructionPC 1633 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1633).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1633 3
    _ = 2217 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1654 = 2241 := by
  calc
    Artifact.submissionArtifact.instructionPC 1654 =
        Artifact.submissionArtifact.instructionPC 1636 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1636).take 18)).length :=
      instructionPC_add Artifact.submissionArtifact 1636 18
    _ = 2241 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1667 = 2262 := by
  calc
    Artifact.submissionArtifact.instructionPC 1667 =
        Artifact.submissionArtifact.instructionPC 1654 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1654).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1654 13
    _ = 2262 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1702 = 2311 := by
  calc
    Artifact.submissionArtifact.instructionPC 1702 =
        Artifact.submissionArtifact.instructionPC 1667 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1667).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1667 35
    _ = 2311 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2350 = 3058 := by
  calc
    Artifact.submissionArtifact.instructionPC 2350 =
        Artifact.submissionArtifact.instructionPC 1702 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1702).take 648)).length :=
      instructionPC_add Artifact.submissionArtifact 1702 648
    _ = 3058 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 935 ≤ i) (hii : i ≤ 973) :
    Artifact.submissionArtifact.instructionPC i =
      [1233, 1234, 1236, 1237, 1238, 1240, 1241, 1244, 1245, 1247, 1248, 1249, 1250, 1251, 1254, 1255, 1256, 1259, 1260, 1261, 1262, 1265, 1266, 1267, 1270, 1271, 1272, 1274, 1275, 1277, 1278, 1279, 1281, 1282, 1283, 1284, 1285, 1287, 1288][i - 935]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (935 + (i - 935)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 935 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 935).take (i - 935))).length :=
      instructionPC_add Artifact.submissionArtifact 935 (i - 935)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 974 ≤ i) (hii : i ≤ 1012) :
    Artifact.submissionArtifact.instructionPC i =
      [1289, 1290, 1291, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1302, 1303, 1305, 1306, 1307, 1308, 1309, 1310, 1312, 1313, 1314, 1317, 1318, 1319, 1322, 1323, 1324, 1327, 1328, 1329, 1331, 1332, 1335, 1336, 1338, 1339, 1340, 1341, 1344][i - 974]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (974 + (i - 974)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 974 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 974).take (i - 974))).length :=
      instructionPC_add Artifact.submissionArtifact 974 (i - 974)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1013 ≤ i) (hii : i ≤ 1048) :
    Artifact.submissionArtifact.instructionPC i =
      [1345, 1346, 1349, 1350, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1371, 1372, 1373, 1374, 1375, 1377, 1378, 1379, 1380, 1381, 1382, 1384, 1385, 1386, 1387][i - 1013]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1013 + (i - 1013)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1013 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1013).take (i - 1013))).length :=
      instructionPC_add Artifact.submissionArtifact 1013 (i - 1013)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1049 ≤ i) (hii : i ≤ 1088) :
    Artifact.submissionArtifact.instructionPC i =
      [1388, 1389, 1391, 1392, 1393, 1394, 1395, 1396, 1398, 1399, 1400, 1401, 1402, 1403, 1405, 1406, 1407, 1408, 1409, 1410, 1412, 1413, 1414, 1415, 1416, 1417, 1419, 1420, 1421, 1422, 1423, 1426, 1427, 1428, 1429, 1431, 1434, 1435, 1438, 1441][i - 1049]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1049 + (i - 1049)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1049 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1049).take (i - 1049))).length :=
      instructionPC_add Artifact.submissionArtifact 1049 (i - 1049)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1089 ≤ i) (hii : i ≤ 1118) :
    Artifact.submissionArtifact.instructionPC i =
      [1444, 1445, 1446, 1449, 1450, 1453, 1456, 1457, 1460, 1463, 1466, 1467, 1468, 1471, 1474, 1477, 1480, 1483, 1484, 1485, 1486, 1487, 1488, 1490, 1491, 1494, 1495, 1498, 1499, 1502][i - 1089]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1089 + (i - 1089)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1089 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1089).take (i - 1089))).length :=
      instructionPC_add Artifact.submissionArtifact 1089 (i - 1089)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1119 ≤ i) (hii : i ≤ 1138) :
    Artifact.submissionArtifact.instructionPC i =
      [1503, 1504, 1505, 1506, 1507, 1510, 1511, 1512, 1513, 1514, 1517, 1518, 1519, 1520, 1521, 1522, 1525, 1526, 1529, 1530][i - 1119]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1119 + (i - 1119)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take (i - 1119))).length :=
      instructionPC_add Artifact.submissionArtifact 1119 (i - 1119)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1139 ≤ i) (hii : i ≤ 1177) :
    Artifact.submissionArtifact.instructionPC i =
      [1531, 1532, 1533, 1534, 1537, 1538, 1541, 1544, 1547, 1550, 1553, 1554, 1555, 1556, 1557, 1558, 1560, 1561, 1562, 1563, 1565, 1566, 1567, 1568, 1571, 1572, 1573, 1576, 1579, 1582, 1585, 1588, 1589, 1590, 1592, 1593, 1596, 1597, 1598][i - 1139]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1139 + (i - 1139)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1139 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1139).take (i - 1139))).length :=
      instructionPC_add Artifact.submissionArtifact 1139 (i - 1139)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1178 ≤ i) (hii : i ≤ 1206) :
    Artifact.submissionArtifact.instructionPC i =
      [1599, 1600, 1603, 1606, 1609, 1612, 1615, 1616, 1617, 1618, 1621, 1622, 1623, 1624, 1625, 1626, 1629, 1630, 1633, 1634, 1635, 1638, 1641, 1644, 1647, 1650, 1651, 1652, 1653][i - 1178]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1178 + (i - 1178)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1178 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1178).take (i - 1178))).length :=
      instructionPC_add Artifact.submissionArtifact 1178 (i - 1178)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1207 ≤ i) (hii : i ≤ 1246) :
    Artifact.submissionArtifact.instructionPC i =
      [1654, 1655, 1656, 1659, 1660, 1663, 1666, 1669, 1672, 1675, 1676, 1677, 1678, 1680, 1681, 1682, 1685, 1686, 1687, 1688, 1690, 1691, 1694, 1695, 1696, 1697, 1699, 1700, 1703, 1704, 1705, 1708, 1711, 1714, 1717, 1720, 1721, 1722, 1723, 1724][i - 1207]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1207 + (i - 1207)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1207 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1207).take (i - 1207))).length :=
      instructionPC_add Artifact.submissionArtifact 1207 (i - 1207)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1247 ≤ i) (hii : i ≤ 1286) :
    Artifact.submissionArtifact.instructionPC i =
      [1725, 1728, 1729, 1730, 1731, 1732, 1733, 1736, 1737, 1738, 1739, 1740, 1741, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1755, 1756, 1757, 1760, 1761, 1764, 1765, 1766, 1767, 1770, 1771, 1772, 1774, 1775, 1776, 1777, 1780, 1781][i - 1247]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1247 + (i - 1247)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1247 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1247).take (i - 1247))).length :=
      instructionPC_add Artifact.submissionArtifact 1247 (i - 1247)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1287 ≤ i) (hii : i ≤ 1325) :
    Artifact.submissionArtifact.instructionPC i =
      [1782, 1783, 1784, 1785, 1788, 1789, 1790, 1792, 1793, 1794, 1797, 1798, 1799, 1800, 1801, 1803, 1804, 1805, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1826, 1827, 1828, 1831, 1832][i - 1287]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1287 + (i - 1287)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1287 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1287).take (i - 1287))).length :=
      instructionPC_add Artifact.submissionArtifact 1287 (i - 1287)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1326 ≤ i) (hii : i ≤ 1362) :
    Artifact.submissionArtifact.instructionPC i =
      [1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869][i - 1326]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1326 + (i - 1326)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1326 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1326).take (i - 1326))).length :=
      instructionPC_add Artifact.submissionArtifact 1326 (i - 1326)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1363 ≤ i) (hii : i ≤ 1405) :
    Artifact.submissionArtifact.instructionPC i =
      [1870, 1871, 1873, 1874, 1875, 1876, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1887, 1888, 1889, 1890, 1891, 1894, 1895, 1896, 1897, 1900, 1901, 1902, 1905, 1906, 1909, 1910, 1911, 1914, 1915, 1916, 1917, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928][i - 1363]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1363 + (i - 1363)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1363 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1363).take (i - 1363))).length :=
      instructionPC_add Artifact.submissionArtifact 1363 (i - 1363)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1406 ≤ i) (hii : i ≤ 1446) :
    Artifact.submissionArtifact.instructionPC i =
      [1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1944, 1945, 1947, 1948, 1949, 1952, 1953, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975][i - 1406]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1406 + (i - 1406)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1406 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1406).take (i - 1406))).length :=
      instructionPC_add Artifact.submissionArtifact 1406 (i - 1406)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1447 ≤ i) (hii : i ≤ 1482) :
    Artifact.submissionArtifact.instructionPC i =
      [1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1991, 1992, 1994, 1995, 1996, 1997, 1998, 1999, 2001, 2002, 2003, 2006, 2007, 2008, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018][i - 1447]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1447 + (i - 1447)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1447 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1447).take (i - 1447))).length :=
      instructionPC_add Artifact.submissionArtifact 1447 (i - 1447)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1483 ≤ i) (hii : i ≤ 1523) :
    Artifact.submissionArtifact.instructionPC i =
      [2021, 2022, 2023, 2024, 2027, 2028, 2029, 2032, 2033, 2034, 2037, 2038, 2040, 2041, 2042, 2043, 2044, 2045, 2048, 2049, 2050, 2051, 2052, 2055, 2056, 2057, 2060, 2061, 2062, 2063, 2064, 2066, 2067, 2068, 2069, 2070, 2071, 2073, 2074, 2075, 2076][i - 1483]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1483 + (i - 1483)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1483 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1483).take (i - 1483))).length :=
      instructionPC_add Artifact.submissionArtifact 1483 (i - 1483)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1524 ≤ i) (hii : i ≤ 1564) :
    Artifact.submissionArtifact.instructionPC i =
      [2077, 2078, 2079, 2080, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095, 2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2109, 2110, 2111, 2112, 2114, 2115, 2116, 2117, 2118, 2120, 2121, 2122][i - 1524]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1524 + (i - 1524)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1524 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1524).take (i - 1524))).length :=
      instructionPC_add Artifact.submissionArtifact 1524 (i - 1524)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1565 ≤ i) (hii : i ≤ 1589) :
    Artifact.submissionArtifact.instructionPC i =
      [2123, 2126, 2127, 2128, 2131, 2132, 2133, 2134, 2135, 2138, 2139, 2140, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155][i - 1565]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1565 + (i - 1565)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1565 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1565).take (i - 1565))).length :=
      instructionPC_add Artifact.submissionArtifact 1565 (i - 1565)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1590 ≤ i) (hii : i ≤ 1632) :
    Artifact.submissionArtifact.instructionPC i =
      [2156, 2157, 2158, 2159, 2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2169, 2170, 2171, 2172, 2174, 2175, 2176, 2177, 2178, 2180, 2181, 2182, 2183, 2186, 2187, 2188, 2191, 2192, 2193, 2194, 2195, 2196, 2199, 2200, 2201, 2204, 2205, 2206, 2209, 2210, 2213][i - 1590]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1590 + (i - 1590)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1590 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1590).take (i - 1590))).length :=
      instructionPC_add Artifact.submissionArtifact 1590 (i - 1590)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1633 ≤ i) (hii : i ≤ 1635) :
    Artifact.submissionArtifact.instructionPC i =
      [2214, 2215, 2216][i - 1633]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1633 + (i - 1633)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1633 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1633).take (i - 1633))).length :=
      instructionPC_add Artifact.submissionArtifact 1633 (i - 1633)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1636 ≤ i) (hii : i ≤ 1653) :
    Artifact.submissionArtifact.instructionPC i =
      [2217, 2218, 2219, 2222, 2223, 2224, 2225, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2237, 2238, 2239, 2240][i - 1636]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1636 + (i - 1636)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1636 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1636).take (i - 1636))).length :=
      instructionPC_add Artifact.submissionArtifact 1636 (i - 1636)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1654 ≤ i) (hii : i ≤ 1666) :
    Artifact.submissionArtifact.instructionPC i =
      [2241, 2242, 2243, 2244, 2246, 2247, 2248, 2251, 2252, 2254, 2257, 2258, 2261][i - 1654]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1654 + (i - 1654)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1654 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1654).take (i - 1654))).length :=
      instructionPC_add Artifact.submissionArtifact 1654 (i - 1654)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1667 ≤ i) (hii : i ≤ 1701) :
    Artifact.submissionArtifact.instructionPC i =
      [2262, 2263, 2264, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2277, 2278, 2280, 2283, 2284, 2285, 2286, 2287, 2289, 2290, 2291, 2292, 2294, 2295, 2296, 2297, 2299, 2300, 2301, 2303, 2304, 2306, 2307, 2310][i - 1667]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1667 + (i - 1667)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1667 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1667).take (i - 1667))).length :=
      instructionPC_add Artifact.submissionArtifact 1667 (i - 1667)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1702 ≤ i) (hii : i ≤ 1713) :
    Artifact.submissionArtifact.instructionPC i =
      [2311, 2312, 2313, 2316, 2317, 2320, 2321, 2324, 2327, 2328, 2331, 2334][i - 1702]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1702 + (i - 1702)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1702 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1702).take (i - 1702))).length :=
      instructionPC_add Artifact.submissionArtifact 1702 (i - 1702)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2350 ≤ i) (hii : i ≤ 2395) :
    Artifact.submissionArtifact.instructionPC i =
      [3058, 3059, 3060, 3061, 3062, 3063, 3064, 3066, 3067, 3068, 3069, 3072, 3073, 3074, 3076, 3079, 3080, 3083, 3086, 3089, 3092, 3095, 3096, 3097, 3098, 3100, 3101, 3103, 3104, 3105, 3106, 3108, 3109, 3110, 3112, 3113, 3115, 3116, 3117, 3118, 3119, 3122, 3123, 3124, 3126, 3129][i - 2350]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2350 + (i - 2350)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2350 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2350).take (i - 2350))).length :=
      instructionPC_add Artifact.submissionArtifact 2350 (i - 2350)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1134 = true :=
  Artifact.isValidJumpDest_index 870 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1445 = true :=
  Artifact.isValidJumpDest_index 1090 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  Artifact.isValidJumpDest_index 1100 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1484 = true :=
  Artifact.isValidJumpDest_index 1107 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1503 = true :=
  Artifact.isValidJumpDest_index 1119 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1518 = true :=
  Artifact.isValidJumpDest_index 1130 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1530 = true :=
  Artifact.isValidJumpDest_index 1138 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1554 = true :=
  Artifact.isValidJumpDest_index 1150 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1589 = true :=
  Artifact.isValidJumpDest_index 1171 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1597 = true :=
  Artifact.isValidJumpDest_index 1176 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1616 = true :=
  Artifact.isValidJumpDest_index 1185 (by rfl)

theorem jumpDest1698 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1617 = true :=
  Artifact.isValidJumpDest_index 1186 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1622 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1634 = true :=
  Artifact.isValidJumpDest_index 1197 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1651 = true :=
  Artifact.isValidJumpDest_index 1204 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1676 = true :=
  Artifact.isValidJumpDest_index 1217 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1677 = true :=
  Artifact.isValidJumpDest_index 1218 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1695 = true :=
  Artifact.isValidJumpDest_index 1230 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1721 = true :=
  Artifact.isValidJumpDest_index 1243 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1731 = true :=
  Artifact.isValidJumpDest_index 1251 (by rfl)

theorem jumpDest1818 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1745 = true :=
  Artifact.isValidJumpDest_index 1261 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1756 = true :=
  Artifact.isValidJumpDest_index 1270 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1760 = true :=
  Artifact.isValidJumpDest_index 1272 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1771 = true :=
  Artifact.isValidJumpDest_index 1279 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1784 = true :=
  Artifact.isValidJumpDest_index 1289 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1819 = true :=
  Artifact.isValidJumpDest_index 1316 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1833 = true :=
  Artifact.isValidJumpDest_index 1326 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1957 = true :=
  Artifact.isValidJumpDest_index 1428 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2056 = true :=
  Artifact.isValidJumpDest_index 1507 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2087 = true :=
  Artifact.isValidJumpDest_index 1532 (by rfl)

theorem jumpDest2220 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2139 = true :=
  Artifact.isValidJumpDest_index 1575 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2144 = true :=
  Artifact.isValidJumpDest_index 1578 (by rfl)

theorem jumpDest2298 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2217 = true :=
  Artifact.isValidJumpDest_index 1636 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2218 = true :=
  Artifact.isValidJumpDest_index 1637 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2229 = true :=
  Artifact.isValidJumpDest_index 1644 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2241 = true :=
  Artifact.isValidJumpDest_index 1654 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2262 = true :=
  Artifact.isValidJumpDest_index 1667 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2284 = true :=
  Artifact.isValidJumpDest_index 1682 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2311 = true :=
  Artifact.isValidJumpDest_index 1702 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3023 = true :=
  Artifact.isValidJumpDest_index 2327 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3058 = true :=
  Artifact.isValidJumpDest_index 2350 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3096 = true :=
  Artifact.isValidJumpDest_index 2372 (by rfl)


theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4902 = true :=
  Artifact.isValidJumpDest_index 3737 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4930 = true :=
  Artifact.isValidJumpDest_index 3755 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
