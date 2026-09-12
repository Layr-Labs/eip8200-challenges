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
    Artifact.submissionArtifact.instructionPC 935 = 1256 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 964 = 1295 := by
  calc
    Artifact.submissionArtifact.instructionPC 964 =
        Artifact.submissionArtifact.instructionPC 935 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 935).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 935 29
    _ = 1295 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1001 = 1347 := by
  calc
    Artifact.submissionArtifact.instructionPC 1001 =
        Artifact.submissionArtifact.instructionPC 964 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 964).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 964 37
    _ = 1347 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1037 = 1390 := by
  calc
    Artifact.submissionArtifact.instructionPC 1037 =
        Artifact.submissionArtifact.instructionPC 1001 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1001).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1001 36
    _ = 1390 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1072 = 1434 := by
  calc
    Artifact.submissionArtifact.instructionPC 1072 =
        Artifact.submissionArtifact.instructionPC 1037 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1037).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1037 35
    _ = 1434 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1102 = 1491 := by
  calc
    Artifact.submissionArtifact.instructionPC 1102 =
        Artifact.submissionArtifact.instructionPC 1072 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1072).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1072 30
    _ = 1491 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1122 = 1519 := by
  calc
    Artifact.submissionArtifact.instructionPC 1122 =
        Artifact.submissionArtifact.instructionPC 1102 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1102).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1102 20
    _ = 1519 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1161 = 1587 := by
  calc
    Artifact.submissionArtifact.instructionPC 1161 =
        Artifact.submissionArtifact.instructionPC 1122 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1122).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1122 39
    _ = 1587 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1189 = 1639 := by
  calc
    Artifact.submissionArtifact.instructionPC 1189 =
        Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1161 28
    _ = 1639 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1229 = 1710 := by
  calc
    Artifact.submissionArtifact.instructionPC 1229 =
        Artifact.submissionArtifact.instructionPC 1189 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1189).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1189 40
    _ = 1710 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1263 = 1759 := by
  calc
    Artifact.submissionArtifact.instructionPC 1263 =
        Artifact.submissionArtifact.instructionPC 1229 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1229).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1229 34
    _ = 1759 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1302 = 1810 := by
  calc
    Artifact.submissionArtifact.instructionPC 1302 =
        Artifact.submissionArtifact.instructionPC 1263 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1263).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1263 39
    _ = 1810 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1339 = 1847 := by
  calc
    Artifact.submissionArtifact.instructionPC 1339 =
        Artifact.submissionArtifact.instructionPC 1302 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1302).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1302 37
    _ = 1847 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1382 = 1906 := by
  calc
    Artifact.submissionArtifact.instructionPC 1382 =
        Artifact.submissionArtifact.instructionPC 1339 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1339).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1339 43
    _ = 1906 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1423 = 1953 := by
  calc
    Artifact.submissionArtifact.instructionPC 1423 =
        Artifact.submissionArtifact.instructionPC 1382 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1382).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1382 41
    _ = 1953 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1459 = 1998 := by
  calc
    Artifact.submissionArtifact.instructionPC 1459 =
        Artifact.submissionArtifact.instructionPC 1423 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1423).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1423 36
    _ = 1998 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1500 = 2054 := by
  calc
    Artifact.submissionArtifact.instructionPC 1500 =
        Artifact.submissionArtifact.instructionPC 1459 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1459).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1459 41
    _ = 2054 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1541 = 2100 := by
  calc
    Artifact.submissionArtifact.instructionPC 1541 =
        Artifact.submissionArtifact.instructionPC 1500 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1500).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1500 41
    _ = 2100 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1565 = 2132 := by
  calc
    Artifact.submissionArtifact.instructionPC 1565 =
        Artifact.submissionArtifact.instructionPC 1541 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1541).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1541 24
    _ = 2132 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1608 = 2190 := by
  calc
    Artifact.submissionArtifact.instructionPC 1608 =
        Artifact.submissionArtifact.instructionPC 1565 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1565).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1565 43
    _ = 2190 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1611 = 2193 := by
  calc
    Artifact.submissionArtifact.instructionPC 1611 =
        Artifact.submissionArtifact.instructionPC 1608 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1608).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1608 3
    _ = 2193 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1628 = 2216 := by
  calc
    Artifact.submissionArtifact.instructionPC 1628 =
        Artifact.submissionArtifact.instructionPC 1611 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1611).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1611 17
    _ = 2216 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1641 = 2237 := by
  calc
    Artifact.submissionArtifact.instructionPC 1641 =
        Artifact.submissionArtifact.instructionPC 1628 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1628).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1628 13
    _ = 2237 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1676 = 2286 := by
  calc
    Artifact.submissionArtifact.instructionPC 1676 =
        Artifact.submissionArtifact.instructionPC 1641 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1641).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1641 35
    _ = 2286 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2304 = 3007 := by
  calc
    Artifact.submissionArtifact.instructionPC 2304 =
        Artifact.submissionArtifact.instructionPC 1676 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1676).take 628)).length :=
      instructionPC_add Artifact.submissionArtifact 1676 628
    _ = 3007 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 935 ≤ i) (hii : i ≤ 963) :
    Artifact.submissionArtifact.instructionPC i =
      [1256, 1257, 1259, 1260, 1261, 1263, 1264, 1265, 1267, 1268, 1271, 1272, 1274, 1275, 1276, 1277, 1278, 1280, 1281, 1283, 1284, 1285, 1287, 1288, 1289, 1290, 1291, 1293, 1294][i - 935]! := by
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

@[simp] theorem fastPC1 (i : Nat) (hi : 964 ≤ i) (hii : i ≤ 1000) :
    Artifact.submissionArtifact.instructionPC i =
      [1295, 1296, 1297, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1308, 1309, 1311, 1312, 1313, 1314, 1315, 1316, 1318, 1319, 1320, 1323, 1324, 1325, 1328, 1329, 1330, 1331, 1333, 1334, 1337, 1338, 1340, 1341, 1342, 1343, 1346][i - 964]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (964 + (i - 964)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 964 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 964).take (i - 964))).length :=
      instructionPC_add Artifact.submissionArtifact 964 (i - 964)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 1001 ≤ i) (hii : i ≤ 1036) :
    Artifact.submissionArtifact.instructionPC i =
      [1347, 1348, 1351, 1352, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1373, 1374, 1375, 1376, 1377, 1379, 1380, 1381, 1382, 1383, 1384, 1386, 1387, 1388, 1389][i - 1001]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1001 + (i - 1001)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1001 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1001).take (i - 1001))).length :=
      instructionPC_add Artifact.submissionArtifact 1001 (i - 1001)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1037 ≤ i) (hii : i ≤ 1071) :
    Artifact.submissionArtifact.instructionPC i =
      [1390, 1391, 1393, 1394, 1395, 1396, 1397, 1398, 1400, 1401, 1402, 1403, 1404, 1405, 1407, 1408, 1409, 1410, 1411, 1412, 1414, 1415, 1416, 1417, 1418, 1419, 1421, 1422, 1423, 1424, 1425, 1428, 1429, 1430, 1431][i - 1037]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1037 + (i - 1037)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1037 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1037).take (i - 1037))).length :=
      instructionPC_add Artifact.submissionArtifact 1037 (i - 1037)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1072 ≤ i) (hii : i ≤ 1101) :
    Artifact.submissionArtifact.instructionPC i =
      [1434, 1435, 1436, 1439, 1440, 1443, 1446, 1447, 1450, 1453, 1456, 1457, 1458, 1461, 1464, 1465, 1468, 1471, 1472, 1473, 1474, 1475, 1476, 1479, 1480, 1482, 1483, 1486, 1487, 1490][i - 1072]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1072 + (i - 1072)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1072 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1072).take (i - 1072))).length :=
      instructionPC_add Artifact.submissionArtifact 1072 (i - 1072)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1102 ≤ i) (hii : i ≤ 1121) :
    Artifact.submissionArtifact.instructionPC i =
      [1491, 1492, 1493, 1494, 1495, 1498, 1499, 1500, 1501, 1502, 1505, 1506, 1507, 1508, 1509, 1510, 1513, 1514, 1517, 1518][i - 1102]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1102 + (i - 1102)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1102 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1102).take (i - 1102))).length :=
      instructionPC_add Artifact.submissionArtifact 1102 (i - 1102)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1122 ≤ i) (hii : i ≤ 1160) :
    Artifact.submissionArtifact.instructionPC i =
      [1519, 1520, 1521, 1522, 1525, 1526, 1529, 1532, 1535, 1538, 1541, 1542, 1543, 1544, 1545, 1546, 1548, 1549, 1550, 1551, 1553, 1554, 1555, 1556, 1559, 1560, 1561, 1564, 1567, 1570, 1573, 1576, 1577, 1578, 1580, 1581, 1584, 1585, 1586][i - 1122]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1122 + (i - 1122)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1122 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1122).take (i - 1122))).length :=
      instructionPC_add Artifact.submissionArtifact 1122 (i - 1122)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1161 ≤ i) (hii : i ≤ 1188) :
    Artifact.submissionArtifact.instructionPC i =
      [1587, 1588, 1591, 1594, 1597, 1600, 1603, 1604, 1605, 1608, 1609, 1610, 1611, 1612, 1613, 1616, 1617, 1620, 1621, 1622, 1625, 1628, 1629, 1632, 1635, 1636, 1637, 1638][i - 1161]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1161 + (i - 1161)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1161 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1161).take (i - 1161))).length :=
      instructionPC_add Artifact.submissionArtifact 1161 (i - 1161)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1189 ≤ i) (hii : i ≤ 1228) :
    Artifact.submissionArtifact.instructionPC i =
      [1639, 1640, 1641, 1644, 1645, 1648, 1651, 1654, 1657, 1660, 1661, 1662, 1663, 1665, 1666, 1667, 1670, 1671, 1672, 1673, 1675, 1676, 1679, 1680, 1681, 1682, 1684, 1685, 1688, 1689, 1690, 1693, 1696, 1699, 1702, 1705, 1706, 1707, 1708, 1709][i - 1189]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1189 + (i - 1189)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1189 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1189).take (i - 1189))).length :=
      instructionPC_add Artifact.submissionArtifact 1189 (i - 1189)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1229 ≤ i) (hii : i ≤ 1262) :
    Artifact.submissionArtifact.instructionPC i =
      [1710, 1713, 1714, 1715, 1716, 1717, 1718, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1732, 1733, 1734, 1737, 1738, 1741, 1742, 1743, 1744, 1747, 1748, 1749, 1751, 1752, 1753, 1754, 1757, 1758][i - 1229]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1229 + (i - 1229)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1229 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1229).take (i - 1229))).length :=
      instructionPC_add Artifact.submissionArtifact 1229 (i - 1229)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1263 ≤ i) (hii : i ≤ 1301) :
    Artifact.submissionArtifact.instructionPC i =
      [1759, 1760, 1761, 1762, 1765, 1766, 1767, 1769, 1770, 1771, 1774, 1775, 1776, 1777, 1778, 1780, 1781, 1782, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1803, 1804, 1805, 1808, 1809][i - 1263]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1263 + (i - 1263)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1263 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1263).take (i - 1263))).length :=
      instructionPC_add Artifact.submissionArtifact 1263 (i - 1263)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1302 ≤ i) (hii : i ≤ 1338) :
    Artifact.submissionArtifact.instructionPC i =
      [1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846][i - 1302]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1302 + (i - 1302)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1302 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1302).take (i - 1302))).length :=
      instructionPC_add Artifact.submissionArtifact 1302 (i - 1302)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1339 ≤ i) (hii : i ≤ 1381) :
    Artifact.submissionArtifact.instructionPC i =
      [1847, 1848, 1850, 1851, 1852, 1853, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1864, 1865, 1866, 1867, 1868, 1871, 1872, 1873, 1874, 1877, 1878, 1879, 1882, 1883, 1886, 1887, 1888, 1891, 1892, 1893, 1894, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905][i - 1339]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1339 + (i - 1339)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1339 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1339).take (i - 1339))).length :=
      instructionPC_add Artifact.submissionArtifact 1339 (i - 1339)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1382 ≤ i) (hii : i ≤ 1422) :
    Artifact.submissionArtifact.instructionPC i =
      [1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1921, 1922, 1924, 1925, 1926, 1929, 1930, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952][i - 1382]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1382 + (i - 1382)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1382 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1382).take (i - 1382))).length :=
      instructionPC_add Artifact.submissionArtifact 1382 (i - 1382)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1423 ≤ i) (hii : i ≤ 1458) :
    Artifact.submissionArtifact.instructionPC i =
      [1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1968, 1969, 1971, 1972, 1973, 1974, 1975, 1976, 1978, 1979, 1980, 1983, 1984, 1985, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995][i - 1423]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1423 + (i - 1423)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1423 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1423).take (i - 1423))).length :=
      instructionPC_add Artifact.submissionArtifact 1423 (i - 1423)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1459 ≤ i) (hii : i ≤ 1499) :
    Artifact.submissionArtifact.instructionPC i =
      [1998, 1999, 2000, 2001, 2004, 2005, 2006, 2009, 2010, 2011, 2014, 2015, 2017, 2018, 2019, 2020, 2021, 2022, 2025, 2026, 2027, 2028, 2029, 2032, 2033, 2034, 2037, 2038, 2039, 2040, 2041, 2043, 2044, 2045, 2046, 2047, 2048, 2050, 2051, 2052, 2053][i - 1459]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1459 + (i - 1459)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1459 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1459).take (i - 1459))).length :=
      instructionPC_add Artifact.submissionArtifact 1459 (i - 1459)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1500 ≤ i) (hii : i ≤ 1540) :
    Artifact.submissionArtifact.instructionPC i =
      [2054, 2055, 2056, 2057, 2060, 2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2086, 2087, 2088, 2089, 2091, 2092, 2093, 2094, 2095, 2097, 2098, 2099][i - 1500]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1500 + (i - 1500)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1500 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1500).take (i - 1500))).length :=
      instructionPC_add Artifact.submissionArtifact 1500 (i - 1500)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1541 ≤ i) (hii : i ≤ 1564) :
    Artifact.submissionArtifact.instructionPC i =
      [2100, 2103, 2104, 2105, 2108, 2109, 2110, 2111, 2112, 2115, 2116, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127, 2128, 2129, 2130, 2131][i - 1541]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1541 + (i - 1541)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1541 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1541).take (i - 1541))).length :=
      instructionPC_add Artifact.submissionArtifact 1541 (i - 1541)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1565 ≤ i) (hii : i ≤ 1607) :
    Artifact.submissionArtifact.instructionPC i =
      [2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143, 2145, 2146, 2147, 2148, 2150, 2151, 2152, 2153, 2154, 2156, 2157, 2158, 2159, 2162, 2163, 2164, 2167, 2168, 2169, 2170, 2171, 2172, 2175, 2176, 2177, 2180, 2181, 2182, 2185, 2186, 2189][i - 1565]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1565 + (i - 1565)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1565 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1565).take (i - 1565))).length :=
      instructionPC_add Artifact.submissionArtifact 1565 (i - 1565)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1608 ≤ i) (hii : i ≤ 1610) :
    Artifact.submissionArtifact.instructionPC i =
      [2190, 2191, 2192][i - 1608]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1608 + (i - 1608)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1608 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1608).take (i - 1608))).length :=
      instructionPC_add Artifact.submissionArtifact 1608 (i - 1608)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1611 ≤ i) (hii : i ≤ 1627) :
    Artifact.submissionArtifact.instructionPC i =
      [2193, 2194, 2197, 2198, 2199, 2200, 2203, 2204, 2205, 2206, 2207, 2208, 2209, 2212, 2213, 2214, 2215][i - 1611]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1611 + (i - 1611)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1611 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1611).take (i - 1611))).length :=
      instructionPC_add Artifact.submissionArtifact 1611 (i - 1611)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1628 ≤ i) (hii : i ≤ 1640) :
    Artifact.submissionArtifact.instructionPC i =
      [2216, 2217, 2218, 2219, 2221, 2222, 2223, 2226, 2227, 2229, 2232, 2233, 2236][i - 1628]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1628 + (i - 1628)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1628 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1628).take (i - 1628))).length :=
      instructionPC_add Artifact.submissionArtifact 1628 (i - 1628)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1641 ≤ i) (hii : i ≤ 1675) :
    Artifact.submissionArtifact.instructionPC i =
      [2237, 2238, 2239, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2252, 2253, 2255, 2258, 2259, 2260, 2261, 2262, 2264, 2265, 2266, 2267, 2269, 2270, 2271, 2272, 2274, 2275, 2276, 2278, 2279, 2281, 2282, 2285][i - 1641]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1641 + (i - 1641)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1641 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1641).take (i - 1641))).length :=
      instructionPC_add Artifact.submissionArtifact 1641 (i - 1641)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1676 ≤ i) (hii : i ≤ 1687) :
    Artifact.submissionArtifact.instructionPC i =
      [2286, 2287, 2288, 2291, 2292, 2295, 2296, 2299, 2302, 2303, 2306, 2309][i - 1676]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1676 + (i - 1676)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1676 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1676).take (i - 1676))).length :=
      instructionPC_add Artifact.submissionArtifact 1676 (i - 1676)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2304 ≤ i) (hii : i ≤ 2349) :
    Artifact.submissionArtifact.instructionPC i =
      [3007, 3008, 3009, 3010, 3011, 3012, 3013, 3015, 3016, 3017, 3018, 3021, 3022, 3023, 3025, 3028, 3029, 3032, 3035, 3038, 3041, 3044, 3045, 3046, 3047, 3049, 3050, 3052, 3053, 3054, 3055, 3057, 3058, 3059, 3061, 3062, 3064, 3065, 3066, 3067, 3068, 3071, 3072, 3073, 3075, 3078][i - 2304]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2304 + (i - 2304)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2304 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2304).take (i - 2304))).length :=
      instructionPC_add Artifact.submissionArtifact 2304 (i - 2304)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 888 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1435 = true :=
  Artifact.isValidJumpDest_index 1073 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1457 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1472 = true :=
  Artifact.isValidJumpDest_index 1090 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1491 = true :=
  Artifact.isValidJumpDest_index 1102 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1506 = true :=
  Artifact.isValidJumpDest_index 1113 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1518 = true :=
  Artifact.isValidJumpDest_index 1121 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1542 = true :=
  Artifact.isValidJumpDest_index 1133 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1577 = true :=
  Artifact.isValidJumpDest_index 1154 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1585 = true :=
  Artifact.isValidJumpDest_index 1159 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1604 = true :=
  Artifact.isValidJumpDest_index 1168 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3273 = true :=
  Artifact.isValidJumpDest_index 2506 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1609 = true :=
  Artifact.isValidJumpDest_index 1171 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1621 = true :=
  Artifact.isValidJumpDest_index 1179 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1636 = true :=
  Artifact.isValidJumpDest_index 1186 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1661 = true :=
  Artifact.isValidJumpDest_index 1199 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1662 = true :=
  Artifact.isValidJumpDest_index 1200 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1680 = true :=
  Artifact.isValidJumpDest_index 1212 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1706 = true :=
  Artifact.isValidJumpDest_index 1225 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1716 = true :=
  Artifact.isValidJumpDest_index 1233 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1722 = true :=
  Artifact.isValidJumpDest_index 1237 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1733 = true :=
  Artifact.isValidJumpDest_index 1246 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1248 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1748 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1761 = true :=
  Artifact.isValidJumpDest_index 1265 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1796 = true :=
  Artifact.isValidJumpDest_index 1292 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1810 = true :=
  Artifact.isValidJumpDest_index 1302 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1934 = true :=
  Artifact.isValidJumpDest_index 1404 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2033 = true :=
  Artifact.isValidJumpDest_index 1483 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2064 = true :=
  Artifact.isValidJumpDest_index 1508 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2120 = true :=
  Artifact.isValidJumpDest_index 1553 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2193 = true :=
  Artifact.isValidJumpDest_index 1611 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2204 = true :=
  Artifact.isValidJumpDest_index 1618 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2216 = true :=
  Artifact.isValidJumpDest_index 1628 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2237 = true :=
  Artifact.isValidJumpDest_index 1641 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2259 = true :=
  Artifact.isValidJumpDest_index 1656 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2286 = true :=
  Artifact.isValidJumpDest_index 1676 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2972 = true :=
  Artifact.isValidJumpDest_index 2281 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3007 = true :=
  Artifact.isValidJumpDest_index 2304 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3045 = true :=
  Artifact.isValidJumpDest_index 2326 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4804 = true :=
  Artifact.isValidJumpDest_index 3636 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4976 = true :=
  Artifact.isValidJumpDest_index 3764 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5227 = true :=
  Artifact.isValidJumpDest_index 3945 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5216 = true :=
  Artifact.isValidJumpDest_index 3938 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
