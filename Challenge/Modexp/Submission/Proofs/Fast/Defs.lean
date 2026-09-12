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
    Artifact.submissionArtifact.instructionPC 961 = 1291 := by
  calc
    Artifact.submissionArtifact.instructionPC 961 =
        Artifact.submissionArtifact.instructionPC 935 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 935).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 935 26
    _ = 1291 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 1000 = 1347 := by
  calc
    Artifact.submissionArtifact.instructionPC 1000 =
        Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 961 39
    _ = 1347 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 1036 = 1390 := by
  calc
    Artifact.submissionArtifact.instructionPC 1036 =
        Artifact.submissionArtifact.instructionPC 1000 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1000).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1000 36
    _ = 1390 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1071 = 1434 := by
  calc
    Artifact.submissionArtifact.instructionPC 1071 =
        Artifact.submissionArtifact.instructionPC 1036 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1036).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1036 35
    _ = 1434 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1101 = 1491 := by
  calc
    Artifact.submissionArtifact.instructionPC 1101 =
        Artifact.submissionArtifact.instructionPC 1071 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1071).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1071 30
    _ = 1491 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1121 = 1519 := by
  calc
    Artifact.submissionArtifact.instructionPC 1121 =
        Artifact.submissionArtifact.instructionPC 1101 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1101).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1101 20
    _ = 1519 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1160 = 1587 := by
  calc
    Artifact.submissionArtifact.instructionPC 1160 =
        Artifact.submissionArtifact.instructionPC 1121 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1121).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1121 39
    _ = 1587 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1188 = 1639 := by
  calc
    Artifact.submissionArtifact.instructionPC 1188 =
        Artifact.submissionArtifact.instructionPC 1160 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1160).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1160 28
    _ = 1639 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1228 = 1710 := by
  calc
    Artifact.submissionArtifact.instructionPC 1228 =
        Artifact.submissionArtifact.instructionPC 1188 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1188).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1188 40
    _ = 1710 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1262 = 1759 := by
  calc
    Artifact.submissionArtifact.instructionPC 1262 =
        Artifact.submissionArtifact.instructionPC 1228 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1228).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1228 34
    _ = 1759 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1301 = 1810 := by
  calc
    Artifact.submissionArtifact.instructionPC 1301 =
        Artifact.submissionArtifact.instructionPC 1262 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1262).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1262 39
    _ = 1810 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1338 = 1847 := by
  calc
    Artifact.submissionArtifact.instructionPC 1338 =
        Artifact.submissionArtifact.instructionPC 1301 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1301).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1301 37
    _ = 1847 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1381 = 1906 := by
  calc
    Artifact.submissionArtifact.instructionPC 1381 =
        Artifact.submissionArtifact.instructionPC 1338 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1338).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1338 43
    _ = 1906 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1422 = 1953 := by
  calc
    Artifact.submissionArtifact.instructionPC 1422 =
        Artifact.submissionArtifact.instructionPC 1381 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1381).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1381 41
    _ = 1953 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1458 = 1998 := by
  calc
    Artifact.submissionArtifact.instructionPC 1458 =
        Artifact.submissionArtifact.instructionPC 1422 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1422).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1422 36
    _ = 1998 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1499 = 2054 := by
  calc
    Artifact.submissionArtifact.instructionPC 1499 =
        Artifact.submissionArtifact.instructionPC 1458 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1458).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1458 41
    _ = 2054 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1540 = 2100 := by
  calc
    Artifact.submissionArtifact.instructionPC 1540 =
        Artifact.submissionArtifact.instructionPC 1499 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1499).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1499 41
    _ = 2100 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1564 = 2132 := by
  calc
    Artifact.submissionArtifact.instructionPC 1564 =
        Artifact.submissionArtifact.instructionPC 1540 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1540).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1540 24
    _ = 2132 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1607 = 2190 := by
  calc
    Artifact.submissionArtifact.instructionPC 1607 =
        Artifact.submissionArtifact.instructionPC 1564 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1564).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1564 43
    _ = 2190 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1610 = 2193 := by
  calc
    Artifact.submissionArtifact.instructionPC 1610 =
        Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1607).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1607 3
    _ = 2193 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1627 = 2216 := by
  calc
    Artifact.submissionArtifact.instructionPC 1627 =
        Artifact.submissionArtifact.instructionPC 1610 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1610).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1610 17
    _ = 2216 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1640 = 2237 := by
  calc
    Artifact.submissionArtifact.instructionPC 1640 =
        Artifact.submissionArtifact.instructionPC 1627 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1627).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1627 13
    _ = 2237 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1675 = 2286 := by
  calc
    Artifact.submissionArtifact.instructionPC 1675 =
        Artifact.submissionArtifact.instructionPC 1640 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1640).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1640 35
    _ = 2286 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2303 = 3007 := by
  calc
    Artifact.submissionArtifact.instructionPC 2303 =
        Artifact.submissionArtifact.instructionPC 1675 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1675).take 628)).length :=
      instructionPC_add Artifact.submissionArtifact 1675 628
    _ = 3007 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 935 ≤ i) (hii : i ≤ 960) :
    Artifact.submissionArtifact.instructionPC i =
      [1256, 1257, 1259, 1260, 1261, 1263, 1264, 1267, 1268, 1270, 1271, 1272, 1273, 1274, 1276, 1277, 1279, 1280, 1281, 1283, 1284, 1285, 1286, 1287, 1289, 1290][i - 935]! := by
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

@[simp] theorem fastPC1 (i : Nat) (hi : 961 ≤ i) (hii : i ≤ 999) :
    Artifact.submissionArtifact.instructionPC i =
      [1291, 1292, 1293, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1304, 1305, 1307, 1308, 1309, 1310, 1311, 1312, 1314, 1315, 1316, 1319, 1320, 1321, 1324, 1325, 1328, 1329, 1330, 1331, 1333, 1334, 1337, 1338, 1340, 1341, 1342, 1343, 1346][i - 961]! := by
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

@[simp] theorem fastPC2 (i : Nat) (hi : 1000 ≤ i) (hii : i ≤ 1035) :
    Artifact.submissionArtifact.instructionPC i =
      [1347, 1348, 1351, 1352, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1373, 1374, 1375, 1376, 1377, 1379, 1380, 1381, 1382, 1383, 1384, 1386, 1387, 1388, 1389][i - 1000]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1000 + (i - 1000)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1000 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1000).take (i - 1000))).length :=
      instructionPC_add Artifact.submissionArtifact 1000 (i - 1000)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 1036 ≤ i) (hii : i ≤ 1070) :
    Artifact.submissionArtifact.instructionPC i =
      [1390, 1391, 1393, 1394, 1395, 1396, 1397, 1398, 1400, 1401, 1402, 1403, 1404, 1405, 1407, 1408, 1409, 1410, 1411, 1412, 1414, 1415, 1416, 1417, 1418, 1419, 1421, 1422, 1423, 1424, 1425, 1428, 1429, 1430, 1431][i - 1036]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1036 + (i - 1036)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1036 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1036).take (i - 1036))).length :=
      instructionPC_add Artifact.submissionArtifact 1036 (i - 1036)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1071 ≤ i) (hii : i ≤ 1100) :
    Artifact.submissionArtifact.instructionPC i =
      [1434, 1435, 1436, 1439, 1440, 1443, 1446, 1447, 1450, 1453, 1456, 1457, 1458, 1461, 1464, 1465, 1468, 1471, 1472, 1473, 1474, 1475, 1476, 1478, 1479, 1482, 1483, 1486, 1487, 1490][i - 1071]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1071 + (i - 1071)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1071 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1071).take (i - 1071))).length :=
      instructionPC_add Artifact.submissionArtifact 1071 (i - 1071)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1101 ≤ i) (hii : i ≤ 1120) :
    Artifact.submissionArtifact.instructionPC i =
      [1491, 1492, 1493, 1494, 1495, 1498, 1499, 1500, 1501, 1502, 1505, 1506, 1507, 1508, 1509, 1510, 1513, 1514, 1517, 1518][i - 1101]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1101 + (i - 1101)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1101 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1101).take (i - 1101))).length :=
      instructionPC_add Artifact.submissionArtifact 1101 (i - 1101)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1121 ≤ i) (hii : i ≤ 1159) :
    Artifact.submissionArtifact.instructionPC i =
      [1519, 1520, 1521, 1522, 1525, 1526, 1529, 1532, 1535, 1538, 1541, 1542, 1543, 1544, 1545, 1546, 1548, 1549, 1550, 1551, 1553, 1554, 1555, 1556, 1559, 1560, 1561, 1564, 1567, 1570, 1573, 1576, 1577, 1578, 1580, 1581, 1584, 1585, 1586][i - 1121]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1121 + (i - 1121)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1121 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1121).take (i - 1121))).length :=
      instructionPC_add Artifact.submissionArtifact 1121 (i - 1121)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1160 ≤ i) (hii : i ≤ 1187) :
    Artifact.submissionArtifact.instructionPC i =
      [1587, 1588, 1591, 1594, 1597, 1600, 1603, 1604, 1605, 1608, 1609, 1610, 1611, 1612, 1613, 1616, 1617, 1620, 1621, 1622, 1625, 1628, 1629, 1632, 1635, 1636, 1637, 1638][i - 1160]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1160 + (i - 1160)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1160 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1160).take (i - 1160))).length :=
      instructionPC_add Artifact.submissionArtifact 1160 (i - 1160)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1188 ≤ i) (hii : i ≤ 1227) :
    Artifact.submissionArtifact.instructionPC i =
      [1639, 1640, 1641, 1644, 1645, 1648, 1651, 1654, 1657, 1660, 1661, 1662, 1663, 1665, 1666, 1667, 1670, 1671, 1672, 1673, 1675, 1676, 1679, 1680, 1681, 1682, 1684, 1685, 1688, 1689, 1690, 1693, 1696, 1699, 1702, 1705, 1706, 1707, 1708, 1709][i - 1188]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1188 + (i - 1188)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1188 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1188).take (i - 1188))).length :=
      instructionPC_add Artifact.submissionArtifact 1188 (i - 1188)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1228 ≤ i) (hii : i ≤ 1261) :
    Artifact.submissionArtifact.instructionPC i =
      [1710, 1713, 1714, 1715, 1716, 1717, 1718, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1732, 1733, 1734, 1737, 1738, 1741, 1742, 1743, 1744, 1747, 1748, 1749, 1751, 1752, 1753, 1754, 1757, 1758][i - 1228]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1228 + (i - 1228)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1228 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1228).take (i - 1228))).length :=
      instructionPC_add Artifact.submissionArtifact 1228 (i - 1228)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1262 ≤ i) (hii : i ≤ 1300) :
    Artifact.submissionArtifact.instructionPC i =
      [1759, 1760, 1761, 1762, 1765, 1766, 1767, 1769, 1770, 1771, 1774, 1775, 1776, 1777, 1778, 1780, 1781, 1782, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1803, 1804, 1805, 1808, 1809][i - 1262]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1262 + (i - 1262)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1262 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1262).take (i - 1262))).length :=
      instructionPC_add Artifact.submissionArtifact 1262 (i - 1262)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1301 ≤ i) (hii : i ≤ 1337) :
    Artifact.submissionArtifact.instructionPC i =
      [1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846][i - 1301]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1301 + (i - 1301)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1301 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1301).take (i - 1301))).length :=
      instructionPC_add Artifact.submissionArtifact 1301 (i - 1301)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1338 ≤ i) (hii : i ≤ 1380) :
    Artifact.submissionArtifact.instructionPC i =
      [1847, 1848, 1850, 1851, 1852, 1853, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1864, 1865, 1866, 1867, 1868, 1871, 1872, 1873, 1874, 1877, 1878, 1879, 1882, 1883, 1886, 1887, 1888, 1891, 1892, 1893, 1894, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905][i - 1338]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1338 + (i - 1338)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1338 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1338).take (i - 1338))).length :=
      instructionPC_add Artifact.submissionArtifact 1338 (i - 1338)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1381 ≤ i) (hii : i ≤ 1421) :
    Artifact.submissionArtifact.instructionPC i =
      [1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1921, 1922, 1924, 1925, 1926, 1929, 1930, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952][i - 1381]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1381 + (i - 1381)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1381 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1381).take (i - 1381))).length :=
      instructionPC_add Artifact.submissionArtifact 1381 (i - 1381)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1422 ≤ i) (hii : i ≤ 1457) :
    Artifact.submissionArtifact.instructionPC i =
      [1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1968, 1969, 1971, 1972, 1973, 1974, 1975, 1976, 1978, 1979, 1980, 1983, 1984, 1985, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995][i - 1422]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1422 + (i - 1422)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1422 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1422).take (i - 1422))).length :=
      instructionPC_add Artifact.submissionArtifact 1422 (i - 1422)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1458 ≤ i) (hii : i ≤ 1498) :
    Artifact.submissionArtifact.instructionPC i =
      [1998, 1999, 2000, 2001, 2004, 2005, 2006, 2009, 2010, 2011, 2014, 2015, 2017, 2018, 2019, 2020, 2021, 2022, 2025, 2026, 2027, 2028, 2029, 2032, 2033, 2034, 2037, 2038, 2039, 2040, 2041, 2043, 2044, 2045, 2046, 2047, 2048, 2050, 2051, 2052, 2053][i - 1458]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1458 + (i - 1458)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1458 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1458).take (i - 1458))).length :=
      instructionPC_add Artifact.submissionArtifact 1458 (i - 1458)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1499 ≤ i) (hii : i ≤ 1539) :
    Artifact.submissionArtifact.instructionPC i =
      [2054, 2055, 2056, 2057, 2060, 2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2086, 2087, 2088, 2089, 2091, 2092, 2093, 2094, 2095, 2097, 2098, 2099][i - 1499]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1499 + (i - 1499)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1499 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1499).take (i - 1499))).length :=
      instructionPC_add Artifact.submissionArtifact 1499 (i - 1499)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1540 ≤ i) (hii : i ≤ 1563) :
    Artifact.submissionArtifact.instructionPC i =
      [2100, 2103, 2104, 2105, 2108, 2109, 2110, 2111, 2112, 2115, 2116, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127, 2128, 2129, 2130, 2131][i - 1540]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1540 + (i - 1540)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1540 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1540).take (i - 1540))).length :=
      instructionPC_add Artifact.submissionArtifact 1540 (i - 1540)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1564 ≤ i) (hii : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143, 2145, 2146, 2147, 2148, 2150, 2151, 2152, 2153, 2154, 2156, 2157, 2158, 2159, 2162, 2163, 2164, 2167, 2168, 2169, 2170, 2171, 2172, 2175, 2176, 2177, 2180, 2181, 2182, 2185, 2186, 2189][i - 1564]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1564 + (i - 1564)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1564 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1564).take (i - 1564))).length :=
      instructionPC_add Artifact.submissionArtifact 1564 (i - 1564)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1607 ≤ i) (hii : i ≤ 1609) :
    Artifact.submissionArtifact.instructionPC i =
      [2190, 2191, 2192][i - 1607]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1607 + (i - 1607)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1607 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1607).take (i - 1607))).length :=
      instructionPC_add Artifact.submissionArtifact 1607 (i - 1607)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1610 ≤ i) (hii : i ≤ 1626) :
    Artifact.submissionArtifact.instructionPC i =
      [2193, 2194, 2197, 2198, 2199, 2200, 2203, 2204, 2205, 2206, 2207, 2208, 2209, 2212, 2213, 2214, 2215][i - 1610]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1610 + (i - 1610)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1610 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1610).take (i - 1610))).length :=
      instructionPC_add Artifact.submissionArtifact 1610 (i - 1610)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1627 ≤ i) (hii : i ≤ 1639) :
    Artifact.submissionArtifact.instructionPC i =
      [2216, 2217, 2218, 2219, 2221, 2222, 2223, 2226, 2227, 2229, 2232, 2233, 2236][i - 1627]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1627 + (i - 1627)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1627 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1627).take (i - 1627))).length :=
      instructionPC_add Artifact.submissionArtifact 1627 (i - 1627)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1640 ≤ i) (hii : i ≤ 1674) :
    Artifact.submissionArtifact.instructionPC i =
      [2237, 2238, 2239, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2252, 2253, 2255, 2258, 2259, 2260, 2261, 2262, 2264, 2265, 2266, 2267, 2269, 2270, 2271, 2272, 2274, 2275, 2276, 2278, 2279, 2281, 2282, 2285][i - 1640]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1640 + (i - 1640)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1640 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1640).take (i - 1640))).length :=
      instructionPC_add Artifact.submissionArtifact 1640 (i - 1640)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1675 ≤ i) (hii : i ≤ 1686) :
    Artifact.submissionArtifact.instructionPC i =
      [2286, 2287, 2288, 2291, 2292, 2295, 2296, 2299, 2302, 2303, 2306, 2309][i - 1675]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1675 + (i - 1675)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1675 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1675).take (i - 1675))).length :=
      instructionPC_add Artifact.submissionArtifact 1675 (i - 1675)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2303 ≤ i) (hii : i ≤ 2348) :
    Artifact.submissionArtifact.instructionPC i =
      [3007, 3008, 3009, 3010, 3011, 3012, 3013, 3015, 3016, 3017, 3018, 3021, 3022, 3023, 3025, 3028, 3029, 3032, 3035, 3038, 3041, 3044, 3045, 3046, 3047, 3049, 3050, 3052, 3053, 3054, 3055, 3057, 3058, 3059, 3061, 3062, 3064, 3065, 3066, 3067, 3068, 3071, 3072, 3073, 3075, 3078][i - 2303]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2303 + (i - 2303)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2303 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2303).take (i - 2303))).length :=
      instructionPC_add Artifact.submissionArtifact 2303 (i - 2303)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 888 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1435 = true :=
  Artifact.isValidJumpDest_index 1072 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1457 = true :=
  Artifact.isValidJumpDest_index 1082 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1472 = true :=
  Artifact.isValidJumpDest_index 1089 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1491 = true :=
  Artifact.isValidJumpDest_index 1101 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1506 = true :=
  Artifact.isValidJumpDest_index 1112 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1518 = true :=
  Artifact.isValidJumpDest_index 1120 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1542 = true :=
  Artifact.isValidJumpDest_index 1132 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1577 = true :=
  Artifact.isValidJumpDest_index 1153 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1585 = true :=
  Artifact.isValidJumpDest_index 1158 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1604 = true :=
  Artifact.isValidJumpDest_index 1167 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3273 = true :=
  Artifact.isValidJumpDest_index 2505 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1609 = true :=
  Artifact.isValidJumpDest_index 1170 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1621 = true :=
  Artifact.isValidJumpDest_index 1178 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1636 = true :=
  Artifact.isValidJumpDest_index 1185 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1661 = true :=
  Artifact.isValidJumpDest_index 1198 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1662 = true :=
  Artifact.isValidJumpDest_index 1199 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1680 = true :=
  Artifact.isValidJumpDest_index 1211 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1706 = true :=
  Artifact.isValidJumpDest_index 1224 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1716 = true :=
  Artifact.isValidJumpDest_index 1232 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1722 = true :=
  Artifact.isValidJumpDest_index 1236 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1733 = true :=
  Artifact.isValidJumpDest_index 1245 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1737 = true :=
  Artifact.isValidJumpDest_index 1247 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1748 = true :=
  Artifact.isValidJumpDest_index 1254 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1761 = true :=
  Artifact.isValidJumpDest_index 1264 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1796 = true :=
  Artifact.isValidJumpDest_index 1291 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1810 = true :=
  Artifact.isValidJumpDest_index 1301 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1934 = true :=
  Artifact.isValidJumpDest_index 1403 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2033 = true :=
  Artifact.isValidJumpDest_index 1482 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2064 = true :=
  Artifact.isValidJumpDest_index 1507 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2120 = true :=
  Artifact.isValidJumpDest_index 1552 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2193 = true :=
  Artifact.isValidJumpDest_index 1610 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2204 = true :=
  Artifact.isValidJumpDest_index 1617 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2216 = true :=
  Artifact.isValidJumpDest_index 1627 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2237 = true :=
  Artifact.isValidJumpDest_index 1640 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2259 = true :=
  Artifact.isValidJumpDest_index 1655 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2286 = true :=
  Artifact.isValidJumpDest_index 1675 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2972 = true :=
  Artifact.isValidJumpDest_index 2280 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3007 = true :=
  Artifact.isValidJumpDest_index 2303 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3045 = true :=
  Artifact.isValidJumpDest_index 2325 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4804 = true :=
  Artifact.isValidJumpDest_index 3635 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4976 = true :=
  Artifact.isValidJumpDest_index 3763 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5227 = true :=
  Artifact.isValidJumpDest_index 3944 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5216 = true :=
  Artifact.isValidJumpDest_index 3937 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
