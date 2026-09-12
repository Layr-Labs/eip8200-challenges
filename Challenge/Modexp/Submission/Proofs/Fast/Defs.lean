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
    Artifact.submissionArtifact.instructionPC 860 = 1121 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 899 = 1177 := by
  calc
    Artifact.submissionArtifact.instructionPC 899 =
        Artifact.submissionArtifact.instructionPC 860 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 860).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 860 39
    _ = 1177 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 938 = 1233 := by
  calc
    Artifact.submissionArtifact.instructionPC 938 =
        Artifact.submissionArtifact.instructionPC 899 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 899).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 899 39
    _ = 1233 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 974 = 1276 := by
  calc
    Artifact.submissionArtifact.instructionPC 974 =
        Artifact.submissionArtifact.instructionPC 938 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 938).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 938 36
    _ = 1276 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1014 = 1332 := by
  calc
    Artifact.submissionArtifact.instructionPC 1014 =
        Artifact.submissionArtifact.instructionPC 974 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 974).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 974 40
    _ = 1332 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1044 = 1389 := by
  calc
    Artifact.submissionArtifact.instructionPC 1044 =
        Artifact.submissionArtifact.instructionPC 1014 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1014).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1014 30
    _ = 1389 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1064 = 1417 := by
  calc
    Artifact.submissionArtifact.instructionPC 1064 =
        Artifact.submissionArtifact.instructionPC 1044 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1044).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1044 20
    _ = 1417 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1103 = 1485 := by
  calc
    Artifact.submissionArtifact.instructionPC 1103 =
        Artifact.submissionArtifact.instructionPC 1064 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1064).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1064 39
    _ = 1485 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1131 = 1537 := by
  calc
    Artifact.submissionArtifact.instructionPC 1131 =
        Artifact.submissionArtifact.instructionPC 1103 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1103).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1103 28
    _ = 1537 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1171 = 1608 := by
  calc
    Artifact.submissionArtifact.instructionPC 1171 =
        Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1131).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1131 40
    _ = 1608 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1211 = 1665 := by
  calc
    Artifact.submissionArtifact.instructionPC 1211 =
        Artifact.submissionArtifact.instructionPC 1171 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1171).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1171 40
    _ = 1665 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1250 = 1716 := by
  calc
    Artifact.submissionArtifact.instructionPC 1250 =
        Artifact.submissionArtifact.instructionPC 1211 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1211).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1211 39
    _ = 1716 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1287 = 1753 := by
  calc
    Artifact.submissionArtifact.instructionPC 1287 =
        Artifact.submissionArtifact.instructionPC 1250 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1250).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1250 37
    _ = 1753 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1330 = 1812 := by
  calc
    Artifact.submissionArtifact.instructionPC 1330 =
        Artifact.submissionArtifact.instructionPC 1287 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1287).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1287 43
    _ = 1812 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1371 = 1859 := by
  calc
    Artifact.submissionArtifact.instructionPC 1371 =
        Artifact.submissionArtifact.instructionPC 1330 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1330).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1330 41
    _ = 1859 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1407 = 1904 := by
  calc
    Artifact.submissionArtifact.instructionPC 1407 =
        Artifact.submissionArtifact.instructionPC 1371 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1371).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1371 36
    _ = 1904 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1448 = 1960 := by
  calc
    Artifact.submissionArtifact.instructionPC 1448 =
        Artifact.submissionArtifact.instructionPC 1407 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1407).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1407 41
    _ = 1960 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1489 = 2006 := by
  calc
    Artifact.submissionArtifact.instructionPC 1489 =
        Artifact.submissionArtifact.instructionPC 1448 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1448).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1448 41
    _ = 2006 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1513 = 2038 := by
  calc
    Artifact.submissionArtifact.instructionPC 1513 =
        Artifact.submissionArtifact.instructionPC 1489 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1489).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1489 24
    _ = 2038 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1556 = 2096 := by
  calc
    Artifact.submissionArtifact.instructionPC 1556 =
        Artifact.submissionArtifact.instructionPC 1513 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1513).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1513 43
    _ = 2096 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1559 = 2099 := by
  calc
    Artifact.submissionArtifact.instructionPC 1559 =
        Artifact.submissionArtifact.instructionPC 1556 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1556).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1556 3
    _ = 2099 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1576 = 2122 := by
  calc
    Artifact.submissionArtifact.instructionPC 1576 =
        Artifact.submissionArtifact.instructionPC 1559 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1559).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1559 17
    _ = 2122 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1589 = 2143 := by
  calc
    Artifact.submissionArtifact.instructionPC 1589 =
        Artifact.submissionArtifact.instructionPC 1576 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1576).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1576 13
    _ = 2143 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1624 = 2192 := by
  calc
    Artifact.submissionArtifact.instructionPC 1624 =
        Artifact.submissionArtifact.instructionPC 1589 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1589).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1589 35
    _ = 2192 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2252 = 2913 := by
  calc
    Artifact.submissionArtifact.instructionPC 2252 =
        Artifact.submissionArtifact.instructionPC 1624 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1624).take 628)).length :=
      instructionPC_add Artifact.submissionArtifact 1624 628
    _ = 2913 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 860 ≤ i) (hii : i ≤ 898) :
    Artifact.submissionArtifact.instructionPC i =
      [1121, 1122, 1124, 1125, 1126, 1128, 1129, 1132, 1133, 1135, 1136, 1137, 1138, 1139, 1142, 1143, 1144, 1147, 1148, 1149, 1150, 1153, 1154, 1155, 1158, 1159, 1160, 1162, 1163, 1165, 1166, 1167, 1169, 1170, 1171, 1172, 1173, 1175, 1176][i - 860]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (860 + (i - 860)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 860 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 860).take (i - 860))).length :=
      instructionPC_add Artifact.submissionArtifact 860 (i - 860)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 899 ≤ i) (hii : i ≤ 937) :
    Artifact.submissionArtifact.instructionPC i =
      [1177, 1178, 1179, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1190, 1191, 1193, 1194, 1195, 1196, 1197, 1198, 1200, 1201, 1202, 1205, 1206, 1207, 1210, 1211, 1212, 1215, 1216, 1217, 1219, 1220, 1223, 1224, 1226, 1227, 1228, 1229, 1232][i - 899]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (899 + (i - 899)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 899 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 899).take (i - 899))).length :=
      instructionPC_add Artifact.submissionArtifact 899 (i - 899)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 938 ≤ i) (hii : i ≤ 973) :
    Artifact.submissionArtifact.instructionPC i =
      [1233, 1234, 1237, 1238, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1259, 1260, 1261, 1262, 1263, 1265, 1266, 1267, 1268, 1269, 1270, 1272, 1273, 1274, 1275][i - 938]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (938 + (i - 938)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 938 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 938).take (i - 938))).length :=
      instructionPC_add Artifact.submissionArtifact 938 (i - 938)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 974 ≤ i) (hii : i ≤ 1013) :
    Artifact.submissionArtifact.instructionPC i =
      [1276, 1277, 1279, 1280, 1281, 1282, 1283, 1284, 1286, 1287, 1288, 1289, 1290, 1291, 1293, 1294, 1295, 1296, 1297, 1298, 1300, 1301, 1302, 1303, 1304, 1305, 1307, 1308, 1309, 1310, 1311, 1314, 1315, 1316, 1317, 1319, 1322, 1323, 1326, 1329][i - 974]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (974 + (i - 974)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 974 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 974).take (i - 974))).length :=
      instructionPC_add Artifact.submissionArtifact 974 (i - 974)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1014 ≤ i) (hii : i ≤ 1043) :
    Artifact.submissionArtifact.instructionPC i =
      [1332, 1333, 1334, 1337, 1338, 1341, 1344, 1345, 1348, 1351, 1354, 1355, 1356, 1359, 1362, 1363, 1366, 1369, 1370, 1371, 1372, 1373, 1374, 1376, 1377, 1380, 1381, 1384, 1385, 1388][i - 1014]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1014 + (i - 1014)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1014 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1014).take (i - 1014))).length :=
      instructionPC_add Artifact.submissionArtifact 1014 (i - 1014)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1044 ≤ i) (hii : i ≤ 1063) :
    Artifact.submissionArtifact.instructionPC i =
      [1389, 1390, 1391, 1392, 1393, 1396, 1397, 1398, 1399, 1400, 1403, 1404, 1405, 1406, 1407, 1408, 1411, 1412, 1415, 1416][i - 1044]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1044 + (i - 1044)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1044 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1044).take (i - 1044))).length :=
      instructionPC_add Artifact.submissionArtifact 1044 (i - 1044)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1064 ≤ i) (hii : i ≤ 1102) :
    Artifact.submissionArtifact.instructionPC i =
      [1417, 1418, 1419, 1420, 1423, 1424, 1427, 1430, 1433, 1436, 1439, 1440, 1441, 1442, 1443, 1444, 1446, 1447, 1448, 1449, 1451, 1452, 1453, 1454, 1457, 1458, 1459, 1462, 1465, 1468, 1471, 1474, 1475, 1476, 1478, 1479, 1482, 1483, 1484][i - 1064]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1064 + (i - 1064)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1064 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1064).take (i - 1064))).length :=
      instructionPC_add Artifact.submissionArtifact 1064 (i - 1064)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1103 ≤ i) (hii : i ≤ 1130) :
    Artifact.submissionArtifact.instructionPC i =
      [1485, 1486, 1489, 1492, 1495, 1498, 1501, 1502, 1503, 1506, 1507, 1508, 1509, 1510, 1511, 1514, 1515, 1518, 1519, 1520, 1523, 1526, 1527, 1530, 1533, 1534, 1535, 1536][i - 1103]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1103 + (i - 1103)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1103 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1103).take (i - 1103))).length :=
      instructionPC_add Artifact.submissionArtifact 1103 (i - 1103)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1131 ≤ i) (hii : i ≤ 1170) :
    Artifact.submissionArtifact.instructionPC i =
      [1537, 1538, 1539, 1542, 1543, 1546, 1549, 1552, 1555, 1558, 1559, 1560, 1561, 1563, 1564, 1565, 1568, 1569, 1570, 1571, 1573, 1574, 1577, 1578, 1579, 1580, 1582, 1583, 1586, 1587, 1588, 1591, 1594, 1597, 1600, 1603, 1604, 1605, 1606, 1607][i - 1131]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1131 + (i - 1131)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1131 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1131).take (i - 1131))).length :=
      instructionPC_add Artifact.submissionArtifact 1131 (i - 1131)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1171 ≤ i) (hii : i ≤ 1210) :
    Artifact.submissionArtifact.instructionPC i =
      [1608, 1611, 1612, 1613, 1614, 1615, 1616, 1619, 1620, 1621, 1622, 1623, 1624, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1638, 1639, 1640, 1643, 1644, 1647, 1648, 1649, 1650, 1653, 1654, 1655, 1657, 1658, 1659, 1660, 1663, 1664][i - 1171]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1171 + (i - 1171)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1171 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1171).take (i - 1171))).length :=
      instructionPC_add Artifact.submissionArtifact 1171 (i - 1171)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1211 ≤ i) (hii : i ≤ 1249) :
    Artifact.submissionArtifact.instructionPC i =
      [1665, 1666, 1667, 1668, 1671, 1672, 1673, 1675, 1676, 1677, 1680, 1681, 1682, 1683, 1684, 1686, 1687, 1688, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1709, 1710, 1711, 1714, 1715][i - 1211]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1211 + (i - 1211)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1211 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1211).take (i - 1211))).length :=
      instructionPC_add Artifact.submissionArtifact 1211 (i - 1211)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1250 ≤ i) (hii : i ≤ 1286) :
    Artifact.submissionArtifact.instructionPC i =
      [1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752][i - 1250]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1250 + (i - 1250)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1250 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1250).take (i - 1250))).length :=
      instructionPC_add Artifact.submissionArtifact 1250 (i - 1250)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1287 ≤ i) (hii : i ≤ 1329) :
    Artifact.submissionArtifact.instructionPC i =
      [1753, 1754, 1756, 1757, 1758, 1759, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1770, 1771, 1772, 1773, 1774, 1777, 1778, 1779, 1780, 1783, 1784, 1785, 1788, 1789, 1792, 1793, 1794, 1797, 1798, 1799, 1800, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811][i - 1287]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1287 + (i - 1287)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1287 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1287).take (i - 1287))).length :=
      instructionPC_add Artifact.submissionArtifact 1287 (i - 1287)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1330 ≤ i) (hii : i ≤ 1370) :
    Artifact.submissionArtifact.instructionPC i =
      [1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1827, 1828, 1830, 1831, 1832, 1835, 1836, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858][i - 1330]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1330 + (i - 1330)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1330 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1330).take (i - 1330))).length :=
      instructionPC_add Artifact.submissionArtifact 1330 (i - 1330)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1371 ≤ i) (hii : i ≤ 1406) :
    Artifact.submissionArtifact.instructionPC i =
      [1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1874, 1875, 1877, 1878, 1879, 1880, 1881, 1882, 1884, 1885, 1886, 1889, 1890, 1891, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901][i - 1371]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1371 + (i - 1371)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1371 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1371).take (i - 1371))).length :=
      instructionPC_add Artifact.submissionArtifact 1371 (i - 1371)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1407 ≤ i) (hii : i ≤ 1447) :
    Artifact.submissionArtifact.instructionPC i =
      [1904, 1905, 1906, 1907, 1910, 1911, 1912, 1915, 1916, 1917, 1920, 1921, 1923, 1924, 1925, 1926, 1927, 1928, 1931, 1932, 1933, 1934, 1935, 1938, 1939, 1940, 1943, 1944, 1945, 1946, 1947, 1949, 1950, 1951, 1952, 1953, 1954, 1956, 1957, 1958, 1959][i - 1407]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1407 + (i - 1407)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1407 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1407).take (i - 1407))).length :=
      instructionPC_add Artifact.submissionArtifact 1407 (i - 1407)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1448 ≤ i) (hii : i ≤ 1488) :
    Artifact.submissionArtifact.instructionPC i =
      [1960, 1961, 1962, 1963, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1992, 1993, 1994, 1995, 1997, 1998, 1999, 2000, 2001, 2003, 2004, 2005][i - 1448]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1448 + (i - 1448)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1448 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1448).take (i - 1448))).length :=
      instructionPC_add Artifact.submissionArtifact 1448 (i - 1448)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1489 ≤ i) (hii : i ≤ 1512) :
    Artifact.submissionArtifact.instructionPC i =
      [2006, 2009, 2010, 2011, 2014, 2015, 2016, 2017, 2018, 2021, 2022, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037][i - 1489]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1489 + (i - 1489)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1489 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1489).take (i - 1489))).length :=
      instructionPC_add Artifact.submissionArtifact 1489 (i - 1489)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1513 ≤ i) (hii : i ≤ 1555) :
    Artifact.submissionArtifact.instructionPC i =
      [2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048, 2049, 2051, 2052, 2053, 2054, 2056, 2057, 2058, 2059, 2060, 2062, 2063, 2064, 2065, 2068, 2069, 2070, 2073, 2074, 2075, 2076, 2077, 2078, 2081, 2082, 2083, 2086, 2087, 2088, 2091, 2092, 2095][i - 1513]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1513 + (i - 1513)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1513 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1513).take (i - 1513))).length :=
      instructionPC_add Artifact.submissionArtifact 1513 (i - 1513)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1556 ≤ i) (hii : i ≤ 1558) :
    Artifact.submissionArtifact.instructionPC i =
      [2096, 2097, 2098][i - 1556]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1556 + (i - 1556)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1556 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1556).take (i - 1556))).length :=
      instructionPC_add Artifact.submissionArtifact 1556 (i - 1556)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1559 ≤ i) (hii : i ≤ 1575) :
    Artifact.submissionArtifact.instructionPC i =
      [2099, 2100, 2103, 2104, 2105, 2106, 2109, 2110, 2111, 2112, 2113, 2114, 2115, 2118, 2119, 2120, 2121][i - 1559]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1559 + (i - 1559)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1559 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1559).take (i - 1559))).length :=
      instructionPC_add Artifact.submissionArtifact 1559 (i - 1559)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1576 ≤ i) (hii : i ≤ 1588) :
    Artifact.submissionArtifact.instructionPC i =
      [2122, 2123, 2124, 2125, 2127, 2128, 2129, 2132, 2133, 2135, 2138, 2139, 2142][i - 1576]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1576 + (i - 1576)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1576 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1576).take (i - 1576))).length :=
      instructionPC_add Artifact.submissionArtifact 1576 (i - 1576)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1589 ≤ i) (hii : i ≤ 1623) :
    Artifact.submissionArtifact.instructionPC i =
      [2143, 2144, 2145, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2158, 2159, 2161, 2164, 2165, 2166, 2167, 2168, 2170, 2171, 2172, 2173, 2175, 2176, 2177, 2178, 2180, 2181, 2182, 2184, 2185, 2187, 2188, 2191][i - 1589]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1589 + (i - 1589)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1589 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1589).take (i - 1589))).length :=
      instructionPC_add Artifact.submissionArtifact 1589 (i - 1589)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1624 ≤ i) (hii : i ≤ 1635) :
    Artifact.submissionArtifact.instructionPC i =
      [2192, 2193, 2194, 2197, 2198, 2201, 2202, 2205, 2208, 2209, 2212, 2215][i - 1624]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1624 + (i - 1624)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1624 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1624).take (i - 1624))).length :=
      instructionPC_add Artifact.submissionArtifact 1624 (i - 1624)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2252 ≤ i) (hii : i ≤ 2297) :
    Artifact.submissionArtifact.instructionPC i =
      [2913, 2914, 2915, 2916, 2917, 2918, 2919, 2921, 2922, 2923, 2924, 2927, 2928, 2929, 2931, 2934, 2935, 2938, 2941, 2944, 2947, 2950, 2951, 2952, 2953, 2955, 2956, 2958, 2959, 2960, 2961, 2963, 2964, 2965, 2967, 2968, 2970, 2971, 2972, 2973, 2974, 2977, 2978, 2979, 2981, 2984][i - 2252]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2252 + (i - 2252)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2252 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2252).take (i - 2252))).length :=
      instructionPC_add Artifact.submissionArtifact 2252 (i - 2252)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1054 = true :=
  Artifact.isValidJumpDest_index 813 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1333 = true :=
  Artifact.isValidJumpDest_index 1015 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1355 = true :=
  Artifact.isValidJumpDest_index 1025 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1370 = true :=
  Artifact.isValidJumpDest_index 1032 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1389 = true :=
  Artifact.isValidJumpDest_index 1044 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1404 = true :=
  Artifact.isValidJumpDest_index 1055 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1416 = true :=
  Artifact.isValidJumpDest_index 1063 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1440 = true :=
  Artifact.isValidJumpDest_index 1075 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1475 = true :=
  Artifact.isValidJumpDest_index 1096 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1483 = true :=
  Artifact.isValidJumpDest_index 1101 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1502 = true :=
  Artifact.isValidJumpDest_index 1110 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3179 = true :=
  Artifact.isValidJumpDest_index 2454 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1507 = true :=
  Artifact.isValidJumpDest_index 1113 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1519 = true :=
  Artifact.isValidJumpDest_index 1121 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1534 = true :=
  Artifact.isValidJumpDest_index 1128 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1559 = true :=
  Artifact.isValidJumpDest_index 1141 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1560 = true :=
  Artifact.isValidJumpDest_index 1142 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1578 = true :=
  Artifact.isValidJumpDest_index 1154 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1604 = true :=
  Artifact.isValidJumpDest_index 1167 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1614 = true :=
  Artifact.isValidJumpDest_index 1175 (by rfl)

theorem jumpDest1818 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1620 = true :=
  Artifact.isValidJumpDest_index 1179 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1628 = true :=
  Artifact.isValidJumpDest_index 1185 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1639 = true :=
  Artifact.isValidJumpDest_index 1194 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1643 = true :=
  Artifact.isValidJumpDest_index 1196 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1654 = true :=
  Artifact.isValidJumpDest_index 1203 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1667 = true :=
  Artifact.isValidJumpDest_index 1213 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1702 = true :=
  Artifact.isValidJumpDest_index 1240 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1716 = true :=
  Artifact.isValidJumpDest_index 1250 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1840 = true :=
  Artifact.isValidJumpDest_index 1352 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1939 = true :=
  Artifact.isValidJumpDest_index 1431 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1970 = true :=
  Artifact.isValidJumpDest_index 1456 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2026 = true :=
  Artifact.isValidJumpDest_index 1501 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2099 = true :=
  Artifact.isValidJumpDest_index 1559 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2110 = true :=
  Artifact.isValidJumpDest_index 1566 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2122 = true :=
  Artifact.isValidJumpDest_index 1576 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2143 = true :=
  Artifact.isValidJumpDest_index 1589 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2165 = true :=
  Artifact.isValidJumpDest_index 1604 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2192 = true :=
  Artifact.isValidJumpDest_index 1624 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2878 = true :=
  Artifact.isValidJumpDest_index 2229 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2913 = true :=
  Artifact.isValidJumpDest_index 2252 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2274 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4671 = true :=
  Artifact.isValidJumpDest_index 3564 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4851 = true :=
  Artifact.isValidJumpDest_index 3681 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5102 = true :=
  Artifact.isValidJumpDest_index 3862 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5091 = true :=
  Artifact.isValidJumpDest_index 3855 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
