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
    Artifact.submissionArtifact.instructionPC 886 = 1156 := by
  calc
    Artifact.submissionArtifact.instructionPC 886 =
        Artifact.submissionArtifact.instructionPC 860 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 860).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 860 26
    _ = 1156 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 925 = 1212 := by
  calc
    Artifact.submissionArtifact.instructionPC 925 =
        Artifact.submissionArtifact.instructionPC 886 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 886).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 886 39
    _ = 1212 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 961 = 1255 := by
  calc
    Artifact.submissionArtifact.instructionPC 961 =
        Artifact.submissionArtifact.instructionPC 925 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 925).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 925 36
    _ = 1255 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 996 = 1299 := by
  calc
    Artifact.submissionArtifact.instructionPC 996 =
        Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 961 35
    _ = 1299 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1026 = 1356 := by
  calc
    Artifact.submissionArtifact.instructionPC 1026 =
        Artifact.submissionArtifact.instructionPC 996 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 996).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 996 30
    _ = 1356 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1046 = 1384 := by
  calc
    Artifact.submissionArtifact.instructionPC 1046 =
        Artifact.submissionArtifact.instructionPC 1026 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1026).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1026 20
    _ = 1384 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1085 = 1452 := by
  calc
    Artifact.submissionArtifact.instructionPC 1085 =
        Artifact.submissionArtifact.instructionPC 1046 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1046).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1046 39
    _ = 1452 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1113 = 1504 := by
  calc
    Artifact.submissionArtifact.instructionPC 1113 =
        Artifact.submissionArtifact.instructionPC 1085 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1085).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1085 28
    _ = 1504 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1153 = 1575 := by
  calc
    Artifact.submissionArtifact.instructionPC 1153 =
        Artifact.submissionArtifact.instructionPC 1113 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1113).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1113 40
    _ = 1575 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1187 = 1624 := by
  calc
    Artifact.submissionArtifact.instructionPC 1187 =
        Artifact.submissionArtifact.instructionPC 1153 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1153).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1153 34
    _ = 1624 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1226 = 1675 := by
  calc
    Artifact.submissionArtifact.instructionPC 1226 =
        Artifact.submissionArtifact.instructionPC 1187 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1187).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1187 39
    _ = 1675 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1263 = 1712 := by
  calc
    Artifact.submissionArtifact.instructionPC 1263 =
        Artifact.submissionArtifact.instructionPC 1226 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1226).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1226 37
    _ = 1712 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1306 = 1771 := by
  calc
    Artifact.submissionArtifact.instructionPC 1306 =
        Artifact.submissionArtifact.instructionPC 1263 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1263).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1263 43
    _ = 1771 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1347 = 1818 := by
  calc
    Artifact.submissionArtifact.instructionPC 1347 =
        Artifact.submissionArtifact.instructionPC 1306 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1306).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1306 41
    _ = 1818 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1383 = 1863 := by
  calc
    Artifact.submissionArtifact.instructionPC 1383 =
        Artifact.submissionArtifact.instructionPC 1347 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1347).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1347 36
    _ = 1863 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1424 = 1919 := by
  calc
    Artifact.submissionArtifact.instructionPC 1424 =
        Artifact.submissionArtifact.instructionPC 1383 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1383).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1383 41
    _ = 1919 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1465 = 1965 := by
  calc
    Artifact.submissionArtifact.instructionPC 1465 =
        Artifact.submissionArtifact.instructionPC 1424 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1424).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1424 41
    _ = 1965 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1489 = 1997 := by
  calc
    Artifact.submissionArtifact.instructionPC 1489 =
        Artifact.submissionArtifact.instructionPC 1465 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1465).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1465 24
    _ = 1997 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1532 = 2055 := by
  calc
    Artifact.submissionArtifact.instructionPC 1532 =
        Artifact.submissionArtifact.instructionPC 1489 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1489).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1489 43
    _ = 2055 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1535 = 2058 := by
  calc
    Artifact.submissionArtifact.instructionPC 1535 =
        Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1532).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1532 3
    _ = 2058 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1552 = 2081 := by
  calc
    Artifact.submissionArtifact.instructionPC 1552 =
        Artifact.submissionArtifact.instructionPC 1535 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1535).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1535 17
    _ = 2081 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1565 = 2102 := by
  calc
    Artifact.submissionArtifact.instructionPC 1565 =
        Artifact.submissionArtifact.instructionPC 1552 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1552).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1552 13
    _ = 2102 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1600 = 2151 := by
  calc
    Artifact.submissionArtifact.instructionPC 1600 =
        Artifact.submissionArtifact.instructionPC 1565 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1565).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1565 35
    _ = 2151 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2228 = 2872 := by
  calc
    Artifact.submissionArtifact.instructionPC 2228 =
        Artifact.submissionArtifact.instructionPC 1600 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1600).take 628)).length :=
      instructionPC_add Artifact.submissionArtifact 1600 628
    _ = 2872 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 860 ≤ i) (hii : i ≤ 885) :
    Artifact.submissionArtifact.instructionPC i =
      [1121, 1122, 1124, 1125, 1126, 1128, 1129, 1132, 1133, 1135, 1136, 1137, 1138, 1139, 1141, 1142, 1144, 1145, 1146, 1148, 1149, 1150, 1151, 1152, 1154, 1155][i - 860]! := by
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

@[simp] theorem fastPC1 (i : Nat) (hi : 886 ≤ i) (hii : i ≤ 924) :
    Artifact.submissionArtifact.instructionPC i =
      [1156, 1157, 1158, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1169, 1170, 1172, 1173, 1174, 1175, 1176, 1177, 1179, 1180, 1181, 1184, 1185, 1186, 1189, 1190, 1191, 1194, 1195, 1196, 1198, 1199, 1202, 1203, 1205, 1206, 1207, 1208, 1211][i - 886]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (886 + (i - 886)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 886 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 886).take (i - 886))).length :=
      instructionPC_add Artifact.submissionArtifact 886 (i - 886)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 925 ≤ i) (hii : i ≤ 960) :
    Artifact.submissionArtifact.instructionPC i =
      [1212, 1213, 1216, 1217, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1238, 1239, 1240, 1241, 1242, 1244, 1245, 1246, 1247, 1248, 1249, 1251, 1252, 1253, 1254][i - 925]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (925 + (i - 925)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 925 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 925).take (i - 925))).length :=
      instructionPC_add Artifact.submissionArtifact 925 (i - 925)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 961 ≤ i) (hii : i ≤ 995) :
    Artifact.submissionArtifact.instructionPC i =
      [1255, 1256, 1258, 1259, 1260, 1261, 1262, 1263, 1265, 1266, 1267, 1268, 1269, 1270, 1272, 1273, 1274, 1275, 1276, 1277, 1279, 1280, 1281, 1282, 1283, 1284, 1286, 1287, 1288, 1289, 1290, 1293, 1294, 1295, 1296][i - 961]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (961 + (i - 961)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take (i - 961))).length :=
      instructionPC_add Artifact.submissionArtifact 961 (i - 961)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 996 ≤ i) (hii : i ≤ 1025) :
    Artifact.submissionArtifact.instructionPC i =
      [1299, 1300, 1301, 1304, 1305, 1308, 1311, 1312, 1315, 1318, 1321, 1322, 1323, 1326, 1329, 1330, 1333, 1336, 1337, 1338, 1339, 1340, 1341, 1343, 1344, 1347, 1348, 1351, 1352, 1355][i - 996]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (996 + (i - 996)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 996 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 996).take (i - 996))).length :=
      instructionPC_add Artifact.submissionArtifact 996 (i - 996)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1026 ≤ i) (hii : i ≤ 1045) :
    Artifact.submissionArtifact.instructionPC i =
      [1356, 1357, 1358, 1359, 1360, 1363, 1364, 1365, 1366, 1367, 1370, 1371, 1372, 1373, 1374, 1375, 1378, 1379, 1382, 1383][i - 1026]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1026 + (i - 1026)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1026 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1026).take (i - 1026))).length :=
      instructionPC_add Artifact.submissionArtifact 1026 (i - 1026)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1046 ≤ i) (hii : i ≤ 1084) :
    Artifact.submissionArtifact.instructionPC i =
      [1384, 1385, 1386, 1387, 1390, 1391, 1394, 1397, 1400, 1403, 1406, 1407, 1408, 1409, 1410, 1411, 1413, 1414, 1415, 1416, 1418, 1419, 1420, 1421, 1424, 1425, 1426, 1429, 1432, 1435, 1438, 1441, 1442, 1443, 1445, 1446, 1449, 1450, 1451][i - 1046]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1046 + (i - 1046)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1046 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1046).take (i - 1046))).length :=
      instructionPC_add Artifact.submissionArtifact 1046 (i - 1046)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1085 ≤ i) (hii : i ≤ 1112) :
    Artifact.submissionArtifact.instructionPC i =
      [1452, 1453, 1456, 1459, 1462, 1465, 1468, 1469, 1470, 1473, 1474, 1475, 1476, 1477, 1478, 1481, 1482, 1485, 1486, 1487, 1490, 1493, 1494, 1497, 1500, 1501, 1502, 1503][i - 1085]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1085 + (i - 1085)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1085 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1085).take (i - 1085))).length :=
      instructionPC_add Artifact.submissionArtifact 1085 (i - 1085)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1113 ≤ i) (hii : i ≤ 1152) :
    Artifact.submissionArtifact.instructionPC i =
      [1504, 1505, 1506, 1509, 1510, 1513, 1516, 1519, 1522, 1525, 1526, 1527, 1528, 1530, 1531, 1532, 1535, 1536, 1537, 1538, 1540, 1541, 1544, 1545, 1546, 1547, 1549, 1550, 1553, 1554, 1555, 1558, 1561, 1564, 1567, 1570, 1571, 1572, 1573, 1574][i - 1113]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1113 + (i - 1113)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1113 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1113).take (i - 1113))).length :=
      instructionPC_add Artifact.submissionArtifact 1113 (i - 1113)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1153 ≤ i) (hii : i ≤ 1186) :
    Artifact.submissionArtifact.instructionPC i =
      [1575, 1578, 1579, 1580, 1581, 1582, 1583, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1597, 1598, 1599, 1602, 1603, 1606, 1607, 1608, 1609, 1612, 1613, 1614, 1616, 1617, 1618, 1619, 1622, 1623][i - 1153]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1153 + (i - 1153)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1153 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1153).take (i - 1153))).length :=
      instructionPC_add Artifact.submissionArtifact 1153 (i - 1153)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1187 ≤ i) (hii : i ≤ 1225) :
    Artifact.submissionArtifact.instructionPC i =
      [1624, 1625, 1626, 1627, 1630, 1631, 1632, 1634, 1635, 1636, 1639, 1640, 1641, 1642, 1643, 1645, 1646, 1647, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1668, 1669, 1670, 1673, 1674][i - 1187]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1187 + (i - 1187)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1187 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1187).take (i - 1187))).length :=
      instructionPC_add Artifact.submissionArtifact 1187 (i - 1187)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1226 ≤ i) (hii : i ≤ 1262) :
    Artifact.submissionArtifact.instructionPC i =
      [1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711][i - 1226]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1226 + (i - 1226)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1226 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1226).take (i - 1226))).length :=
      instructionPC_add Artifact.submissionArtifact 1226 (i - 1226)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1263 ≤ i) (hii : i ≤ 1305) :
    Artifact.submissionArtifact.instructionPC i =
      [1712, 1713, 1715, 1716, 1717, 1718, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1729, 1730, 1731, 1732, 1733, 1736, 1737, 1738, 1739, 1742, 1743, 1744, 1747, 1748, 1751, 1752, 1753, 1756, 1757, 1758, 1759, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770][i - 1263]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1263 + (i - 1263)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1263 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1263).take (i - 1263))).length :=
      instructionPC_add Artifact.submissionArtifact 1263 (i - 1263)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1306 ≤ i) (hii : i ≤ 1346) :
    Artifact.submissionArtifact.instructionPC i =
      [1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1786, 1787, 1789, 1790, 1791, 1794, 1795, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817][i - 1306]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1306 + (i - 1306)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1306 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1306).take (i - 1306))).length :=
      instructionPC_add Artifact.submissionArtifact 1306 (i - 1306)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1347 ≤ i) (hii : i ≤ 1382) :
    Artifact.submissionArtifact.instructionPC i =
      [1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1833, 1834, 1836, 1837, 1838, 1839, 1840, 1841, 1843, 1844, 1845, 1848, 1849, 1850, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860][i - 1347]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1347 + (i - 1347)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1347 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1347).take (i - 1347))).length :=
      instructionPC_add Artifact.submissionArtifact 1347 (i - 1347)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1383 ≤ i) (hii : i ≤ 1423) :
    Artifact.submissionArtifact.instructionPC i =
      [1863, 1864, 1865, 1866, 1869, 1870, 1871, 1874, 1875, 1876, 1879, 1880, 1882, 1883, 1884, 1885, 1886, 1887, 1890, 1891, 1892, 1893, 1894, 1897, 1898, 1899, 1902, 1903, 1904, 1905, 1906, 1908, 1909, 1910, 1911, 1912, 1913, 1915, 1916, 1917, 1918][i - 1383]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1383 + (i - 1383)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1383 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1383).take (i - 1383))).length :=
      instructionPC_add Artifact.submissionArtifact 1383 (i - 1383)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1424 ≤ i) (hii : i ≤ 1464) :
    Artifact.submissionArtifact.instructionPC i =
      [1919, 1920, 1921, 1922, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1951, 1952, 1953, 1954, 1956, 1957, 1958, 1959, 1960, 1962, 1963, 1964][i - 1424]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1424 + (i - 1424)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1424 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1424).take (i - 1424))).length :=
      instructionPC_add Artifact.submissionArtifact 1424 (i - 1424)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1465 ≤ i) (hii : i ≤ 1488) :
    Artifact.submissionArtifact.instructionPC i =
      [1965, 1968, 1969, 1970, 1973, 1974, 1975, 1976, 1977, 1980, 1981, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996][i - 1465]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1465 + (i - 1465)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1465 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1465).take (i - 1465))).length :=
      instructionPC_add Artifact.submissionArtifact 1465 (i - 1465)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1489 ≤ i) (hii : i ≤ 1531) :
    Artifact.submissionArtifact.instructionPC i =
      [1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2010, 2011, 2012, 2013, 2015, 2016, 2017, 2018, 2019, 2021, 2022, 2023, 2024, 2027, 2028, 2029, 2032, 2033, 2034, 2035, 2036, 2037, 2040, 2041, 2042, 2045, 2046, 2047, 2050, 2051, 2054][i - 1489]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1489 + (i - 1489)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1489 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1489).take (i - 1489))).length :=
      instructionPC_add Artifact.submissionArtifact 1489 (i - 1489)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1532 ≤ i) (hii : i ≤ 1534) :
    Artifact.submissionArtifact.instructionPC i =
      [2055, 2056, 2057][i - 1532]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1532 + (i - 1532)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1532 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1532).take (i - 1532))).length :=
      instructionPC_add Artifact.submissionArtifact 1532 (i - 1532)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1535 ≤ i) (hii : i ≤ 1551) :
    Artifact.submissionArtifact.instructionPC i =
      [2058, 2059, 2062, 2063, 2064, 2065, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2077, 2078, 2079, 2080][i - 1535]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1535 + (i - 1535)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1535 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1535).take (i - 1535))).length :=
      instructionPC_add Artifact.submissionArtifact 1535 (i - 1535)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1552 ≤ i) (hii : i ≤ 1564) :
    Artifact.submissionArtifact.instructionPC i =
      [2081, 2082, 2083, 2084, 2086, 2087, 2088, 2091, 2092, 2094, 2097, 2098, 2101][i - 1552]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1552 + (i - 1552)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1552 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1552).take (i - 1552))).length :=
      instructionPC_add Artifact.submissionArtifact 1552 (i - 1552)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1565 ≤ i) (hii : i ≤ 1599) :
    Artifact.submissionArtifact.instructionPC i =
      [2102, 2103, 2104, 2107, 2108, 2109, 2110, 2111, 2112, 2113, 2114, 2117, 2118, 2120, 2123, 2124, 2125, 2126, 2127, 2129, 2130, 2131, 2132, 2134, 2135, 2136, 2137, 2139, 2140, 2141, 2143, 2144, 2146, 2147, 2150][i - 1565]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1565 + (i - 1565)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1565 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1565).take (i - 1565))).length :=
      instructionPC_add Artifact.submissionArtifact 1565 (i - 1565)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1600 ≤ i) (hii : i ≤ 1611) :
    Artifact.submissionArtifact.instructionPC i =
      [2151, 2152, 2153, 2156, 2157, 2160, 2161, 2164, 2167, 2168, 2171, 2174][i - 1600]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1600 + (i - 1600)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1600 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1600).take (i - 1600))).length :=
      instructionPC_add Artifact.submissionArtifact 1600 (i - 1600)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2228 ≤ i) (hii : i ≤ 2273) :
    Artifact.submissionArtifact.instructionPC i =
      [2872, 2873, 2874, 2875, 2876, 2877, 2878, 2880, 2881, 2882, 2883, 2886, 2887, 2888, 2890, 2893, 2894, 2897, 2900, 2903, 2906, 2909, 2910, 2911, 2912, 2914, 2915, 2917, 2918, 2919, 2920, 2922, 2923, 2924, 2926, 2927, 2929, 2930, 2931, 2932, 2933, 2936, 2937, 2938, 2940, 2943][i - 2228]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2228 + (i - 2228)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2228 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2228).take (i - 2228))).length :=
      instructionPC_add Artifact.submissionArtifact 2228 (i - 2228)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1054 = true :=
  Artifact.isValidJumpDest_index 813 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1300 = true :=
  Artifact.isValidJumpDest_index 997 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1322 = true :=
  Artifact.isValidJumpDest_index 1007 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1337 = true :=
  Artifact.isValidJumpDest_index 1014 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1356 = true :=
  Artifact.isValidJumpDest_index 1026 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1371 = true :=
  Artifact.isValidJumpDest_index 1037 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1383 = true :=
  Artifact.isValidJumpDest_index 1045 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1407 = true :=
  Artifact.isValidJumpDest_index 1057 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1442 = true :=
  Artifact.isValidJumpDest_index 1078 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1450 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1469 = true :=
  Artifact.isValidJumpDest_index 1092 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3138 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1474 = true :=
  Artifact.isValidJumpDest_index 1095 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1486 = true :=
  Artifact.isValidJumpDest_index 1103 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1501 = true :=
  Artifact.isValidJumpDest_index 1110 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1526 = true :=
  Artifact.isValidJumpDest_index 1123 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1527 = true :=
  Artifact.isValidJumpDest_index 1124 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1545 = true :=
  Artifact.isValidJumpDest_index 1136 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1571 = true :=
  Artifact.isValidJumpDest_index 1149 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1581 = true :=
  Artifact.isValidJumpDest_index 1157 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1587 = true :=
  Artifact.isValidJumpDest_index 1161 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1598 = true :=
  Artifact.isValidJumpDest_index 1170 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1602 = true :=
  Artifact.isValidJumpDest_index 1172 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1613 = true :=
  Artifact.isValidJumpDest_index 1179 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1626 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1661 = true :=
  Artifact.isValidJumpDest_index 1216 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1675 = true :=
  Artifact.isValidJumpDest_index 1226 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1799 = true :=
  Artifact.isValidJumpDest_index 1328 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1898 = true :=
  Artifact.isValidJumpDest_index 1407 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1929 = true :=
  Artifact.isValidJumpDest_index 1432 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1985 = true :=
  Artifact.isValidJumpDest_index 1477 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2058 = true :=
  Artifact.isValidJumpDest_index 1535 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2069 = true :=
  Artifact.isValidJumpDest_index 1542 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2081 = true :=
  Artifact.isValidJumpDest_index 1552 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2102 = true :=
  Artifact.isValidJumpDest_index 1565 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2124 = true :=
  Artifact.isValidJumpDest_index 1580 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2151 = true :=
  Artifact.isValidJumpDest_index 1600 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2837 = true :=
  Artifact.isValidJumpDest_index 2205 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2872 = true :=
  Artifact.isValidJumpDest_index 2228 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2910 = true :=
  Artifact.isValidJumpDest_index 2250 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4669 = true :=
  Artifact.isValidJumpDest_index 3560 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4925 = true :=
  Artifact.isValidJumpDest_index 3722 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5176 = true :=
  Artifact.isValidJumpDest_index 3903 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5165 = true :=
  Artifact.isValidJumpDest_index 3896 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
