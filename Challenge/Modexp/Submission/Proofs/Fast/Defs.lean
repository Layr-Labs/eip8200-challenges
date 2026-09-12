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
    Artifact.submissionArtifact.instructionPC 1001 = 1311 := by
  calc
    Artifact.submissionArtifact.instructionPC 1001 =
        Artifact.submissionArtifact.instructionPC 961 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 961).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 961 40
    _ = 1311 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1031 = 1368 := by
  calc
    Artifact.submissionArtifact.instructionPC 1031 =
        Artifact.submissionArtifact.instructionPC 1001 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1001).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1001 30
    _ = 1368 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1051 = 1396 := by
  calc
    Artifact.submissionArtifact.instructionPC 1051 =
        Artifact.submissionArtifact.instructionPC 1031 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1031).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1031 20
    _ = 1396 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1090 = 1464 := by
  calc
    Artifact.submissionArtifact.instructionPC 1090 =
        Artifact.submissionArtifact.instructionPC 1051 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1051).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1051 39
    _ = 1464 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1118 = 1516 := by
  calc
    Artifact.submissionArtifact.instructionPC 1118 =
        Artifact.submissionArtifact.instructionPC 1090 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1090).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1090 28
    _ = 1516 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1158 = 1587 := by
  calc
    Artifact.submissionArtifact.instructionPC 1158 =
        Artifact.submissionArtifact.instructionPC 1118 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1118).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1118 40
    _ = 1587 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1192 = 1636 := by
  calc
    Artifact.submissionArtifact.instructionPC 1192 =
        Artifact.submissionArtifact.instructionPC 1158 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1158).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1158 34
    _ = 1636 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1231 = 1687 := by
  calc
    Artifact.submissionArtifact.instructionPC 1231 =
        Artifact.submissionArtifact.instructionPC 1192 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1192).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1192 39
    _ = 1687 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1268 = 1724 := by
  calc
    Artifact.submissionArtifact.instructionPC 1268 =
        Artifact.submissionArtifact.instructionPC 1231 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1231).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1231 37
    _ = 1724 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1311 = 1783 := by
  calc
    Artifact.submissionArtifact.instructionPC 1311 =
        Artifact.submissionArtifact.instructionPC 1268 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1268).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1268 43
    _ = 1783 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1352 = 1830 := by
  calc
    Artifact.submissionArtifact.instructionPC 1352 =
        Artifact.submissionArtifact.instructionPC 1311 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1311).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1311 41
    _ = 1830 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1388 = 1875 := by
  calc
    Artifact.submissionArtifact.instructionPC 1388 =
        Artifact.submissionArtifact.instructionPC 1352 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1352).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1352 36
    _ = 1875 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1429 = 1931 := by
  calc
    Artifact.submissionArtifact.instructionPC 1429 =
        Artifact.submissionArtifact.instructionPC 1388 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1388).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1388 41
    _ = 1931 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1470 = 1977 := by
  calc
    Artifact.submissionArtifact.instructionPC 1470 =
        Artifact.submissionArtifact.instructionPC 1429 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1429).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1429 41
    _ = 1977 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1494 = 2009 := by
  calc
    Artifact.submissionArtifact.instructionPC 1494 =
        Artifact.submissionArtifact.instructionPC 1470 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1470).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1470 24
    _ = 2009 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1537 = 2067 := by
  calc
    Artifact.submissionArtifact.instructionPC 1537 =
        Artifact.submissionArtifact.instructionPC 1494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1494).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1494 43
    _ = 2067 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1540 = 2070 := by
  calc
    Artifact.submissionArtifact.instructionPC 1540 =
        Artifact.submissionArtifact.instructionPC 1537 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1537).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1537 3
    _ = 2070 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1557 = 2093 := by
  calc
    Artifact.submissionArtifact.instructionPC 1557 =
        Artifact.submissionArtifact.instructionPC 1540 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1540).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1540 17
    _ = 2093 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1570 = 2114 := by
  calc
    Artifact.submissionArtifact.instructionPC 1570 =
        Artifact.submissionArtifact.instructionPC 1557 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1557).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1557 13
    _ = 2114 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1605 = 2163 := by
  calc
    Artifact.submissionArtifact.instructionPC 1605 =
        Artifact.submissionArtifact.instructionPC 1570 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1570).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1570 35
    _ = 2163 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2231 = 2880 := by
  calc
    Artifact.submissionArtifact.instructionPC 2231 =
        Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take 626)).length :=
      instructionPC_add Artifact.submissionArtifact 1605 626
    _ = 2880 := by
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

@[simp] theorem fastPC3 (i : Nat) (hi : 961 ≤ i) (hii : i ≤ 1000) :
    Artifact.submissionArtifact.instructionPC i =
      [1255, 1256, 1258, 1259, 1260, 1261, 1262, 1263, 1265, 1266, 1267, 1268, 1269, 1270, 1272, 1273, 1274, 1275, 1276, 1277, 1279, 1280, 1281, 1282, 1283, 1284, 1286, 1287, 1288, 1289, 1290, 1293, 1294, 1295, 1296, 1298, 1301, 1302, 1305, 1308][i - 961]! := by
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

@[simp] theorem fastPC4 (i : Nat) (hi : 1001 ≤ i) (hii : i ≤ 1030) :
    Artifact.submissionArtifact.instructionPC i =
      [1311, 1312, 1313, 1316, 1317, 1320, 1323, 1324, 1327, 1330, 1333, 1334, 1335, 1338, 1341, 1342, 1345, 1348, 1349, 1350, 1351, 1352, 1353, 1355, 1356, 1359, 1360, 1363, 1364, 1367][i - 1001]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1001 + (i - 1001)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1001 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1001).take (i - 1001))).length :=
      instructionPC_add Artifact.submissionArtifact 1001 (i - 1001)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1031 ≤ i) (hii : i ≤ 1050) :
    Artifact.submissionArtifact.instructionPC i =
      [1368, 1369, 1370, 1371, 1372, 1375, 1376, 1377, 1378, 1379, 1382, 1383, 1384, 1385, 1386, 1387, 1390, 1391, 1394, 1395][i - 1031]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1031 + (i - 1031)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1031 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1031).take (i - 1031))).length :=
      instructionPC_add Artifact.submissionArtifact 1031 (i - 1031)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1051 ≤ i) (hii : i ≤ 1089) :
    Artifact.submissionArtifact.instructionPC i =
      [1396, 1397, 1398, 1399, 1402, 1403, 1406, 1409, 1412, 1415, 1418, 1419, 1420, 1421, 1422, 1423, 1425, 1426, 1427, 1428, 1430, 1431, 1432, 1433, 1436, 1437, 1438, 1441, 1444, 1447, 1450, 1453, 1454, 1455, 1457, 1458, 1461, 1462, 1463][i - 1051]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1051 + (i - 1051)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1051 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1051).take (i - 1051))).length :=
      instructionPC_add Artifact.submissionArtifact 1051 (i - 1051)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1090 ≤ i) (hii : i ≤ 1117) :
    Artifact.submissionArtifact.instructionPC i =
      [1464, 1465, 1468, 1471, 1474, 1477, 1480, 1481, 1482, 1485, 1486, 1487, 1488, 1489, 1490, 1493, 1494, 1497, 1498, 1499, 1502, 1505, 1506, 1509, 1512, 1513, 1514, 1515][i - 1090]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1090 + (i - 1090)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1090 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1090).take (i - 1090))).length :=
      instructionPC_add Artifact.submissionArtifact 1090 (i - 1090)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1118 ≤ i) (hii : i ≤ 1157) :
    Artifact.submissionArtifact.instructionPC i =
      [1516, 1517, 1518, 1521, 1522, 1525, 1528, 1531, 1534, 1537, 1538, 1539, 1540, 1542, 1543, 1544, 1547, 1548, 1549, 1550, 1552, 1553, 1556, 1557, 1558, 1559, 1561, 1562, 1565, 1566, 1567, 1570, 1573, 1576, 1579, 1582, 1583, 1584, 1585, 1586][i - 1118]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1118 + (i - 1118)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1118 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1118).take (i - 1118))).length :=
      instructionPC_add Artifact.submissionArtifact 1118 (i - 1118)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1158 ≤ i) (hii : i ≤ 1191) :
    Artifact.submissionArtifact.instructionPC i =
      [1587, 1590, 1591, 1592, 1593, 1594, 1595, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1609, 1610, 1611, 1614, 1615, 1618, 1619, 1620, 1621, 1624, 1625, 1626, 1628, 1629, 1630, 1631, 1634, 1635][i - 1158]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1158 + (i - 1158)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1158 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1158).take (i - 1158))).length :=
      instructionPC_add Artifact.submissionArtifact 1158 (i - 1158)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1192 ≤ i) (hii : i ≤ 1230) :
    Artifact.submissionArtifact.instructionPC i =
      [1636, 1637, 1638, 1639, 1642, 1643, 1644, 1646, 1647, 1648, 1651, 1652, 1653, 1654, 1655, 1657, 1658, 1659, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1680, 1681, 1682, 1685, 1686][i - 1192]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1192 + (i - 1192)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1192 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1192).take (i - 1192))).length :=
      instructionPC_add Artifact.submissionArtifact 1192 (i - 1192)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1231 ≤ i) (hii : i ≤ 1267) :
    Artifact.submissionArtifact.instructionPC i =
      [1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723][i - 1231]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1231 + (i - 1231)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1231 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1231).take (i - 1231))).length :=
      instructionPC_add Artifact.submissionArtifact 1231 (i - 1231)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1268 ≤ i) (hii : i ≤ 1310) :
    Artifact.submissionArtifact.instructionPC i =
      [1724, 1725, 1727, 1728, 1729, 1730, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1741, 1742, 1743, 1744, 1745, 1748, 1749, 1750, 1751, 1754, 1755, 1756, 1759, 1760, 1763, 1764, 1765, 1768, 1769, 1770, 1771, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782][i - 1268]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1268 + (i - 1268)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1268 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1268).take (i - 1268))).length :=
      instructionPC_add Artifact.submissionArtifact 1268 (i - 1268)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1311 ≤ i) (hii : i ≤ 1351) :
    Artifact.submissionArtifact.instructionPC i =
      [1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1798, 1799, 1801, 1802, 1803, 1806, 1807, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829][i - 1311]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1311 + (i - 1311)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1311 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1311).take (i - 1311))).length :=
      instructionPC_add Artifact.submissionArtifact 1311 (i - 1311)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1352 ≤ i) (hii : i ≤ 1387) :
    Artifact.submissionArtifact.instructionPC i =
      [1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1845, 1846, 1848, 1849, 1850, 1851, 1852, 1853, 1855, 1856, 1857, 1860, 1861, 1862, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872][i - 1352]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1352 + (i - 1352)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1352 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1352).take (i - 1352))).length :=
      instructionPC_add Artifact.submissionArtifact 1352 (i - 1352)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1388 ≤ i) (hii : i ≤ 1428) :
    Artifact.submissionArtifact.instructionPC i =
      [1875, 1876, 1877, 1878, 1881, 1882, 1883, 1886, 1887, 1888, 1891, 1892, 1894, 1895, 1896, 1897, 1898, 1899, 1902, 1903, 1904, 1905, 1906, 1909, 1910, 1911, 1914, 1915, 1916, 1917, 1918, 1920, 1921, 1922, 1923, 1924, 1925, 1927, 1928, 1929, 1930][i - 1388]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1388 + (i - 1388)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1388 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1388).take (i - 1388))).length :=
      instructionPC_add Artifact.submissionArtifact 1388 (i - 1388)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1429 ≤ i) (hii : i ≤ 1469) :
    Artifact.submissionArtifact.instructionPC i =
      [1931, 1932, 1933, 1934, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1963, 1964, 1965, 1966, 1968, 1969, 1970, 1971, 1972, 1974, 1975, 1976][i - 1429]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1429 + (i - 1429)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1429 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1429).take (i - 1429))).length :=
      instructionPC_add Artifact.submissionArtifact 1429 (i - 1429)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1470 ≤ i) (hii : i ≤ 1493) :
    Artifact.submissionArtifact.instructionPC i =
      [1977, 1980, 1981, 1982, 1985, 1986, 1987, 1988, 1989, 1992, 1993, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008][i - 1470]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1470 + (i - 1470)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1470 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1470).take (i - 1470))).length :=
      instructionPC_add Artifact.submissionArtifact 1470 (i - 1470)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1494 ≤ i) (hii : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2022, 2023, 2024, 2025, 2027, 2028, 2029, 2030, 2031, 2033, 2034, 2035, 2036, 2039, 2040, 2041, 2044, 2045, 2046, 2047, 2048, 2049, 2052, 2053, 2054, 2057, 2058, 2059, 2062, 2063, 2066][i - 1494]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1494 + (i - 1494)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1494).take (i - 1494))).length :=
      instructionPC_add Artifact.submissionArtifact 1494 (i - 1494)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1537 ≤ i) (hii : i ≤ 1539) :
    Artifact.submissionArtifact.instructionPC i =
      [2067, 2068, 2069][i - 1537]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1537 + (i - 1537)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1537 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1537).take (i - 1537))).length :=
      instructionPC_add Artifact.submissionArtifact 1537 (i - 1537)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1540 ≤ i) (hii : i ≤ 1556) :
    Artifact.submissionArtifact.instructionPC i =
      [2070, 2071, 2074, 2075, 2076, 2077, 2080, 2081, 2082, 2083, 2084, 2085, 2086, 2089, 2090, 2091, 2092][i - 1540]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1540 + (i - 1540)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1540 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1540).take (i - 1540))).length :=
      instructionPC_add Artifact.submissionArtifact 1540 (i - 1540)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1557 ≤ i) (hii : i ≤ 1569) :
    Artifact.submissionArtifact.instructionPC i =
      [2093, 2094, 2095, 2096, 2098, 2099, 2100, 2103, 2104, 2106, 2109, 2110, 2113][i - 1557]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1557 + (i - 1557)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1557 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1557).take (i - 1557))).length :=
      instructionPC_add Artifact.submissionArtifact 1557 (i - 1557)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1570 ≤ i) (hii : i ≤ 1604) :
    Artifact.submissionArtifact.instructionPC i =
      [2114, 2115, 2116, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2129, 2130, 2132, 2135, 2136, 2137, 2138, 2139, 2141, 2142, 2143, 2144, 2146, 2147, 2148, 2149, 2151, 2152, 2153, 2155, 2156, 2158, 2159, 2162][i - 1570]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1570 + (i - 1570)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1570 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1570).take (i - 1570))).length :=
      instructionPC_add Artifact.submissionArtifact 1570 (i - 1570)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1605 ≤ i) (hii : i ≤ 1616) :
    Artifact.submissionArtifact.instructionPC i =
      [2163, 2164, 2165, 2168, 2169, 2172, 2173, 2176, 2179, 2180, 2183, 2186][i - 1605]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1605 + (i - 1605)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1605 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1605).take (i - 1605))).length :=
      instructionPC_add Artifact.submissionArtifact 1605 (i - 1605)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2231 ≤ i) (hii : i ≤ 2276) :
    Artifact.submissionArtifact.instructionPC i =
      [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2888, 2889, 2890, 2891, 2894, 2895, 2896, 2898, 2901, 2902, 2905, 2908, 2911, 2914, 2917, 2918, 2919, 2920, 2922, 2923, 2925, 2926, 2927, 2928, 2930, 2931, 2932, 2934, 2935, 2937, 2938, 2939, 2940, 2941, 2944, 2945, 2946, 2948, 2951][i - 2231]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2231 + (i - 2231)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2231 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2231).take (i - 2231))).length :=
      instructionPC_add Artifact.submissionArtifact 2231 (i - 2231)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1054 = true :=
  Artifact.isValidJumpDest_index 813 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1312 = true :=
  Artifact.isValidJumpDest_index 1002 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1334 = true :=
  Artifact.isValidJumpDest_index 1012 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1349 = true :=
  Artifact.isValidJumpDest_index 1019 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1368 = true :=
  Artifact.isValidJumpDest_index 1031 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1383 = true :=
  Artifact.isValidJumpDest_index 1042 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1395 = true :=
  Artifact.isValidJumpDest_index 1050 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1419 = true :=
  Artifact.isValidJumpDest_index 1062 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1454 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1462 = true :=
  Artifact.isValidJumpDest_index 1088 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1481 = true :=
  Artifact.isValidJumpDest_index 1097 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2433 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1486 = true :=
  Artifact.isValidJumpDest_index 1100 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1498 = true :=
  Artifact.isValidJumpDest_index 1108 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1513 = true :=
  Artifact.isValidJumpDest_index 1115 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1538 = true :=
  Artifact.isValidJumpDest_index 1128 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1539 = true :=
  Artifact.isValidJumpDest_index 1129 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1557 = true :=
  Artifact.isValidJumpDest_index 1141 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1583 = true :=
  Artifact.isValidJumpDest_index 1154 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1593 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1599 = true :=
  Artifact.isValidJumpDest_index 1166 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1610 = true :=
  Artifact.isValidJumpDest_index 1175 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1614 = true :=
  Artifact.isValidJumpDest_index 1177 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1625 = true :=
  Artifact.isValidJumpDest_index 1184 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1638 = true :=
  Artifact.isValidJumpDest_index 1194 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1673 = true :=
  Artifact.isValidJumpDest_index 1221 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1687 = true :=
  Artifact.isValidJumpDest_index 1231 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1811 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1910 = true :=
  Artifact.isValidJumpDest_index 1412 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1941 = true :=
  Artifact.isValidJumpDest_index 1437 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1997 = true :=
  Artifact.isValidJumpDest_index 1482 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2070 = true :=
  Artifact.isValidJumpDest_index 1540 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2081 = true :=
  Artifact.isValidJumpDest_index 1547 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2093 = true :=
  Artifact.isValidJumpDest_index 1557 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2114 = true :=
  Artifact.isValidJumpDest_index 1570 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2136 = true :=
  Artifact.isValidJumpDest_index 1585 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2163 = true :=
  Artifact.isValidJumpDest_index 1605 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2845 = true :=
  Artifact.isValidJumpDest_index 2208 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2880 = true :=
  Artifact.isValidJumpDest_index 2231 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2918 = true :=
  Artifact.isValidJumpDest_index 2253 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4613 = true :=
  Artifact.isValidJumpDest_index 3549 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4861 = true :=
  Artifact.isValidJumpDest_index 3709 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5112 = true :=
  Artifact.isValidJumpDest_index 3890 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5101 = true :=
  Artifact.isValidJumpDest_index 3883 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
