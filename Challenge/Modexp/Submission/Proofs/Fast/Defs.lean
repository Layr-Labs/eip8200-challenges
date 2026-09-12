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
    Artifact.submissionArtifact.instructionPC 895 = 1169 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 921 = 1204 := by
  calc
    Artifact.submissionArtifact.instructionPC 921 =
        Artifact.submissionArtifact.instructionPC 895 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 895).take 26)).length :=
      instructionPC_add Artifact.submissionArtifact 895 26
    _ = 1204 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 960 = 1260 := by
  calc
    Artifact.submissionArtifact.instructionPC 960 =
        Artifact.submissionArtifact.instructionPC 921 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 921).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 921 39
    _ = 1260 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 996 = 1303 := by
  calc
    Artifact.submissionArtifact.instructionPC 996 =
        Artifact.submissionArtifact.instructionPC 960 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 960).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 960 36
    _ = 1303 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 1031 = 1347 := by
  calc
    Artifact.submissionArtifact.instructionPC 1031 =
        Artifact.submissionArtifact.instructionPC 996 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 996).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 996 35
    _ = 1347 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 1061 = 1404 := by
  calc
    Artifact.submissionArtifact.instructionPC 1061 =
        Artifact.submissionArtifact.instructionPC 1031 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1031).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 1031 30
    _ = 1404 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 1081 = 1432 := by
  calc
    Artifact.submissionArtifact.instructionPC 1081 =
        Artifact.submissionArtifact.instructionPC 1061 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1061).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 1061 20
    _ = 1432 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 1120 = 1500 := by
  calc
    Artifact.submissionArtifact.instructionPC 1120 =
        Artifact.submissionArtifact.instructionPC 1081 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1081).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1081 39
    _ = 1500 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 1148 = 1552 := by
  calc
    Artifact.submissionArtifact.instructionPC 1148 =
        Artifact.submissionArtifact.instructionPC 1120 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1120).take 28)).length :=
      instructionPC_add Artifact.submissionArtifact 1120 28
    _ = 1552 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 1188 = 1623 := by
  calc
    Artifact.submissionArtifact.instructionPC 1188 =
        Artifact.submissionArtifact.instructionPC 1148 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1148).take 40)).length :=
      instructionPC_add Artifact.submissionArtifact 1148 40
    _ = 1623 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 1222 = 1672 := by
  calc
    Artifact.submissionArtifact.instructionPC 1222 =
        Artifact.submissionArtifact.instructionPC 1188 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1188).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 1188 34
    _ = 1672 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 1261 = 1723 := by
  calc
    Artifact.submissionArtifact.instructionPC 1261 =
        Artifact.submissionArtifact.instructionPC 1222 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1222).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 1222 39
    _ = 1723 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 1298 = 1760 := by
  calc
    Artifact.submissionArtifact.instructionPC 1298 =
        Artifact.submissionArtifact.instructionPC 1261 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1261).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 1261 37
    _ = 1760 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 1341 = 1819 := by
  calc
    Artifact.submissionArtifact.instructionPC 1341 =
        Artifact.submissionArtifact.instructionPC 1298 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1298).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1298 43
    _ = 1819 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 1382 = 1866 := by
  calc
    Artifact.submissionArtifact.instructionPC 1382 =
        Artifact.submissionArtifact.instructionPC 1341 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1341).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1341 41
    _ = 1866 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1418 = 1911 := by
  calc
    Artifact.submissionArtifact.instructionPC 1418 =
        Artifact.submissionArtifact.instructionPC 1382 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1382).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 1382 36
    _ = 1911 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1459 = 1967 := by
  calc
    Artifact.submissionArtifact.instructionPC 1459 =
        Artifact.submissionArtifact.instructionPC 1418 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1418).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1418 41
    _ = 1967 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1500 = 2013 := by
  calc
    Artifact.submissionArtifact.instructionPC 1500 =
        Artifact.submissionArtifact.instructionPC 1459 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1459).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1459 41
    _ = 2013 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1524 = 2045 := by
  calc
    Artifact.submissionArtifact.instructionPC 1524 =
        Artifact.submissionArtifact.instructionPC 1500 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1500).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1500 24
    _ = 2045 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1567 = 2103 := by
  calc
    Artifact.submissionArtifact.instructionPC 1567 =
        Artifact.submissionArtifact.instructionPC 1524 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1524).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1524 43
    _ = 2103 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1570 = 2106 := by
  calc
    Artifact.submissionArtifact.instructionPC 1570 =
        Artifact.submissionArtifact.instructionPC 1567 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1567).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1567 3
    _ = 2106 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1587 = 2129 := by
  calc
    Artifact.submissionArtifact.instructionPC 1587 =
        Artifact.submissionArtifact.instructionPC 1570 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1570).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1570 17
    _ = 2129 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1600 = 2150 := by
  calc
    Artifact.submissionArtifact.instructionPC 1600 =
        Artifact.submissionArtifact.instructionPC 1587 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1587).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1587 13
    _ = 2150 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1635 = 2199 := by
  calc
    Artifact.submissionArtifact.instructionPC 1635 =
        Artifact.submissionArtifact.instructionPC 1600 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1600).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1600 35
    _ = 2199 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 2258 = 2913 := by
  calc
    Artifact.submissionArtifact.instructionPC 2258 =
        Artifact.submissionArtifact.instructionPC 1635 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1635).take 623)).length :=
      instructionPC_add Artifact.submissionArtifact 1635 623
    _ = 2913 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 895 ≤ i) (hii : i ≤ 920) :
    Artifact.submissionArtifact.instructionPC i =
      [1169,1170,1172,1173,1174,1176,1177,1180,1181,1183,1184,1185,1186,1187,1189,1190,1192,1193,1194,1196,1197,1198,1199,1200,1202,1203][i - 895]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (895 + (i - 895)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 895 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 895).take (i - 895))).length :=
      instructionPC_add Artifact.submissionArtifact 895 (i - 895)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 921 ≤ i) (hii : i ≤ 959) :
    Artifact.submissionArtifact.instructionPC i =
      [1204,1205,1206,1208,1209,1210,1211,1212,1213,1214,1217,1218,1220,1221,1222,1223,1224,1225,1227,1228,1229,1232,1233,1234,1237,1238,1239,1242,1243,1244,1246,1247,1250,1251,1253,1254,1255,1256,1259][i - 921]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (921 + (i - 921)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 921 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 921).take (i - 921))).length :=
      instructionPC_add Artifact.submissionArtifact 921 (i - 921)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 960 ≤ i) (hii : i ≤ 995) :
    Artifact.submissionArtifact.instructionPC i =
      [1260,1261,1264,1265,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1286,1287,1288,1289,1290,1292,1293,1294,1295,1296,1297,1299,1300,1301,1302][i - 960]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (960 + (i - 960)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 960 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 960).take (i - 960))).length :=
      instructionPC_add Artifact.submissionArtifact 960 (i - 960)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 996 ≤ i) (hii : i ≤ 1030) :
    Artifact.submissionArtifact.instructionPC i =
      [1303,1304,1306,1307,1308,1309,1310,1311,1313,1314,1315,1316,1317,1318,1320,1321,1322,1323,1324,1325,1327,1328,1329,1330,1331,1332,1334,1335,1336,1337,1338,1341,1342,1343,1344][i - 996]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (996 + (i - 996)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 996 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 996).take (i - 996))).length :=
      instructionPC_add Artifact.submissionArtifact 996 (i - 996)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 1031 ≤ i) (hii : i ≤ 1060) :
    Artifact.submissionArtifact.instructionPC i =
      [1347,1348,1349,1352,1353,1356,1359,1360,1363,1366,1369,1370,1371,1374,1377,1378,1381,1384,1385,1386,1387,1388,1389,1391,1392,1395,1396,1399,1400,1403][i - 1031]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1031 + (i - 1031)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1031 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1031).take (i - 1031))).length :=
      instructionPC_add Artifact.submissionArtifact 1031 (i - 1031)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 1061 ≤ i) (hii : i ≤ 1080) :
    Artifact.submissionArtifact.instructionPC i =
      [1404,1405,1406,1407,1408,1411,1412,1413,1414,1415,1418,1419,1420,1421,1422,1423,1426,1427,1430,1431][i - 1061]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1061 + (i - 1061)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1061 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1061).take (i - 1061))).length :=
      instructionPC_add Artifact.submissionArtifact 1061 (i - 1061)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 1081 ≤ i) (hii : i ≤ 1119) :
    Artifact.submissionArtifact.instructionPC i =
      [1432,1433,1434,1435,1438,1439,1442,1445,1448,1451,1454,1455,1456,1457,1458,1459,1461,1462,1463,1464,1466,1467,1468,1469,1472,1473,1474,1477,1480,1483,1486,1489,1490,1491,1493,1494,1497,1498,1499][i - 1081]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1081 + (i - 1081)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1081 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1081).take (i - 1081))).length :=
      instructionPC_add Artifact.submissionArtifact 1081 (i - 1081)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 1120 ≤ i) (hii : i ≤ 1147) :
    Artifact.submissionArtifact.instructionPC i =
      [1500,1501,1504,1507,1510,1513,1516,1517,1518,1521,1522,1523,1524,1525,1526,1529,1530,1533,1534,1535,1538,1541,1542,1545,1548,1549,1550,1551][i - 1120]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1120 + (i - 1120)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1120 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1120).take (i - 1120))).length :=
      instructionPC_add Artifact.submissionArtifact 1120 (i - 1120)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 1148 ≤ i) (hii : i ≤ 1187) :
    Artifact.submissionArtifact.instructionPC i =
      [1552,1553,1554,1557,1558,1561,1564,1567,1570,1573,1574,1575,1576,1578,1579,1580,1583,1584,1585,1586,1588,1589,1592,1593,1594,1595,1597,1598,1601,1602,1603,1606,1609,1612,1615,1618,1619,1620,1621,1622][i - 1148]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1148 + (i - 1148)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1148 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1148).take (i - 1148))).length :=
      instructionPC_add Artifact.submissionArtifact 1148 (i - 1148)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 1188 ≤ i) (hii : i ≤ 1221) :
    Artifact.submissionArtifact.instructionPC i =
      [1623,1626,1627,1628,1629,1630,1631,1634,1635,1636,1637,1638,1639,1640,1641,1642,1645,1646,1647,1650,1651,1654,1655,1656,1657,1660,1661,1662,1664,1665,1666,1667,1670,1671][i - 1188]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1188 + (i - 1188)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1188 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1188).take (i - 1188))).length :=
      instructionPC_add Artifact.submissionArtifact 1188 (i - 1188)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 1222 ≤ i) (hii : i ≤ 1260) :
    Artifact.submissionArtifact.instructionPC i =
      [1672,1673,1674,1675,1678,1679,1680,1682,1683,1684,1687,1688,1689,1690,1691,1693,1694,1695,1697,1698,1699,1700,1701,1702,1703,1705,1706,1707,1708,1709,1710,1711,1712,1713,1716,1717,1718,1721,1722][i - 1222]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1222 + (i - 1222)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1222 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1222).take (i - 1222))).length :=
      instructionPC_add Artifact.submissionArtifact 1222 (i - 1222)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 1261 ≤ i) (hii : i ≤ 1297) :
    Artifact.submissionArtifact.instructionPC i =
      [1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759][i - 1261]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1261 + (i - 1261)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1261 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1261).take (i - 1261))).length :=
      instructionPC_add Artifact.submissionArtifact 1261 (i - 1261)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 1298 ≤ i) (hii : i ≤ 1340) :
    Artifact.submissionArtifact.instructionPC i =
      [1760,1761,1763,1764,1765,1766,1768,1769,1770,1771,1772,1773,1774,1777,1778,1779,1780,1781,1784,1785,1786,1787,1790,1791,1792,1795,1796,1799,1800,1801,1804,1805,1806,1807,1810,1811,1812,1813,1814,1815,1816,1817,1818][i - 1298]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1298 + (i - 1298)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1298 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1298).take (i - 1298))).length :=
      instructionPC_add Artifact.submissionArtifact 1298 (i - 1298)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 1341 ≤ i) (hii : i ≤ 1381) :
    Artifact.submissionArtifact.instructionPC i =
      [1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1834,1835,1837,1838,1839,1842,1843,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865][i - 1341]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1341 + (i - 1341)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1341 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1341).take (i - 1341))).length :=
      instructionPC_add Artifact.submissionArtifact 1341 (i - 1341)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 1382 ≤ i) (hii : i ≤ 1417) :
    Artifact.submissionArtifact.instructionPC i =
      [1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1881,1882,1884,1885,1886,1887,1888,1889,1891,1892,1893,1896,1897,1898,1901,1902,1903,1904,1905,1906,1907,1908][i - 1382]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1382 + (i - 1382)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1382 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1382).take (i - 1382))).length :=
      instructionPC_add Artifact.submissionArtifact 1382 (i - 1382)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1418 ≤ i) (hii : i ≤ 1458) :
    Artifact.submissionArtifact.instructionPC i =
      [1911,1912,1913,1914,1917,1918,1919,1922,1923,1924,1927,1928,1930,1931,1932,1933,1934,1935,1938,1939,1940,1941,1942,1945,1946,1947,1950,1951,1952,1953,1954,1956,1957,1958,1959,1960,1961,1963,1964,1965,1966][i - 1418]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1418 + (i - 1418)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1418 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1418).take (i - 1418))).length :=
      instructionPC_add Artifact.submissionArtifact 1418 (i - 1418)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1459 ≤ i) (hii : i ≤ 1499) :
    Artifact.submissionArtifact.instructionPC i =
      [1967,1968,1969,1970,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1999,2000,2001,2002,2004,2005,2006,2007,2008,2010,2011,2012][i - 1459]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1459 + (i - 1459)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1459 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1459).take (i - 1459))).length :=
      instructionPC_add Artifact.submissionArtifact 1459 (i - 1459)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1500 ≤ i) (hii : i ≤ 1523) :
    Artifact.submissionArtifact.instructionPC i =
      [2013,2016,2017,2018,2021,2022,2023,2024,2025,2028,2029,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044][i - 1500]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1500 + (i - 1500)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1500 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1500).take (i - 1500))).length :=
      instructionPC_add Artifact.submissionArtifact 1500 (i - 1500)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1524 ≤ i) (hii : i ≤ 1566) :
    Artifact.submissionArtifact.instructionPC i =
      [2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2058,2059,2060,2061,2063,2064,2065,2066,2067,2069,2070,2071,2072,2075,2076,2077,2080,2081,2082,2083,2084,2085,2088,2089,2090,2093,2094,2095,2098,2099,2102][i - 1524]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1524 + (i - 1524)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1524 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1524).take (i - 1524))).length :=
      instructionPC_add Artifact.submissionArtifact 1524 (i - 1524)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1567 ≤ i) (hii : i ≤ 1569) :
    Artifact.submissionArtifact.instructionPC i =
      [2103,2104,2105][i - 1567]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1567 + (i - 1567)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1567 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1567).take (i - 1567))).length :=
      instructionPC_add Artifact.submissionArtifact 1567 (i - 1567)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1570 ≤ i) (hii : i ≤ 1586) :
    Artifact.submissionArtifact.instructionPC i =
      [2106,2107,2110,2111,2112,2113,2116,2117,2118,2119,2120,2121,2122,2125,2126,2127,2128][i - 1570]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1570 + (i - 1570)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1570 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1570).take (i - 1570))).length :=
      instructionPC_add Artifact.submissionArtifact 1570 (i - 1570)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1587 ≤ i) (hii : i ≤ 1599) :
    Artifact.submissionArtifact.instructionPC i =
      [2129,2130,2131,2132,2134,2135,2136,2139,2140,2142,2145,2146,2149][i - 1587]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1587 + (i - 1587)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1587 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1587).take (i - 1587))).length :=
      instructionPC_add Artifact.submissionArtifact 1587 (i - 1587)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1600 ≤ i) (hii : i ≤ 1634) :
    Artifact.submissionArtifact.instructionPC i =
      [2150,2151,2152,2155,2156,2157,2158,2159,2160,2161,2162,2165,2166,2168,2171,2172,2173,2174,2175,2177,2178,2179,2180,2182,2183,2184,2185,2187,2188,2189,2191,2192,2194,2195,2198][i - 1600]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1600 + (i - 1600)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1600 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1600).take (i - 1600))).length :=
      instructionPC_add Artifact.submissionArtifact 1600 (i - 1600)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1635 ≤ i) (hii : i ≤ 1646) :
    Artifact.submissionArtifact.instructionPC i =
      [2199,2200,2201,2204,2205,2208,2209,2212,2215,2216,2219,2222][i - 1635]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1635 + (i - 1635)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1635 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1635).take (i - 1635))).length :=
      instructionPC_add Artifact.submissionArtifact 1635 (i - 1635)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 2258 ≤ i) (hii : i ≤ 2303) :
    Artifact.submissionArtifact.instructionPC i =
      [2913,2914,2915,2916,2917,2918,2919,2921,2922,2923,2924,2927,2928,2929,2931,2934,2935,2938,2941,2944,2947,2950,2951,2952,2953,2955,2956,2958,2959,2960,2961,2963,2964,2965,2967,2968,2970,2971,2972,2973,2974,2977,2978,2979,2981,2984][i - 2258]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2258 + (i - 2258)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2258 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2258).take (i - 2258))).length :=
      instructionPC_add Artifact.submissionArtifact 2258 (i - 2258)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1107 = true :=
  Artifact.isValidJumpDest_index 851 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1348 = true :=
  Artifact.isValidJumpDest_index 1032 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1370 = true :=
  Artifact.isValidJumpDest_index 1042 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1385 = true :=
  Artifact.isValidJumpDest_index 1049 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1404 = true :=
  Artifact.isValidJumpDest_index 1061 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1419 = true :=
  Artifact.isValidJumpDest_index 1072 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1431 = true :=
  Artifact.isValidJumpDest_index 1080 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1455 = true :=
  Artifact.isValidJumpDest_index 1092 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1490 = true :=
  Artifact.isValidJumpDest_index 1113 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1498 = true :=
  Artifact.isValidJumpDest_index 1118 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1517 = true :=
  Artifact.isValidJumpDest_index 1127 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3179 = true :=
  Artifact.isValidJumpDest_index 2460 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1522 = true :=
  Artifact.isValidJumpDest_index 1130 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1534 = true :=
  Artifact.isValidJumpDest_index 1138 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1549 = true :=
  Artifact.isValidJumpDest_index 1145 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1574 = true :=
  Artifact.isValidJumpDest_index 1158 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1575 = true :=
  Artifact.isValidJumpDest_index 1159 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1593 = true :=
  Artifact.isValidJumpDest_index 1171 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1619 = true :=
  Artifact.isValidJumpDest_index 1184 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1629 = true :=
  Artifact.isValidJumpDest_index 1192 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1635 = true :=
  Artifact.isValidJumpDest_index 1196 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1646 = true :=
  Artifact.isValidJumpDest_index 1205 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1650 = true :=
  Artifact.isValidJumpDest_index 1207 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1661 = true :=
  Artifact.isValidJumpDest_index 1214 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1674 = true :=
  Artifact.isValidJumpDest_index 1224 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1709 = true :=
  Artifact.isValidJumpDest_index 1251 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1723 = true :=
  Artifact.isValidJumpDest_index 1261 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1847 = true :=
  Artifact.isValidJumpDest_index 1363 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1946 = true :=
  Artifact.isValidJumpDest_index 1442 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1977 = true :=
  Artifact.isValidJumpDest_index 1467 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2033 = true :=
  Artifact.isValidJumpDest_index 1512 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2106 = true :=
  Artifact.isValidJumpDest_index 1570 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2117 = true :=
  Artifact.isValidJumpDest_index 1577 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2129 = true :=
  Artifact.isValidJumpDest_index 1587 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2150 = true :=
  Artifact.isValidJumpDest_index 1600 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2172 = true :=
  Artifact.isValidJumpDest_index 1615 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2199 = true :=
  Artifact.isValidJumpDest_index 1635 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2878 = true :=
  Artifact.isValidJumpDest_index 2235 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2913 = true :=
  Artifact.isValidJumpDest_index 2258 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2280 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4792 = true :=
  Artifact.isValidJumpDest_index 3714 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5039 = true :=
  Artifact.isValidJumpDest_index 3873 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5290 = true :=
  Artifact.isValidJumpDest_index 4054 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5279 = true :=
  Artifact.isValidJumpDest_index 4047 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
