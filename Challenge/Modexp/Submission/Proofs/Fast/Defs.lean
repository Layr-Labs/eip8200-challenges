import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
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
    Artifact.submissionArtifact.instructionPC 421 = 597 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 449 = 635 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 484 = 685 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 519 = 728 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 551 = 768 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 581 = 824 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 601 = 852 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 640 = 920 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 665 = 967 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 707 = 1041 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 735 = 1083 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 774 = 1134 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 811 = 1171 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 854 = 1230 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 895 = 1277 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 931 = 1322 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 972 = 1378 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1013 = 1424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1037 = 1456 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1080 = 1514 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1083 = 1517 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1100 = 1540 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1113 = 1561 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1148 = 1610 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 1749 = 2301 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 421 ≤ i) (hii : i ≤ 448) :
    Artifact.submissionArtifact.instructionPC i =
      [597,598,600,601,603,604,605,607,608,611,612,614,615,616,617,619,620,621,623,624,625,627,628,630,631,632,633,634][i - 421]! := by
  have hsplit : i = 421 + (i - 421) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 449 ≤ i) (hii : i ≤ 483) :
    Artifact.submissionArtifact.instructionPC i =
      [635,636,637,638,639,641,642,643,644,647,648,650,651,652,653,654,655,657,658,659,662,663,664,667,668,669,671,672,675,676,678,679,680,681,684][i - 449]! := by
  have hsplit : i = 449 + (i - 449) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 484 ≤ i) (hii : i ≤ 518) :
    Artifact.submissionArtifact.instructionPC i =
      [685,686,689,690,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,711,712,714,715,716,717,718,720,721,722,723,724,725,727][i - 484]! := by
  have hsplit : i = 484 + (i - 484) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 519 ≤ i) (hii : i ≤ 550) :
    Artifact.submissionArtifact.instructionPC i =
      [728,729,730,731,732,734,735,736,737,738,739,741,742,743,744,745,746,748,749,750,751,752,753,755,756,757,758,759,762,763,764,765][i - 519]! := by
  have hsplit : i = 519 + (i - 519) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor3]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 551 ≤ i) (hii : i ≤ 580) :
    Artifact.submissionArtifact.instructionPC i =
      [768,769,770,773,774,777,780,781,784,787,790,791,792,795,798,799,802,805,806,807,808,809,810,812,813,815,816,819,820,823][i - 551]! := by
  have hsplit : i = 551 + (i - 551) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor4]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 581 ≤ i) (hii : i ≤ 600) :
    Artifact.submissionArtifact.instructionPC i =
      [824,825,826,827,828,831,832,833,834,835,838,839,840,841,842,843,846,847,850,851][i - 581]! := by
  have hsplit : i = 581 + (i - 581) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor5]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 601 ≤ i) (hii : i ≤ 639) :
    Artifact.submissionArtifact.instructionPC i =
      [852,853,854,855,858,859,862,865,868,871,874,875,876,877,878,879,881,882,883,884,886,887,888,889,892,893,894,897,900,903,906,909,910,911,913,914,917,918,919][i - 601]! := by
  have hsplit : i = 601 + (i - 601) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor6]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 640 ≤ i) (hii : i ≤ 664) :
    Artifact.submissionArtifact.instructionPC i =
      [920,921,924,927,930,933,936,937,938,939,940,941,944,945,948,949,950,953,956,957,960,963,964,965,966][i - 640]! := by
  have hsplit : i = 640 + (i - 640) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor7]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 665 ≤ i) (hii : i ≤ 706) :
    Artifact.submissionArtifact.instructionPC i =
      [967,968,969,972,973,976,979,982,985,988,989,990,991,994,995,996,999,1000,1001,1002,1004,1005,1008,1009,1010,1011,1013,1014,1017,1018,1019,1022,1025,1028,1031,1034,1035,1036,1037,1038,1039,1040][i - 665]! := by
  have hsplit : i = 665 + (i - 665) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 707 ≤ i) (hii : i ≤ 734) :
    Artifact.submissionArtifact.instructionPC i =
      [1041,1044,1045,1046,1047,1048,1049,1052,1053,1054,1056,1057,1058,1061,1062,1065,1066,1067,1068,1071,1072,1073,1075,1076,1077,1078,1081,1082][i - 707]! := by
  have hsplit : i = 707 + (i - 707) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 735 ≤ i) (hii : i ≤ 773) :
    Artifact.submissionArtifact.instructionPC i =
      [1083,1084,1085,1086,1089,1090,1091,1093,1094,1095,1098,1099,1100,1101,1102,1104,1105,1106,1108,1109,1110,1111,1112,1113,1114,1116,1117,1118,1119,1120,1121,1122,1123,1124,1127,1128,1129,1132,1133][i - 735]! := by
  have hsplit : i = 735 + (i - 735) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 774 ≤ i) (hii : i ≤ 810) :
    Artifact.submissionArtifact.instructionPC i =
      [1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170][i - 774]! := by
  have hsplit : i = 774 + (i - 774) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor11]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 811 ≤ i) (hii : i ≤ 853) :
    Artifact.submissionArtifact.instructionPC i =
      [1171,1172,1174,1175,1176,1177,1179,1180,1181,1182,1183,1184,1185,1188,1189,1190,1191,1192,1195,1196,1197,1198,1201,1202,1203,1206,1207,1210,1211,1212,1215,1216,1217,1218,1221,1222,1223,1224,1225,1226,1227,1228,1229][i - 811]! := by
  have hsplit : i = 811 + (i - 811) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor12]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 854 ≤ i) (hii : i ≤ 894) :
    Artifact.submissionArtifact.instructionPC i =
      [1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1245,1246,1248,1249,1250,1253,1254,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276][i - 854]! := by
  have hsplit : i = 854 + (i - 854) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor13]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 895 ≤ i) (hii : i ≤ 930) :
    Artifact.submissionArtifact.instructionPC i =
      [1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1292,1293,1295,1296,1297,1298,1299,1300,1302,1303,1304,1307,1308,1309,1312,1313,1314,1315,1316,1317,1318,1319][i - 895]! := by
  have hsplit : i = 895 + (i - 895) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor14]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 931 ≤ i) (hii : i ≤ 971) :
    Artifact.submissionArtifact.instructionPC i =
      [1322,1323,1324,1325,1328,1329,1330,1333,1334,1335,1338,1339,1341,1342,1343,1344,1345,1346,1349,1350,1351,1352,1353,1356,1357,1358,1361,1362,1363,1364,1365,1367,1368,1369,1370,1371,1372,1374,1375,1376,1377][i - 931]! := by
  have hsplit : i = 931 + (i - 931) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 972 ≤ i) (hii : i ≤ 1012) :
    Artifact.submissionArtifact.instructionPC i =
      [1378,1379,1380,1381,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1410,1411,1412,1413,1415,1416,1417,1418,1419,1421,1422,1423][i - 972]! := by
  have hsplit : i = 972 + (i - 972) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor16]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1013 ≤ i) (hii : i ≤ 1036) :
    Artifact.submissionArtifact.instructionPC i =
      [1424,1427,1428,1429,1432,1433,1434,1435,1436,1439,1440,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455][i - 1013]! := by
  have hsplit : i = 1013 + (i - 1013) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor17]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1037 ≤ i) (hii : i ≤ 1079) :
    Artifact.submissionArtifact.instructionPC i =
      [1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1469,1470,1471,1472,1474,1475,1476,1477,1478,1480,1481,1482,1483,1486,1487,1488,1491,1492,1493,1494,1495,1496,1499,1500,1501,1504,1505,1506,1509,1510,1513][i - 1037]! := by
  have hsplit : i = 1037 + (i - 1037) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor18]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1080 ≤ i) (hii : i ≤ 1082) :
    Artifact.submissionArtifact.instructionPC i =
      [1514,1515,1516][i - 1080]! := by
  have hsplit : i = 1080 + (i - 1080) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor19]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1083 ≤ i) (hii : i ≤ 1099) :
    Artifact.submissionArtifact.instructionPC i =
      [1517,1518,1521,1522,1523,1524,1527,1528,1529,1530,1531,1532,1533,1536,1537,1538,1539][i - 1083]! := by
  have hsplit : i = 1083 + (i - 1083) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor20]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1100 ≤ i) (hii : i ≤ 1112) :
    Artifact.submissionArtifact.instructionPC i =
      [1540,1541,1542,1543,1545,1546,1547,1550,1551,1553,1556,1557,1560][i - 1100]! := by
  have hsplit : i = 1100 + (i - 1100) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor21]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1113 ≤ i) (hii : i ≤ 1147) :
    Artifact.submissionArtifact.instructionPC i =
      [1561,1562,1563,1566,1567,1568,1569,1570,1571,1572,1573,1576,1577,1579,1582,1583,1584,1585,1586,1588,1589,1590,1591,1593,1594,1595,1596,1598,1599,1600,1602,1603,1605,1606,1609][i - 1113]! := by
  have hsplit : i = 1113 + (i - 1113) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor22]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1148 ≤ i) (hii : i ≤ 1159) :
    Artifact.submissionArtifact.instructionPC i =
      [1610,1611,1612,1615,1616,1619,1620,1623,1626,1627,1630,1633][i - 1148]! := by
  have hsplit : i = 1148 + (i - 1148) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor23]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 1749 ≤ i) (hii : i ≤ 1794) :
    Artifact.submissionArtifact.instructionPC i =
      [2301,2302,2303,2304,2305,2306,2307,2309,2310,2311,2312,2315,2316,2317,2319,2322,2323,2326,2329,2332,2335,2338,2339,2340,2341,2343,2344,2346,2347,2348,2349,2351,2352,2353,2355,2356,2358,2359,2360,2361,2362,2364,2365,2366,2368,2371][i - 1749]! := by
  have hsplit : i = 1749 + (i - 1749) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor24]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 551 = true :=
  Artifact.isValidJumpDest_index 387 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 769 = true :=
  Artifact.isValidJumpDest_index 552 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 791 = true :=
  Artifact.isValidJumpDest_index 562 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 806 = true :=
  Artifact.isValidJumpDest_index 569 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 824 = true :=
  Artifact.isValidJumpDest_index 581 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 839 = true :=
  Artifact.isValidJumpDest_index 592 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 851 = true :=
  Artifact.isValidJumpDest_index 600 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 875 = true :=
  Artifact.isValidJumpDest_index 612 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 910 = true :=
  Artifact.isValidJumpDest_index 633 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 918 = true :=
  Artifact.isValidJumpDest_index 638 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 937 = true :=
  Artifact.isValidJumpDest_index 647 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2439 = true :=
  Artifact.isValidJumpDest_index 1843 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 937 = true :=
  Artifact.isValidJumpDest_index 647 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 949 = true :=
  Artifact.isValidJumpDest_index 655 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 964 = true :=
  Artifact.isValidJumpDest_index 662 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 989 = true :=
  Artifact.isValidJumpDest_index 675 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 990 = true :=
  Artifact.isValidJumpDest_index 676 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1009 = true :=
  Artifact.isValidJumpDest_index 688 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1037 = true :=
  Artifact.isValidJumpDest_index 703 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1047 = true :=
  Artifact.isValidJumpDest_index 711 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1053 = true :=
  Artifact.isValidJumpDest_index 715 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1057 = true :=
  Artifact.isValidJumpDest_index 718 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1061 = true :=
  Artifact.isValidJumpDest_index 720 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1072 = true :=
  Artifact.isValidJumpDest_index 727 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1085 = true :=
  Artifact.isValidJumpDest_index 737 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1120 = true :=
  Artifact.isValidJumpDest_index 764 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1134 = true :=
  Artifact.isValidJumpDest_index 774 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1258 = true :=
  Artifact.isValidJumpDest_index 876 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1357 = true :=
  Artifact.isValidJumpDest_index 955 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1388 = true :=
  Artifact.isValidJumpDest_index 980 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1444 = true :=
  Artifact.isValidJumpDest_index 1025 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1517 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1528 = true :=
  Artifact.isValidJumpDest_index 1090 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1540 = true :=
  Artifact.isValidJumpDest_index 1100 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1561 = true :=
  Artifact.isValidJumpDest_index 1113 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1583 = true :=
  Artifact.isValidJumpDest_index 1128 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1610 = true :=
  Artifact.isValidJumpDest_index 1148 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2266 = true :=
  Artifact.isValidJumpDest_index 1726 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2301 = true :=
  Artifact.isValidJumpDest_index 1749 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2339 = true :=
  Artifact.isValidJumpDest_index 1771 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4128 = true :=
  Artifact.isValidJumpDest_index 3135 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4295 = true :=
  Artifact.isValidJumpDest_index 3252 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4551 = true :=
  Artifact.isValidJumpDest_index 3436 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4540 = true :=
  Artifact.isValidJumpDest_index 3429 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
