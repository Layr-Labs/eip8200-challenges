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
    Artifact.submissionArtifact.instructionPC 423 = 599 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 451 = 637 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 486 = 687 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 521 = 730 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 553 = 770 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 583 = 826 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 603 = 854 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 642 = 922 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 667 = 969 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 709 = 1042 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 737 = 1084 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 776 = 1135 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 813 = 1172 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 856 = 1231 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 897 = 1278 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 933 = 1323 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 974 = 1379 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1013 = 1423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1037 = 1455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1080 = 1513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1083 = 1516 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1100 = 1539 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1113 = 1560 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1148 = 1609 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 1753 = 2305 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 423 ≤ i) (hii : i ≤ 450) :
    Artifact.submissionArtifact.instructionPC i =
      [599,600,602,603,605,606,607,609,610,613,614,616,617,618,619,621,622,623,625,626,627,629,630,632,633,634,635,636][i - 423]! := by
  have hsplit : i = 423 + (i - 423) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 451 ≤ i) (hii : i ≤ 485) :
    Artifact.submissionArtifact.instructionPC i =
      [637,638,639,640,641,643,644,645,646,649,650,652,653,654,655,656,657,659,660,661,664,665,666,669,670,671,673,674,677,678,680,681,682,683,686][i - 451]! := by
  have hsplit : i = 451 + (i - 451) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 486 ≤ i) (hii : i ≤ 520) :
    Artifact.submissionArtifact.instructionPC i =
      [687,688,691,692,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,713,714,716,717,718,719,720,722,723,724,725,726,727,729][i - 486]! := by
  have hsplit : i = 486 + (i - 486) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 521 ≤ i) (hii : i ≤ 552) :
    Artifact.submissionArtifact.instructionPC i =
      [730,731,732,733,734,736,737,738,739,740,741,743,744,745,746,747,748,750,751,752,753,754,755,757,758,759,760,761,764,765,766,767][i - 521]! := by
  have hsplit : i = 521 + (i - 521) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor3]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 553 ≤ i) (hii : i ≤ 582) :
    Artifact.submissionArtifact.instructionPC i =
      [770,771,772,775,776,779,782,783,786,789,792,793,794,797,800,801,804,807,808,809,810,811,812,814,815,817,818,821,822,825][i - 553]! := by
  have hsplit : i = 553 + (i - 553) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor4]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 583 ≤ i) (hii : i ≤ 602) :
    Artifact.submissionArtifact.instructionPC i =
      [826,827,828,829,830,833,834,835,836,837,840,841,842,843,844,845,848,849,852,853][i - 583]! := by
  have hsplit : i = 583 + (i - 583) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor5]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 603 ≤ i) (hii : i ≤ 641) :
    Artifact.submissionArtifact.instructionPC i =
      [854,855,856,857,860,861,864,867,870,873,876,877,878,879,880,881,883,884,885,886,888,889,890,891,894,895,896,899,902,905,908,911,912,913,915,916,919,920,921][i - 603]! := by
  have hsplit : i = 603 + (i - 603) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor6]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 642 ≤ i) (hii : i ≤ 666) :
    Artifact.submissionArtifact.instructionPC i =
      [922,923,926,929,932,935,938,939,940,941,942,943,946,947,950,951,952,955,958,959,962,965,966,967,968][i - 642]! := by
  have hsplit : i = 642 + (i - 642) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor7]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 667 ≤ i) (hii : i ≤ 708) :
    Artifact.submissionArtifact.instructionPC i =
      [969,970,971,974,975,978,981,984,987,990,991,992,993,995,996,997,1000,1001,1002,1003,1005,1006,1009,1010,1011,1012,1014,1015,1018,1019,1020,1023,1026,1029,1032,1035,1036,1037,1038,1039,1040,1041][i - 667]! := by
  have hsplit : i = 667 + (i - 667) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 709 ≤ i) (hii : i ≤ 736) :
    Artifact.submissionArtifact.instructionPC i =
      [1042,1045,1046,1047,1048,1049,1050,1053,1054,1055,1057,1058,1059,1062,1063,1066,1067,1068,1069,1072,1073,1074,1076,1077,1078,1079,1082,1083][i - 709]! := by
  have hsplit : i = 709 + (i - 709) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 737 ≤ i) (hii : i ≤ 775) :
    Artifact.submissionArtifact.instructionPC i =
      [1084,1085,1086,1087,1090,1091,1092,1094,1095,1096,1099,1100,1101,1102,1103,1105,1106,1107,1109,1110,1111,1112,1113,1114,1115,1117,1118,1119,1120,1121,1122,1123,1124,1125,1128,1129,1130,1133,1134][i - 737]! := by
  have hsplit : i = 737 + (i - 737) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 776 ≤ i) (hii : i ≤ 812) :
    Artifact.submissionArtifact.instructionPC i =
      [1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171][i - 776]! := by
  have hsplit : i = 776 + (i - 776) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor11]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 813 ≤ i) (hii : i ≤ 855) :
    Artifact.submissionArtifact.instructionPC i =
      [1172,1173,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1189,1190,1191,1192,1193,1196,1197,1198,1199,1202,1203,1204,1207,1208,1211,1212,1213,1216,1217,1218,1219,1222,1223,1224,1225,1226,1227,1228,1229,1230][i - 813]! := by
  have hsplit : i = 813 + (i - 813) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor12]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 856 ≤ i) (hii : i ≤ 896) :
    Artifact.submissionArtifact.instructionPC i =
      [1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1246,1247,1249,1250,1251,1254,1255,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277][i - 856]! := by
  have hsplit : i = 856 + (i - 856) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor13]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 897 ≤ i) (hii : i ≤ 932) :
    Artifact.submissionArtifact.instructionPC i =
      [1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1293,1294,1296,1297,1298,1299,1300,1301,1303,1304,1305,1308,1309,1310,1313,1314,1315,1316,1317,1318,1319,1320][i - 897]! := by
  have hsplit : i = 897 + (i - 897) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor14]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 933 ≤ i) (hii : i ≤ 973) :
    Artifact.submissionArtifact.instructionPC i =
      [1323,1324,1325,1326,1329,1330,1331,1334,1335,1336,1339,1340,1342,1343,1344,1345,1346,1347,1350,1351,1352,1353,1354,1357,1358,1359,1362,1363,1364,1365,1366,1368,1369,1370,1371,1372,1373,1375,1376,1377,1378][i - 933]! := by
  have hsplit : i = 933 + (i - 933) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 974 ≤ i) (hii : i ≤ 1012) :
    Artifact.submissionArtifact.instructionPC i =
      [1379,1380,1381,1382,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1411,1413,1415,1416,1417,1418,1419,1420,1421,1422][i - 974]! := by
  have hsplit : i = 974 + (i - 974) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor16]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1013 ≤ i) (hii : i ≤ 1036) :
    Artifact.submissionArtifact.instructionPC i =
      [1423,1426,1427,1428,1431,1432,1433,1434,1435,1438,1439,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454][i - 1013]! := by
  have hsplit : i = 1013 + (i - 1013) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor17]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1037 ≤ i) (hii : i ≤ 1079) :
    Artifact.submissionArtifact.instructionPC i =
      [1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1468,1470,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1485,1486,1487,1490,1491,1492,1493,1494,1495,1498,1499,1500,1503,1504,1505,1508,1509,1512][i - 1037]! := by
  have hsplit : i = 1037 + (i - 1037) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor18]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1080 ≤ i) (hii : i ≤ 1082) :
    Artifact.submissionArtifact.instructionPC i =
      [1513,1514,1515][i - 1080]! := by
  have hsplit : i = 1080 + (i - 1080) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor19]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1083 ≤ i) (hii : i ≤ 1099) :
    Artifact.submissionArtifact.instructionPC i =
      [1516,1517,1520,1521,1522,1523,1526,1527,1528,1529,1530,1531,1532,1535,1536,1537,1538][i - 1083]! := by
  have hsplit : i = 1083 + (i - 1083) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor20]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1100 ≤ i) (hii : i ≤ 1112) :
    Artifact.submissionArtifact.instructionPC i =
      [1539,1540,1541,1542,1544,1545,1546,1549,1550,1552,1555,1556,1559][i - 1100]! := by
  have hsplit : i = 1100 + (i - 1100) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor21]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1113 ≤ i) (hii : i ≤ 1147) :
    Artifact.submissionArtifact.instructionPC i =
      [1560,1561,1562,1565,1566,1567,1568,1569,1570,1571,1572,1575,1576,1578,1581,1582,1583,1584,1585,1587,1588,1589,1590,1592,1593,1594,1595,1597,1598,1599,1601,1602,1604,1605,1608][i - 1113]! := by
  have hsplit : i = 1113 + (i - 1113) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor22]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1148 ≤ i) (hii : i ≤ 1159) :
    Artifact.submissionArtifact.instructionPC i =
      [1609,1610,1611,1614,1615,1618,1619,1622,1625,1626,1629,1632][i - 1148]! := by
  have hsplit : i = 1148 + (i - 1148) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor23]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 1753 ≤ i) (hii : i ≤ 1798) :
    Artifact.submissionArtifact.instructionPC i =
      [2305,2306,2307,2308,2309,2310,2311,2313,2314,2315,2316,2319,2320,2321,2323,2326,2327,2330,2333,2336,2339,2342,2343,2344,2345,2347,2348,2350,2351,2352,2353,2355,2356,2357,2359,2360,2362,2363,2364,2365,2366,2368,2369,2370,2372,2375][i - 1753]! := by
  have hsplit : i = 1753 + (i - 1753) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor24]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 553 = true :=
  Artifact.isValidJumpDest_index 389 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 771 = true :=
  Artifact.isValidJumpDest_index 554 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 793 = true :=
  Artifact.isValidJumpDest_index 564 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 808 = true :=
  Artifact.isValidJumpDest_index 571 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 826 = true :=
  Artifact.isValidJumpDest_index 583 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 841 = true :=
  Artifact.isValidJumpDest_index 594 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 853 = true :=
  Artifact.isValidJumpDest_index 602 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 877 = true :=
  Artifact.isValidJumpDest_index 614 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 912 = true :=
  Artifact.isValidJumpDest_index 635 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 920 = true :=
  Artifact.isValidJumpDest_index 640 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 939 = true :=
  Artifact.isValidJumpDest_index 649 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2443 = true :=
  Artifact.isValidJumpDest_index 1847 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 939 = true :=
  Artifact.isValidJumpDest_index 649 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 951 = true :=
  Artifact.isValidJumpDest_index 657 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 966 = true :=
  Artifact.isValidJumpDest_index 664 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 991 = true :=
  Artifact.isValidJumpDest_index 677 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 992 = true :=
  Artifact.isValidJumpDest_index 678 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1010 = true :=
  Artifact.isValidJumpDest_index 690 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1038 = true :=
  Artifact.isValidJumpDest_index 705 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1048 = true :=
  Artifact.isValidJumpDest_index 713 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1054 = true :=
  Artifact.isValidJumpDest_index 717 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1058 = true :=
  Artifact.isValidJumpDest_index 720 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1062 = true :=
  Artifact.isValidJumpDest_index 722 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1073 = true :=
  Artifact.isValidJumpDest_index 729 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1086 = true :=
  Artifact.isValidJumpDest_index 739 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1121 = true :=
  Artifact.isValidJumpDest_index 766 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1135 = true :=
  Artifact.isValidJumpDest_index 776 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1259 = true :=
  Artifact.isValidJumpDest_index 878 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1358 = true :=
  Artifact.isValidJumpDest_index 957 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1389 = true :=
  Artifact.isValidJumpDest_index 982 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1443 = true :=
  Artifact.isValidJumpDest_index 1025 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1516 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1527 = true :=
  Artifact.isValidJumpDest_index 1090 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1539 = true :=
  Artifact.isValidJumpDest_index 1100 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1560 = true :=
  Artifact.isValidJumpDest_index 1113 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1582 = true :=
  Artifact.isValidJumpDest_index 1128 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1609 = true :=
  Artifact.isValidJumpDest_index 1148 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2270 = true :=
  Artifact.isValidJumpDest_index 1730 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2305 = true :=
  Artifact.isValidJumpDest_index 1753 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2343 = true :=
  Artifact.isValidJumpDest_index 1775 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4132 = true :=
  Artifact.isValidJumpDest_index 3139 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4299 = true :=
  Artifact.isValidJumpDest_index 3256 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4555 = true :=
  Artifact.isValidJumpDest_index 3440 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4544 = true :=
  Artifact.isValidJumpDest_index 3433 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
