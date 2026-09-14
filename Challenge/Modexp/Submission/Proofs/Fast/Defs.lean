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
    Artifact.submissionArtifact.instructionPC 494 = 708 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 522 = 746 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 557 = 796 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 592 = 839 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 624 = 879 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 654 = 935 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 674 = 963 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 713 = 1031 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 738 = 1078 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 780 = 1151 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 814 = 1200 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 853 = 1251 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 890 = 1288 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 933 = 1347 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 974 = 1394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1010 = 1439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1051 = 1495 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1092 = 1541 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1116 = 1573 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1159 = 1631 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1162 = 1634 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1179 = 1657 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1192 = 1678 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1227 = 1727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 1828 = 2429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 494 ≤ i) (hii : i ≤ 521) :
    Artifact.submissionArtifact.instructionPC i =
      [708,709,711,712,714,715,716,718,719,722,723,725,726,727,728,730,731,732,734,735,736,738,739,741,742,743,744,745][i - 494]! := by
  have hsplit : i = 494 + (i - 494) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 522 ≤ i) (hii : i ≤ 556) :
    Artifact.submissionArtifact.instructionPC i =
      [746,747,748,749,750,752,753,754,755,758,759,761,762,763,764,765,766,768,769,770,773,774,775,778,779,780,782,783,786,787,789,790,791,792,795][i - 522]! := by
  have hsplit : i = 522 + (i - 522) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 557 ≤ i) (hii : i ≤ 591) :
    Artifact.submissionArtifact.instructionPC i =
      [796,797,800,801,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,822,823,825,826,827,828,829,831,832,833,834,835,836,838][i - 557]! := by
  have hsplit : i = 557 + (i - 557) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 592 ≤ i) (hii : i ≤ 623) :
    Artifact.submissionArtifact.instructionPC i =
      [839,840,841,842,843,845,846,847,848,849,850,852,853,854,855,856,857,859,860,861,862,863,864,866,867,868,869,870,873,874,875,876][i - 592]! := by
  have hsplit : i = 592 + (i - 592) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor3]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 624 ≤ i) (hii : i ≤ 653) :
    Artifact.submissionArtifact.instructionPC i =
      [879,880,881,884,885,888,891,892,895,898,901,902,903,906,909,910,913,916,917,918,919,920,921,923,924,926,927,930,931,934][i - 624]! := by
  have hsplit : i = 624 + (i - 624) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor4]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 654 ≤ i) (hii : i ≤ 673) :
    Artifact.submissionArtifact.instructionPC i =
      [935,936,937,938,939,942,943,944,945,946,949,950,951,952,953,954,957,958,961,962][i - 654]! := by
  have hsplit : i = 654 + (i - 654) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor5]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 674 ≤ i) (hii : i ≤ 712) :
    Artifact.submissionArtifact.instructionPC i =
      [963,964,965,966,969,970,973,976,979,982,985,986,987,988,989,990,992,993,994,995,997,998,999,1000,1003,1004,1005,1008,1011,1014,1017,1020,1021,1022,1024,1025,1028,1029,1030][i - 674]! := by
  have hsplit : i = 674 + (i - 674) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor6]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 713 ≤ i) (hii : i ≤ 737) :
    Artifact.submissionArtifact.instructionPC i =
      [1031,1032,1035,1038,1041,1044,1047,1048,1049,1050,1051,1052,1055,1056,1059,1060,1061,1064,1067,1068,1071,1074,1075,1076,1077][i - 713]! := by
  have hsplit : i = 713 + (i - 713) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor7]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 738 ≤ i) (hii : i ≤ 779) :
    Artifact.submissionArtifact.instructionPC i =
      [1078,1079,1080,1083,1084,1087,1090,1093,1096,1099,1100,1101,1102,1104,1105,1106,1109,1110,1111,1112,1114,1115,1118,1119,1120,1121,1123,1124,1127,1128,1129,1132,1135,1138,1141,1144,1145,1146,1147,1148,1149,1150][i - 738]! := by
  have hsplit : i = 738 + (i - 738) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 780 ≤ i) (hii : i ≤ 813) :
    Artifact.submissionArtifact.instructionPC i =
      [1151,1154,1155,1156,1157,1158,1159,1162,1163,1164,1165,1166,1167,1168,1169,1170,1173,1174,1175,1178,1179,1182,1183,1184,1185,1188,1189,1190,1192,1193,1194,1195,1198,1199][i - 780]! := by
  have hsplit : i = 780 + (i - 780) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 814 ≤ i) (hii : i ≤ 852) :
    Artifact.submissionArtifact.instructionPC i =
      [1200,1201,1202,1203,1206,1207,1208,1210,1211,1212,1215,1216,1217,1218,1219,1221,1222,1223,1225,1226,1227,1228,1229,1230,1231,1233,1234,1235,1236,1237,1238,1239,1240,1241,1244,1245,1246,1249,1250][i - 814]! := by
  have hsplit : i = 814 + (i - 814) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 853 ≤ i) (hii : i ≤ 889) :
    Artifact.submissionArtifact.instructionPC i =
      [1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287][i - 853]! := by
  have hsplit : i = 853 + (i - 853) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor11]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 890 ≤ i) (hii : i ≤ 932) :
    Artifact.submissionArtifact.instructionPC i =
      [1288,1289,1291,1292,1293,1294,1296,1297,1298,1299,1300,1301,1302,1305,1306,1307,1308,1309,1312,1313,1314,1315,1318,1319,1320,1323,1324,1327,1328,1329,1332,1333,1334,1335,1338,1339,1340,1341,1342,1343,1344,1345,1346][i - 890]! := by
  have hsplit : i = 890 + (i - 890) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor12]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 933 ≤ i) (hii : i ≤ 973) :
    Artifact.submissionArtifact.instructionPC i =
      [1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1362,1363,1365,1366,1367,1370,1371,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393][i - 933]! := by
  have hsplit : i = 933 + (i - 933) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor13]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 974 ≤ i) (hii : i ≤ 1009) :
    Artifact.submissionArtifact.instructionPC i =
      [1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1409,1410,1412,1413,1414,1415,1416,1417,1419,1420,1421,1424,1425,1426,1429,1430,1431,1432,1433,1434,1435,1436][i - 974]! := by
  have hsplit : i = 974 + (i - 974) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor14]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1010 ≤ i) (hii : i ≤ 1050) :
    Artifact.submissionArtifact.instructionPC i =
      [1439,1440,1441,1442,1445,1446,1447,1450,1451,1452,1455,1456,1458,1459,1460,1461,1462,1463,1466,1467,1468,1469,1470,1473,1474,1475,1478,1479,1480,1481,1482,1484,1485,1486,1487,1488,1489,1491,1492,1493,1494][i - 1010]! := by
  have hsplit : i = 1010 + (i - 1010) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1051 ≤ i) (hii : i ≤ 1091) :
    Artifact.submissionArtifact.instructionPC i =
      [1495,1496,1497,1498,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1527,1529,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540][i - 1051]! := by
  have hsplit : i = 1051 + (i - 1051) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor16]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1092 ≤ i) (hii : i ≤ 1115) :
    Artifact.submissionArtifact.instructionPC i =
      [1541,1544,1545,1546,1549,1550,1551,1552,1553,1556,1557,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572][i - 1092]! := by
  have hsplit : i = 1092 + (i - 1092) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor17]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1116 ≤ i) (hii : i ≤ 1158) :
    Artifact.submissionArtifact.instructionPC i =
      [1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1586,1587,1588,1589,1591,1592,1593,1594,1595,1597,1598,1599,1600,1603,1604,1605,1608,1609,1610,1611,1612,1613,1616,1617,1618,1621,1622,1623,1626,1627,1630][i - 1116]! := by
  have hsplit : i = 1116 + (i - 1116) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor18]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1159 ≤ i) (hii : i ≤ 1161) :
    Artifact.submissionArtifact.instructionPC i =
      [1631,1632,1633][i - 1159]! := by
  have hsplit : i = 1159 + (i - 1159) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor19]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1162 ≤ i) (hii : i ≤ 1178) :
    Artifact.submissionArtifact.instructionPC i =
      [1634,1635,1638,1639,1640,1641,1644,1645,1646,1647,1648,1649,1650,1653,1654,1655,1656][i - 1162]! := by
  have hsplit : i = 1162 + (i - 1162) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor20]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1179 ≤ i) (hii : i ≤ 1191) :
    Artifact.submissionArtifact.instructionPC i =
      [1657,1658,1659,1660,1662,1663,1664,1667,1668,1670,1673,1674,1677][i - 1179]! := by
  have hsplit : i = 1179 + (i - 1179) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor21]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1192 ≤ i) (hii : i ≤ 1226) :
    Artifact.submissionArtifact.instructionPC i =
      [1678,1679,1680,1683,1684,1685,1686,1687,1688,1689,1690,1693,1694,1696,1699,1700,1701,1702,1703,1705,1706,1707,1708,1710,1711,1712,1713,1715,1716,1717,1719,1720,1722,1723,1726][i - 1192]! := by
  have hsplit : i = 1192 + (i - 1192) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor22]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1227 ≤ i) (hii : i ≤ 1238) :
    Artifact.submissionArtifact.instructionPC i =
      [1727,1728,1729,1732,1733,1736,1737,1740,1743,1744,1747,1750][i - 1227]! := by
  have hsplit : i = 1227 + (i - 1227) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor23]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 1828 ≤ i) (hii : i ≤ 1873) :
    Artifact.submissionArtifact.instructionPC i =
      [2429,2430,2431,2432,2433,2434,2435,2437,2438,2439,2440,2443,2444,2445,2447,2450,2451,2454,2457,2460,2463,2466,2467,2468,2469,2471,2472,2474,2475,2476,2477,2479,2480,2481,2483,2484,2486,2487,2488,2489,2490,2492,2493,2494,2496,2499][i - 1828]! := by
  have hsplit : i = 1828 + (i - 1828) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor24]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 647 = true :=
  Artifact.isValidJumpDest_index 450 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 880 = true :=
  Artifact.isValidJumpDest_index 625 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 902 = true :=
  Artifact.isValidJumpDest_index 635 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 917 = true :=
  Artifact.isValidJumpDest_index 642 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 935 = true :=
  Artifact.isValidJumpDest_index 654 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 950 = true :=
  Artifact.isValidJumpDest_index 665 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 962 = true :=
  Artifact.isValidJumpDest_index 673 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 986 = true :=
  Artifact.isValidJumpDest_index 685 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1021 = true :=
  Artifact.isValidJumpDest_index 706 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1029 = true :=
  Artifact.isValidJumpDest_index 711 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1048 = true :=
  Artifact.isValidJumpDest_index 720 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2631 = true :=
  Artifact.isValidJumpDest_index 1978 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1048 = true :=
  Artifact.isValidJumpDest_index 720 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1060 = true :=
  Artifact.isValidJumpDest_index 728 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1075 = true :=
  Artifact.isValidJumpDest_index 735 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1100 = true :=
  Artifact.isValidJumpDest_index 748 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1101 = true :=
  Artifact.isValidJumpDest_index 749 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1119 = true :=
  Artifact.isValidJumpDest_index 761 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1147 = true :=
  Artifact.isValidJumpDest_index 776 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1157 = true :=
  Artifact.isValidJumpDest_index 784 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1163 = true :=
  Artifact.isValidJumpDest_index 788 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1174 = true :=
  Artifact.isValidJumpDest_index 797 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1178 = true :=
  Artifact.isValidJumpDest_index 799 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  Artifact.isValidJumpDest_index 806 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1202 = true :=
  Artifact.isValidJumpDest_index 816 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1237 = true :=
  Artifact.isValidJumpDest_index 843 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1251 = true :=
  Artifact.isValidJumpDest_index 853 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1375 = true :=
  Artifact.isValidJumpDest_index 955 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1474 = true :=
  Artifact.isValidJumpDest_index 1034 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1505 = true :=
  Artifact.isValidJumpDest_index 1059 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1561 = true :=
  Artifact.isValidJumpDest_index 1104 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1634 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1645 = true :=
  Artifact.isValidJumpDest_index 1169 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1657 = true :=
  Artifact.isValidJumpDest_index 1179 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1678 = true :=
  Artifact.isValidJumpDest_index 1192 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1700 = true :=
  Artifact.isValidJumpDest_index 1207 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1727 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2394 = true :=
  Artifact.isValidJumpDest_index 1805 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2429 = true :=
  Artifact.isValidJumpDest_index 1828 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2467 = true :=
  Artifact.isValidJumpDest_index 1850 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4320 = true :=
  Artifact.isValidJumpDest_index 3275 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4536 = true :=
  Artifact.isValidJumpDest_index 3433 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4772 = true :=
  Artifact.isValidJumpDest_index 3605 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4398 = true :=
  Artifact.isValidJumpDest_index 3322 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
