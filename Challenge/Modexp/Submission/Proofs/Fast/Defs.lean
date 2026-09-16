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
    Artifact.submissionArtifact.instructionPC 496 = 698 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 531 = 741 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 563 = 781 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 593 = 837 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 613 = 865 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 652 = 933 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 677 = 980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 719 = 1053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 747 = 1095 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl





private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 749 = 1097 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 765 = 1118 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 804 = 1162 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 828 = 1194 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 871 = 1252 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 874 = 1255 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 891 = 1278 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 904 = 1299 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 939 = 1348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 1542 = 2044 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 423 ≤ i) (hii : i ≤ 450) :
    Artifact.submissionArtifact.instructionPC i =
      [599,600,602,603,605,606,607,609,610,613,614,616,617,618,619,621,622,623,625,626,627,629,630,632,633,634,635,636][i - 423]! := by
  have hsplit : i = 423 + (i - 423) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 451 ≤ i) (hii : i ≤ 495) :
    Artifact.submissionArtifact.instructionPC i =
      [637,638,640,641,642,643,644,645,646,649,650,652,653,654,655,656,657,658,659,660,661,662,664,665,666,667,668,670,671,672,675,676,677,680,681,682,684,685,688,689,691,692,693,694,697][i - 451]! := by
  have hsplit : i = 451 + (i - 451) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 496 ≤ i) (hii : i ≤ 530) :
    Artifact.submissionArtifact.instructionPC i =
      [698,699,702,703,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,724,725,727,728,729,730,731,733,734,735,736,737,738,740][i - 496]! := by
  have hsplit : i = 496 + (i - 496) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 531 ≤ i) (hii : i ≤ 562) :
    Artifact.submissionArtifact.instructionPC i =
      [741,742,743,744,745,747,748,749,750,751,752,754,755,756,757,758,759,761,762,763,764,765,766,768,769,770,771,772,775,776,777,778][i - 531]! := by
  have hsplit : i = 531 + (i - 531) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor3]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 563 ≤ i) (hii : i ≤ 592) :
    Artifact.submissionArtifact.instructionPC i =
      [781,782,783,786,787,790,793,794,797,800,803,804,805,808,811,812,815,818,819,820,821,822,823,825,826,828,829,832,833,836][i - 563]! := by
  have hsplit : i = 563 + (i - 563) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor4]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 593 ≤ i) (hii : i ≤ 612) :
    Artifact.submissionArtifact.instructionPC i =
      [837,838,839,840,841,844,845,846,847,848,851,852,853,854,855,856,859,860,863,864][i - 593]! := by
  have hsplit : i = 593 + (i - 593) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor5]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 613 ≤ i) (hii : i ≤ 651) :
    Artifact.submissionArtifact.instructionPC i =
      [865,866,867,868,871,872,875,878,881,884,887,888,889,890,891,892,894,895,896,897,899,900,901,902,905,906,907,910,913,916,919,922,923,924,926,927,930,931,932][i - 613]! := by
  have hsplit : i = 613 + (i - 613) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor6]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 652 ≤ i) (hii : i ≤ 676) :
    Artifact.submissionArtifact.instructionPC i =
      [933,934,937,940,943,946,949,950,951,952,953,954,957,958,961,962,963,966,969,970,973,976,977,978,979][i - 652]! := by
  have hsplit : i = 652 + (i - 652) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor7]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 677 ≤ i) (hii : i ≤ 718) :
    Artifact.submissionArtifact.instructionPC i =
      [980,981,982,985,986,989,992,995,998,1001,1002,1003,1004,1006,1007,1008,1011,1012,1013,1014,1016,1017,1020,1021,1022,1023,1025,1026,1029,1030,1031,1034,1037,1040,1043,1046,1047,1048,1049,1050,1051,1052][i - 677]! := by
  have hsplit : i = 677 + (i - 677) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 719 ≤ i) (hii : i ≤ 746) :
    Artifact.submissionArtifact.instructionPC i =
      [1053,1056,1057,1058,1059,1060,1061,1064,1065,1066,1068,1069,1070,1073,1074,1077,1078,1079,1080,1083,1084,1085,1087,1088,1089,1090,1093,1094][i - 719]! := by
  have hsplit : i = 719 + (i - 719) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 747 ≤ i) (hii : i ≤ 748) :
    Artifact.submissionArtifact.instructionPC i =
      [1095,1096][i - 747]! := by
  have hsplit : i = 747 + (i - 747) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl





@[simp] theorem fastPC15 (i : Nat) (hi : 749 ≤ i) (hii : i ≤ 764) :
    Artifact.submissionArtifact.instructionPC i =
      [1097,1098,1101,1102,1105,1106,1107,1108,1109,1110,1111,1112,1114,1115,1116,1117][i - 749]! := by
  have hsplit : i = 749 + (i - 749) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 765 ≤ i) (hii : i ≤ 803) :
    Artifact.submissionArtifact.instructionPC i =
      [1118,1119,1120,1121,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1150,1152,1154,1155,1156,1157,1158,1159,1160,1161][i - 765]! := by
  have hsplit : i = 765 + (i - 765) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor16]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 804 ≤ i) (hii : i ≤ 827) :
    Artifact.submissionArtifact.instructionPC i =
      [1162,1165,1166,1167,1170,1171,1172,1173,1174,1177,1178,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193][i - 804]! := by
  have hsplit : i = 804 + (i - 804) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor17]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 828 ≤ i) (hii : i ≤ 870) :
    Artifact.submissionArtifact.instructionPC i =
      [1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1207,1208,1209,1210,1212,1213,1214,1215,1216,1218,1219,1220,1221,1224,1225,1226,1229,1230,1231,1232,1233,1234,1237,1238,1239,1242,1243,1244,1247,1248,1251][i - 828]! := by
  have hsplit : i = 828 + (i - 828) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor18]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 871 ≤ i) (hii : i ≤ 873) :
    Artifact.submissionArtifact.instructionPC i =
      [1252,1253,1254][i - 871]! := by
  have hsplit : i = 871 + (i - 871) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor19]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 874 ≤ i) (hii : i ≤ 890) :
    Artifact.submissionArtifact.instructionPC i =
      [1255,1256,1259,1260,1261,1262,1265,1266,1267,1268,1269,1270,1271,1274,1275,1276,1277][i - 874]! := by
  have hsplit : i = 874 + (i - 874) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor20]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 891 ≤ i) (hii : i ≤ 903) :
    Artifact.submissionArtifact.instructionPC i =
      [1278,1279,1280,1281,1283,1284,1285,1288,1289,1291,1294,1295,1298][i - 891]! := by
  have hsplit : i = 891 + (i - 891) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor21]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 904 ≤ i) (hii : i ≤ 938) :
    Artifact.submissionArtifact.instructionPC i =
      [1299,1300,1301,1304,1305,1306,1307,1308,1309,1310,1311,1314,1315,1317,1320,1321,1322,1323,1324,1326,1327,1328,1329,1331,1332,1333,1334,1336,1337,1338,1340,1341,1343,1344,1347][i - 904]! := by
  have hsplit : i = 904 + (i - 904) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor22]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 939 ≤ i) (hii : i ≤ 950) :
    Artifact.submissionArtifact.instructionPC i =
      [1348,1349,1350,1353,1354,1357,1358,1361,1364,1365,1368,1371][i - 939]! := by
  have hsplit : i = 939 + (i - 939) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor23]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 1542 ≤ i) (hii : i ≤ 1587) :
    Artifact.submissionArtifact.instructionPC i =
      [2044,2045,2046,2047,2048,2049,2050,2052,2053,2054,2055,2058,2059,2060,2062,2065,2066,2069,2072,2075,2078,2081,2082,2083,2084,2086,2087,2089,2090,2091,2092,2094,2095,2096,2098,2099,2101,2102,2103,2104,2105,2107,2108,2109,2111,2114][i - 1542]! := by
  have hsplit : i = 1542 + (i - 1542) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor24]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 553 = true :=
  Artifact.isValidJumpDest_index 389 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 782 = true :=
  Artifact.isValidJumpDest_index 564 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 804 = true :=
  Artifact.isValidJumpDest_index 574 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 819 = true :=
  Artifact.isValidJumpDest_index 581 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 837 = true :=
  Artifact.isValidJumpDest_index 593 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 852 = true :=
  Artifact.isValidJumpDest_index 604 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 864 = true :=
  Artifact.isValidJumpDest_index 612 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 888 = true :=
  Artifact.isValidJumpDest_index 624 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 923 = true :=
  Artifact.isValidJumpDest_index 645 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 931 = true :=
  Artifact.isValidJumpDest_index 650 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 950 = true :=
  Artifact.isValidJumpDest_index 659 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2182 = true :=
  Artifact.isValidJumpDest_index 1635 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 950 = true :=
  Artifact.isValidJumpDest_index 659 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 962 = true :=
  Artifact.isValidJumpDest_index 667 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 977 = true :=
  Artifact.isValidJumpDest_index 674 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1002 = true :=
  Artifact.isValidJumpDest_index 687 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1003 = true :=
  Artifact.isValidJumpDest_index 688 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1021 = true :=
  Artifact.isValidJumpDest_index 700 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1049 = true :=
  Artifact.isValidJumpDest_index 715 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1059 = true :=
  Artifact.isValidJumpDest_index 723 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1065 = true :=
  Artifact.isValidJumpDest_index 727 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1069 = true :=
  Artifact.isValidJumpDest_index 730 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1073 = true :=
  Artifact.isValidJumpDest_index 732 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1084 = true :=
  Artifact.isValidJumpDest_index 739 (by rfl)





theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1097 = true :=
  Artifact.isValidJumpDest_index 749 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1128 = true :=
  Artifact.isValidJumpDest_index 773 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1182 = true :=
  Artifact.isValidJumpDest_index 816 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1255 = true :=
  Artifact.isValidJumpDest_index 874 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1266 = true :=
  Artifact.isValidJumpDest_index 881 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1278 = true :=
  Artifact.isValidJumpDest_index 891 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1299 = true :=
  Artifact.isValidJumpDest_index 904 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1321 = true :=
  Artifact.isValidJumpDest_index 919 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1348 = true :=
  Artifact.isValidJumpDest_index 939 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2009 = true :=
  Artifact.isValidJumpDest_index 1519 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2044 = true :=
  Artifact.isValidJumpDest_index 1542 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2082 = true :=
  Artifact.isValidJumpDest_index 1564 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3963 = true :=
  Artifact.isValidJumpDest_index 2990 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4130 = true :=
  Artifact.isValidJumpDest_index 3098 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4353 = true :=
  Artifact.isValidJumpDest_index 3255 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4342 = true :=
  Artifact.isValidJumpDest_index 3248 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
