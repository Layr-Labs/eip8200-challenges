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
    Artifact.submissionArtifact.instructionPC 494 = 717 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 523 = 756 := by
  calc
    Artifact.submissionArtifact.instructionPC 523 =
        Artifact.submissionArtifact.instructionPC 494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 494).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 494 29
    _ = 756 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 560 = 808 := by
  calc
    Artifact.submissionArtifact.instructionPC 560 =
        Artifact.submissionArtifact.instructionPC 523 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 523).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 523 37
    _ = 808 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 595 = 851 := by
  calc
    Artifact.submissionArtifact.instructionPC 595 =
        Artifact.submissionArtifact.instructionPC 560 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 560).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 560 35
    _ = 851 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 627 = 895 := by
  calc
    Artifact.submissionArtifact.instructionPC 627 =
        Artifact.submissionArtifact.instructionPC 595 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 595).take 32)).length :=
      instructionPC_add Artifact.submissionArtifact 595 32
    _ = 895 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 657 = 952 := by
  calc
    Artifact.submissionArtifact.instructionPC 657 =
        Artifact.submissionArtifact.instructionPC 627 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 627).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 627 30
    _ = 952 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 677 = 980 := by
  calc
    Artifact.submissionArtifact.instructionPC 677 =
        Artifact.submissionArtifact.instructionPC 657 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 657).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 657 20
    _ = 980 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 716 = 1048 := by
  calc
    Artifact.submissionArtifact.instructionPC 716 =
        Artifact.submissionArtifact.instructionPC 677 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 677).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 677 39
    _ = 1048 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 741 = 1095 := by
  calc
    Artifact.submissionArtifact.instructionPC 741 =
        Artifact.submissionArtifact.instructionPC 716 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 716).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 716 25
    _ = 1095 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 783 = 1168 := by
  calc
    Artifact.submissionArtifact.instructionPC 783 =
        Artifact.submissionArtifact.instructionPC 741 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 741).take 42)).length :=
      instructionPC_add Artifact.submissionArtifact 741 42
    _ = 1168 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 817 = 1217 := by
  calc
    Artifact.submissionArtifact.instructionPC 817 =
        Artifact.submissionArtifact.instructionPC 783 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 783).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 783 34
    _ = 1217 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 856 = 1268 := by
  calc
    Artifact.submissionArtifact.instructionPC 856 =
        Artifact.submissionArtifact.instructionPC 817 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 817).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 817 39
    _ = 1268 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 893 = 1305 := by
  calc
    Artifact.submissionArtifact.instructionPC 893 =
        Artifact.submissionArtifact.instructionPC 856 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 856).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 856 37
    _ = 1305 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 936 = 1364 := by
  calc
    Artifact.submissionArtifact.instructionPC 936 =
        Artifact.submissionArtifact.instructionPC 893 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 893).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 893 43
    _ = 1364 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 977 = 1411 := by
  calc
    Artifact.submissionArtifact.instructionPC 977 =
        Artifact.submissionArtifact.instructionPC 936 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 936).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 936 41
    _ = 1411 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1013 = 1456 := by
  calc
    Artifact.submissionArtifact.instructionPC 1013 =
        Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 977 36
    _ = 1456 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1054 = 1512 := by
  calc
    Artifact.submissionArtifact.instructionPC 1054 =
        Artifact.submissionArtifact.instructionPC 1013 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1013).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1013 41
    _ = 1512 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1095 = 1558 := by
  calc
    Artifact.submissionArtifact.instructionPC 1095 =
        Artifact.submissionArtifact.instructionPC 1054 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1054).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1054 41
    _ = 1558 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1119 = 1590 := by
  calc
    Artifact.submissionArtifact.instructionPC 1119 =
        Artifact.submissionArtifact.instructionPC 1095 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1095).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1095 24
    _ = 1590 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1162 = 1648 := by
  calc
    Artifact.submissionArtifact.instructionPC 1162 =
        Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1119 43
    _ = 1648 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1165 = 1651 := by
  calc
    Artifact.submissionArtifact.instructionPC 1165 =
        Artifact.submissionArtifact.instructionPC 1162 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1162).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1162 3
    _ = 1651 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1182 = 1674 := by
  calc
    Artifact.submissionArtifact.instructionPC 1182 =
        Artifact.submissionArtifact.instructionPC 1165 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1165).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1165 17
    _ = 1674 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1195 = 1695 := by
  calc
    Artifact.submissionArtifact.instructionPC 1195 =
        Artifact.submissionArtifact.instructionPC 1182 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1182).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1182 13
    _ = 1695 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1230 = 1744 := by
  calc
    Artifact.submissionArtifact.instructionPC 1230 =
        Artifact.submissionArtifact.instructionPC 1195 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1195).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1195 35
    _ = 1744 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 1840 = 2473 := by
  calc
    Artifact.submissionArtifact.instructionPC 1840 =
        Artifact.submissionArtifact.instructionPC 1230 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1230).take 610)).length :=
      instructionPC_add Artifact.submissionArtifact 1230 610
    _ = 2473 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 494 ≤ i) (hii : i ≤ 522) :
    Artifact.submissionArtifact.instructionPC i =
      [717,718,720,721,722,724,725,726,728,729,732,733,735,736,737,738,739,741,742,744,745,746,748,749,750,751,752,754,755][i - 494]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (494 + (i - 494)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 494).take (i - 494))).length :=
      instructionPC_add Artifact.submissionArtifact 494 (i - 494)
    _ = _ := by
      rw [fastPCAnchor0]
      interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 523 ≤ i) (hii : i ≤ 559) :
    Artifact.submissionArtifact.instructionPC i =
      [756,757,758,760,761,762,763,764,765,766,769,770,772,773,774,775,776,777,779,780,781,784,785,786,789,790,791,792,794,795,798,799,801,802,803,804,807][i - 523]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (523 + (i - 523)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 523 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 523).take (i - 523))).length :=
      instructionPC_add Artifact.submissionArtifact 523 (i - 523)
    _ = _ := by
      rw [fastPCAnchor1]
      interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 560 ≤ i) (hii : i ≤ 594) :
    Artifact.submissionArtifact.instructionPC i =
      [808,809,812,813,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,834,835,837,838,839,840,841,843,844,845,846,847,848,850][i - 560]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (560 + (i - 560)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 560 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 560).take (i - 560))).length :=
      instructionPC_add Artifact.submissionArtifact 560 (i - 560)
    _ = _ := by
      rw [fastPCAnchor2]
      interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 595 ≤ i) (hii : i ≤ 626) :
    Artifact.submissionArtifact.instructionPC i =
      [851,852,853,854,855,857,858,859,860,861,862,864,865,866,867,868,869,871,872,873,874,875,876,878,879,880,881,882,889,890,891,892][i - 595]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (595 + (i - 595)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 595 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 595).take (i - 595))).length :=
      instructionPC_add Artifact.submissionArtifact 595 (i - 595)
    _ = _ := by
      rw [fastPCAnchor3]
      interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 627 ≤ i) (hii : i ≤ 656) :
    Artifact.submissionArtifact.instructionPC i =
      [895,896,897,900,901,904,907,908,911,914,917,918,919,922,925,926,929,932,933,934,935,936,937,939,940,943,944,947,948,951][i - 627]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (627 + (i - 627)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 627 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 627).take (i - 627))).length :=
      instructionPC_add Artifact.submissionArtifact 627 (i - 627)
    _ = _ := by
      rw [fastPCAnchor4]
      interval_cases i <;> rfl

@[simp] theorem fastPC5 (i : Nat) (hi : 657 ≤ i) (hii : i ≤ 676) :
    Artifact.submissionArtifact.instructionPC i =
      [952,953,954,955,956,959,960,961,962,963,966,967,968,969,970,971,974,975,978,979][i - 657]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (657 + (i - 657)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 657 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 657).take (i - 657))).length :=
      instructionPC_add Artifact.submissionArtifact 657 (i - 657)
    _ = _ := by
      rw [fastPCAnchor5]
      interval_cases i <;> rfl

@[simp] theorem fastPC6 (i : Nat) (hi : 677 ≤ i) (hii : i ≤ 715) :
    Artifact.submissionArtifact.instructionPC i =
      [980,981,982,983,986,987,990,993,996,999,1002,1003,1004,1005,1006,1007,1009,1010,1011,1012,1014,1015,1016,1017,1020,1021,1022,1025,1028,1031,1034,1037,1038,1039,1041,1042,1045,1046,1047][i - 677]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (677 + (i - 677)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 677 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 677).take (i - 677))).length :=
      instructionPC_add Artifact.submissionArtifact 677 (i - 677)
    _ = _ := by
      rw [fastPCAnchor6]
      interval_cases i <;> rfl

@[simp] theorem fastPC7 (i : Nat) (hi : 716 ≤ i) (hii : i ≤ 740) :
    Artifact.submissionArtifact.instructionPC i =
      [1048,1049,1052,1055,1058,1061,1064,1065,1066,1067,1068,1069,1072,1073,1076,1077,1078,1081,1084,1085,1088,1091,1092,1093,1094][i - 716]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (716 + (i - 716)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 716 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 716).take (i - 716))).length :=
      instructionPC_add Artifact.submissionArtifact 716 (i - 716)
    _ = _ := by
      rw [fastPCAnchor7]
      interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 741 ≤ i) (hii : i ≤ 782) :
    Artifact.submissionArtifact.instructionPC i =
      [1095,1096,1097,1100,1101,1104,1107,1110,1113,1116,1117,1118,1119,1121,1122,1123,1126,1127,1128,1129,1131,1132,1135,1136,1137,1138,1140,1141,1144,1145,1146,1149,1152,1155,1158,1161,1162,1163,1164,1165,1166,1167][i - 741]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (741 + (i - 741)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 741 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 741).take (i - 741))).length :=
      instructionPC_add Artifact.submissionArtifact 741 (i - 741)
    _ = _ := by
      rw [fastPCAnchor8]
      interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 783 ≤ i) (hii : i ≤ 816) :
    Artifact.submissionArtifact.instructionPC i =
 [1168,1171,1172,1173,1174,1175,1176,1179,1180,1181,1182,1183,1184,1185,1186,1187,1190,1191,1192,1195,1196,1199,1200,1201,1202,1205,1206,1207,1208,1209,1210,1211,1215,1216][i - 783]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (783 + (i - 783)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 783 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 783).take (i - 783))).length :=
      instructionPC_add Artifact.submissionArtifact 783 (i - 783)
    _ = _ := by
      rw [fastPCAnchor9]
      interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 817 ≤ i) (hii : i ≤ 855) :
    Artifact.submissionArtifact.instructionPC i =
      [1217,1218,1219,1220,1223,1224,1225,1227,1228,1229,1232,1233,1234,1235,1236,1238,1239,1240,1242,1243,1244,1245,1246,1247,1248,1250,1251,1252,1253,1254,1255,1256,1257,1258,1261,1262,1263,1266,1267][i - 817]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (817 + (i - 817)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 817 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 817).take (i - 817))).length :=
      instructionPC_add Artifact.submissionArtifact 817 (i - 817)
    _ = _ := by
      rw [fastPCAnchor10]
      interval_cases i <;> rfl

@[simp] theorem fastPC11 (i : Nat) (hi : 856 ≤ i) (hii : i ≤ 892) :
    Artifact.submissionArtifact.instructionPC i =
      [1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304][i - 856]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (856 + (i - 856)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 856 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 856).take (i - 856))).length :=
      instructionPC_add Artifact.submissionArtifact 856 (i - 856)
    _ = _ := by
      rw [fastPCAnchor11]
      interval_cases i <;> rfl

@[simp] theorem fastPC12 (i : Nat) (hi : 893 ≤ i) (hii : i ≤ 935) :
    Artifact.submissionArtifact.instructionPC i =
      [1305,1306,1308,1309,1310,1311,1313,1314,1315,1316,1317,1318,1319,1322,1323,1324,1325,1326,1329,1330,1331,1332,1335,1336,1337,1340,1341,1344,1345,1346,1349,1350,1351,1352,1355,1356,1357,1358,1359,1360,1361,1362,1363][i - 893]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (893 + (i - 893)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 893 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 893).take (i - 893))).length :=
      instructionPC_add Artifact.submissionArtifact 893 (i - 893)
    _ = _ := by
      rw [fastPCAnchor12]
      interval_cases i <;> rfl

@[simp] theorem fastPC13 (i : Nat) (hi : 936 ≤ i) (hii : i ≤ 976) :
    Artifact.submissionArtifact.instructionPC i =
      [1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1379,1380,1382,1383,1384,1387,1388,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410][i - 936]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (936 + (i - 936)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 936 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 936).take (i - 936))).length :=
      instructionPC_add Artifact.submissionArtifact 936 (i - 936)
    _ = _ := by
      rw [fastPCAnchor13]
      interval_cases i <;> rfl

@[simp] theorem fastPC14 (i : Nat) (hi : 977 ≤ i) (hii : i ≤ 1012) :
    Artifact.submissionArtifact.instructionPC i =
      [1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1426,1427,1429,1430,1431,1432,1433,1434,1436,1437,1438,1441,1442,1443,1446,1447,1448,1449,1450,1451,1452,1453][i - 977]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (977 + (i - 977)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take (i - 977))).length :=
      instructionPC_add Artifact.submissionArtifact 977 (i - 977)
    _ = _ := by
      rw [fastPCAnchor14]
      interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 1013 ≤ i) (hii : i ≤ 1053) :
    Artifact.submissionArtifact.instructionPC i =
      [1456,1457,1458,1459,1462,1463,1464,1467,1468,1469,1472,1473,1475,1476,1477,1478,1479,1480,1483,1484,1485,1486,1487,1490,1491,1492,1495,1496,1497,1498,1499,1501,1502,1503,1504,1505,1506,1508,1509,1510,1511][i - 1013]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1013 + (i - 1013)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1013 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1013).take (i - 1013))).length :=
      instructionPC_add Artifact.submissionArtifact 1013 (i - 1013)
    _ = _ := by
      rw [fastPCAnchor15]
      interval_cases i <;> rfl

@[simp] theorem fastPC16 (i : Nat) (hi : 1054 ≤ i) (hii : i ≤ 1094) :
    Artifact.submissionArtifact.instructionPC i =
      [1512,1513,1514,1515,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1544,1545,1546,1547,1549,1550,1551,1552,1553,1555,1556,1557][i - 1054]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1054 + (i - 1054)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1054 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1054).take (i - 1054))).length :=
      instructionPC_add Artifact.submissionArtifact 1054 (i - 1054)
    _ = _ := by
      rw [fastPCAnchor16]
      interval_cases i <;> rfl

@[simp] theorem fastPC17 (i : Nat) (hi : 1095 ≤ i) (hii : i ≤ 1118) :
    Artifact.submissionArtifact.instructionPC i =
      [1558,1561,1562,1563,1566,1567,1568,1569,1570,1573,1574,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589][i - 1095]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1095 + (i - 1095)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1095 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1095).take (i - 1095))).length :=
      instructionPC_add Artifact.submissionArtifact 1095 (i - 1095)
    _ = _ := by
      rw [fastPCAnchor17]
      interval_cases i <;> rfl

@[simp] theorem fastPC18 (i : Nat) (hi : 1119 ≤ i) (hii : i ≤ 1161) :
    Artifact.submissionArtifact.instructionPC i =
      [1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1603,1604,1605,1606,1608,1609,1610,1611,1612,1614,1615,1616,1617,1620,1621,1622,1625,1626,1627,1628,1629,1630,1633,1634,1635,1638,1639,1640,1643,1644,1647][i - 1119]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1119 + (i - 1119)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take (i - 1119))).length :=
      instructionPC_add Artifact.submissionArtifact 1119 (i - 1119)
    _ = _ := by
      rw [fastPCAnchor18]
      interval_cases i <;> rfl

@[simp] theorem fastPC19 (i : Nat) (hi : 1162 ≤ i) (hii : i ≤ 1164) :
    Artifact.submissionArtifact.instructionPC i =
      [1648,1649,1650][i - 1162]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1162 + (i - 1162)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1162 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1162).take (i - 1162))).length :=
      instructionPC_add Artifact.submissionArtifact 1162 (i - 1162)
    _ = _ := by
      rw [fastPCAnchor19]
      interval_cases i <;> rfl

@[simp] theorem fastPC20 (i : Nat) (hi : 1165 ≤ i) (hii : i ≤ 1181) :
    Artifact.submissionArtifact.instructionPC i =
      [1651,1652,1655,1656,1657,1658,1661,1662,1663,1664,1665,1666,1667,1670,1671,1672,1673][i - 1165]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1165 + (i - 1165)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1165 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1165).take (i - 1165))).length :=
      instructionPC_add Artifact.submissionArtifact 1165 (i - 1165)
    _ = _ := by
      rw [fastPCAnchor20]
      interval_cases i <;> rfl

@[simp] theorem fastPC21 (i : Nat) (hi : 1182 ≤ i) (hii : i ≤ 1194) :
    Artifact.submissionArtifact.instructionPC i =
      [1674,1675,1676,1677,1679,1680,1681,1684,1685,1687,1690,1691,1694][i - 1182]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1182 + (i - 1182)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1182 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1182).take (i - 1182))).length :=
      instructionPC_add Artifact.submissionArtifact 1182 (i - 1182)
    _ = _ := by
      rw [fastPCAnchor21]
      interval_cases i <;> rfl

@[simp] theorem fastPC22 (i : Nat) (hi : 1195 ≤ i) (hii : i ≤ 1229) :
    Artifact.submissionArtifact.instructionPC i =
      [1695,1696,1697,1700,1701,1702,1703,1704,1705,1706,1707,1710,1711,1713,1716,1717,1718,1719,1720,1722,1723,1724,1725,1727,1728,1729,1730,1732,1733,1734,1736,1737,1739,1740,1743][i - 1195]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1195 + (i - 1195)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1195 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1195).take (i - 1195))).length :=
      instructionPC_add Artifact.submissionArtifact 1195 (i - 1195)
    _ = _ := by
      rw [fastPCAnchor22]
      interval_cases i <;> rfl

@[simp] theorem fastPC23 (i : Nat) (hi : 1230 ≤ i) (hii : i ≤ 1241) :
    Artifact.submissionArtifact.instructionPC i =
      [1744,1745,1746,1749,1750,1753,1754,1757,1760,1761,1764,1767][i - 1230]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1230 + (i - 1230)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1230 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1230).take (i - 1230))).length :=
      instructionPC_add Artifact.submissionArtifact 1230 (i - 1230)
    _ = _ := by
      rw [fastPCAnchor23]
      interval_cases i <;> rfl

@[simp] theorem fullBasePC (i : Nat) (hi : 1840 ≤ i) (hii : i ≤ 1885) :
    Artifact.submissionArtifact.instructionPC i =
      [2473,2474,2475,2476,2477,2478,2479,2481,2482,2483,2484,2487,2488,2489,2491,2494,2495,2498,2501,2504,2507,2510,2511,2512,2513,2515,2516,2518,2519,2520,2521,2523,2524,2525,2527,2528,2530,2531,2532,2533,2534,2536,2537,2538,2540,2543][i - 1840]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (1840 + (i - 1840)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 1840 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1840).take (i - 1840))).length :=
      instructionPC_add Artifact.submissionArtifact 1840 (i - 1840)
    _ = _ := by
      rw [fastPCAnchor24]
      interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 655 = true :=
  Artifact.isValidJumpDest_index 450 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 896 = true :=
  Artifact.isValidJumpDest_index 628 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 918 = true :=
  Artifact.isValidJumpDest_index 638 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 933 = true :=
  Artifact.isValidJumpDest_index 645 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 952 = true :=
  Artifact.isValidJumpDest_index 657 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 967 = true :=
  Artifact.isValidJumpDest_index 668 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 979 = true :=
  Artifact.isValidJumpDest_index 676 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1003 = true :=
  Artifact.isValidJumpDest_index 688 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1038 = true :=
  Artifact.isValidJumpDest_index 709 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1046 = true :=
  Artifact.isValidJumpDest_index 714 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1065 = true :=
  Artifact.isValidJumpDest_index 723 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2682 = true :=
  Artifact.isValidJumpDest_index 1995 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1065 = true :=
  Artifact.isValidJumpDest_index 723 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1077 = true :=
  Artifact.isValidJumpDest_index 731 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1092 = true :=
  Artifact.isValidJumpDest_index 738 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1117 = true :=
  Artifact.isValidJumpDest_index 751 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1118 = true :=
  Artifact.isValidJumpDest_index 752 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1136 = true :=
  Artifact.isValidJumpDest_index 764 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1164 = true :=
  Artifact.isValidJumpDest_index 779 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1174 = true :=
  Artifact.isValidJumpDest_index 787 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1180 = true :=
  Artifact.isValidJumpDest_index 791 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1191 = true :=
  Artifact.isValidJumpDest_index 800 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1195 = true :=
  Artifact.isValidJumpDest_index 802 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1206 = true :=
  Artifact.isValidJumpDest_index 809 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1219 = true :=
  Artifact.isValidJumpDest_index 819 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1254 = true :=
  Artifact.isValidJumpDest_index 846 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1268 = true :=
  Artifact.isValidJumpDest_index 856 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1392 = true :=
  Artifact.isValidJumpDest_index 958 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1491 = true :=
  Artifact.isValidJumpDest_index 1037 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1522 = true :=
  Artifact.isValidJumpDest_index 1062 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1578 = true :=
  Artifact.isValidJumpDest_index 1107 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1651 = true :=
  Artifact.isValidJumpDest_index 1165 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1662 = true :=
  Artifact.isValidJumpDest_index 1172 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1674 = true :=
  Artifact.isValidJumpDest_index 1182 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1695 = true :=
  Artifact.isValidJumpDest_index 1195 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1717 = true :=
  Artifact.isValidJumpDest_index 1210 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1744 = true :=
  Artifact.isValidJumpDest_index 1230 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2438 = true :=
  Artifact.isValidJumpDest_index 1817 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2473 = true :=
  Artifact.isValidJumpDest_index 1840 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2511 = true :=
  Artifact.isValidJumpDest_index 1862 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4337 = true :=
  Artifact.isValidJumpDest_index 3265 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4499 = true :=
  Artifact.isValidJumpDest_index 3382 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4746 = true :=
  Artifact.isValidJumpDest_index 3561 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 3554 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
