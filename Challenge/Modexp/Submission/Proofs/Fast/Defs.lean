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
    Artifact.submissionArtifact.instructionPC 494 = 709 := by
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 523 = 748 := by
  calc
    Artifact.submissionArtifact.instructionPC 523 =
        Artifact.submissionArtifact.instructionPC 494 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 494).take 29)).length :=
      instructionPC_add Artifact.submissionArtifact 494 29
    _ = 748 := by
      rw [fastPCAnchor0]
      rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 560 = 800 := by
  calc
    Artifact.submissionArtifact.instructionPC 560 =
        Artifact.submissionArtifact.instructionPC 523 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 523).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 523 37
    _ = 800 := by
      rw [fastPCAnchor1]
      rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 595 = 843 := by
  calc
    Artifact.submissionArtifact.instructionPC 595 =
        Artifact.submissionArtifact.instructionPC 560 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 560).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 560 35
    _ = 843 := by
      rw [fastPCAnchor2]
      rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 627 = 883 := by
  calc
    Artifact.submissionArtifact.instructionPC 627 =
        Artifact.submissionArtifact.instructionPC 595 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 595).take 32)).length :=
      instructionPC_add Artifact.submissionArtifact 595 32
    _ = 883 := by
      rw [fastPCAnchor3]
      rfl

private theorem fastPCAnchor5 :
    Artifact.submissionArtifact.instructionPC 657 = 940 := by
  calc
    Artifact.submissionArtifact.instructionPC 657 =
        Artifact.submissionArtifact.instructionPC 627 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 627).take 30)).length :=
      instructionPC_add Artifact.submissionArtifact 627 30
    _ = 940 := by
      rw [fastPCAnchor4]
      rfl

private theorem fastPCAnchor6 :
    Artifact.submissionArtifact.instructionPC 677 = 968 := by
  calc
    Artifact.submissionArtifact.instructionPC 677 =
        Artifact.submissionArtifact.instructionPC 657 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 657).take 20)).length :=
      instructionPC_add Artifact.submissionArtifact 657 20
    _ = 968 := by
      rw [fastPCAnchor5]
      rfl

private theorem fastPCAnchor7 :
    Artifact.submissionArtifact.instructionPC 716 = 1036 := by
  calc
    Artifact.submissionArtifact.instructionPC 716 =
        Artifact.submissionArtifact.instructionPC 677 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 677).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 677 39
    _ = 1036 := by
      rw [fastPCAnchor6]
      rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 741 = 1083 := by
  calc
    Artifact.submissionArtifact.instructionPC 741 =
        Artifact.submissionArtifact.instructionPC 716 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 716).take 25)).length :=
      instructionPC_add Artifact.submissionArtifact 716 25
    _ = 1083 := by
      rw [fastPCAnchor7]
      rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 783 = 1156 := by
  calc
    Artifact.submissionArtifact.instructionPC 783 =
        Artifact.submissionArtifact.instructionPC 741 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 741).take 42)).length :=
      instructionPC_add Artifact.submissionArtifact 741 42
    _ = 1156 := by
      rw [fastPCAnchor8]
      rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 817 = 1205 := by
  calc
    Artifact.submissionArtifact.instructionPC 817 =
        Artifact.submissionArtifact.instructionPC 783 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 783).take 34)).length :=
      instructionPC_add Artifact.submissionArtifact 783 34
    _ = 1205 := by
      rw [fastPCAnchor9]
      rfl

private theorem fastPCAnchor11 :
    Artifact.submissionArtifact.instructionPC 856 = 1256 := by
  calc
    Artifact.submissionArtifact.instructionPC 856 =
        Artifact.submissionArtifact.instructionPC 817 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 817).take 39)).length :=
      instructionPC_add Artifact.submissionArtifact 817 39
    _ = 1256 := by
      rw [fastPCAnchor10]
      rfl

private theorem fastPCAnchor12 :
    Artifact.submissionArtifact.instructionPC 893 = 1293 := by
  calc
    Artifact.submissionArtifact.instructionPC 893 =
        Artifact.submissionArtifact.instructionPC 856 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 856).take 37)).length :=
      instructionPC_add Artifact.submissionArtifact 856 37
    _ = 1293 := by
      rw [fastPCAnchor11]
      rfl

private theorem fastPCAnchor13 :
    Artifact.submissionArtifact.instructionPC 936 = 1352 := by
  calc
    Artifact.submissionArtifact.instructionPC 936 =
        Artifact.submissionArtifact.instructionPC 893 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 893).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 893 43
    _ = 1352 := by
      rw [fastPCAnchor12]
      rfl

private theorem fastPCAnchor14 :
    Artifact.submissionArtifact.instructionPC 977 = 1399 := by
  calc
    Artifact.submissionArtifact.instructionPC 977 =
        Artifact.submissionArtifact.instructionPC 936 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 936).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 936 41
    _ = 1399 := by
      rw [fastPCAnchor13]
      rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 1013 = 1444 := by
  calc
    Artifact.submissionArtifact.instructionPC 1013 =
        Artifact.submissionArtifact.instructionPC 977 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 977).take 36)).length :=
      instructionPC_add Artifact.submissionArtifact 977 36
    _ = 1444 := by
      rw [fastPCAnchor14]
      rfl

private theorem fastPCAnchor16 :
    Artifact.submissionArtifact.instructionPC 1054 = 1500 := by
  calc
    Artifact.submissionArtifact.instructionPC 1054 =
        Artifact.submissionArtifact.instructionPC 1013 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1013).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1013 41
    _ = 1500 := by
      rw [fastPCAnchor15]
      rfl

private theorem fastPCAnchor17 :
    Artifact.submissionArtifact.instructionPC 1095 = 1546 := by
  calc
    Artifact.submissionArtifact.instructionPC 1095 =
        Artifact.submissionArtifact.instructionPC 1054 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1054).take 41)).length :=
      instructionPC_add Artifact.submissionArtifact 1054 41
    _ = 1546 := by
      rw [fastPCAnchor16]
      rfl

private theorem fastPCAnchor18 :
    Artifact.submissionArtifact.instructionPC 1119 = 1578 := by
  calc
    Artifact.submissionArtifact.instructionPC 1119 =
        Artifact.submissionArtifact.instructionPC 1095 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1095).take 24)).length :=
      instructionPC_add Artifact.submissionArtifact 1095 24
    _ = 1578 := by
      rw [fastPCAnchor17]
      rfl

private theorem fastPCAnchor19 :
    Artifact.submissionArtifact.instructionPC 1162 = 1636 := by
  calc
    Artifact.submissionArtifact.instructionPC 1162 =
        Artifact.submissionArtifact.instructionPC 1119 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1119).take 43)).length :=
      instructionPC_add Artifact.submissionArtifact 1119 43
    _ = 1636 := by
      rw [fastPCAnchor18]
      rfl

private theorem fastPCAnchor20 :
    Artifact.submissionArtifact.instructionPC 1165 = 1639 := by
  calc
    Artifact.submissionArtifact.instructionPC 1165 =
        Artifact.submissionArtifact.instructionPC 1162 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1162).take 3)).length :=
      instructionPC_add Artifact.submissionArtifact 1162 3
    _ = 1639 := by
      rw [fastPCAnchor19]
      rfl

private theorem fastPCAnchor21 :
    Artifact.submissionArtifact.instructionPC 1182 = 1662 := by
  calc
    Artifact.submissionArtifact.instructionPC 1182 =
        Artifact.submissionArtifact.instructionPC 1165 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1165).take 17)).length :=
      instructionPC_add Artifact.submissionArtifact 1165 17
    _ = 1662 := by
      rw [fastPCAnchor20]
      rfl

private theorem fastPCAnchor22 :
    Artifact.submissionArtifact.instructionPC 1195 = 1683 := by
  calc
    Artifact.submissionArtifact.instructionPC 1195 =
        Artifact.submissionArtifact.instructionPC 1182 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1182).take 13)).length :=
      instructionPC_add Artifact.submissionArtifact 1182 13
    _ = 1683 := by
      rw [fastPCAnchor21]
      rfl

private theorem fastPCAnchor23 :
    Artifact.submissionArtifact.instructionPC 1230 = 1732 := by
  calc
    Artifact.submissionArtifact.instructionPC 1230 =
        Artifact.submissionArtifact.instructionPC 1195 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1195).take 35)).length :=
      instructionPC_add Artifact.submissionArtifact 1195 35
    _ = 1732 := by
      rw [fastPCAnchor22]
      rfl

private theorem fastPCAnchor24 :
    Artifact.submissionArtifact.instructionPC 1840 = 2434 := by
  calc
    Artifact.submissionArtifact.instructionPC 1840 =
        Artifact.submissionArtifact.instructionPC 1230 +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop 1230).take 610)).length :=
      instructionPC_add Artifact.submissionArtifact 1230 610
    _ = 2434 := by
      rw [fastPCAnchor23]
      rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 494 ≤ i) (hii : i ≤ 522) :
    Artifact.submissionArtifact.instructionPC i =
      [709,710,712,713,714,716,717,718,720,721,724,725,727,728,729,730,731,733,734,736,737,738,740,741,742,743,744,746,747][i - 494]! := by
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
      [748,749,750,752,753,754,755,756,757,758,761,762,764,765,766,767,768,769,771,772,773,776,777,778,781,782,783,784,786,787,790,791,793,794,795,796,799][i - 523]! := by
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
      [800,801,804,805,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,826,827,829,830,831,832,833,835,836,837,838,839,840,842][i - 560]! := by
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
      [843,844,845,846,847,849,850,851,852,853,854,856,857,858,859,860,861,863,864,865,866,867,868,870,871,872,873,874,877,878,879,880][i - 595]! := by
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
      [883,884,885,888,889,892,895,896,899,902,905,906,907,910,913,914,917,920,921,922,923,924,925,927,928,930,931,935,936,939][i - 627]! := by
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
      [940,941,942,943,944,947,948,949,950,951,954,955,956,957,958,959,962,963,966,967][i - 657]! := by
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
      [968,969,970,971,974,975,978,981,984,987,990,991,992,993,994,995,997,998,999,1000,1002,1003,1004,1005,1008,1009,1010,1013,1016,1019,1022,1025,1026,1027,1029,1030,1033,1034,1035][i - 677]! := by
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
      [1036,1037,1040,1043,1046,1049,1052,1053,1054,1055,1056,1057,1060,1061,1064,1065,1066,1069,1072,1073,1076,1079,1080,1081,1082][i - 716]! := by
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
      [1083,1084,1085,1088,1089,1092,1095,1098,1101,1104,1105,1106,1107,1109,1110,1111,1114,1115,1116,1117,1119,1120,1123,1124,1125,1126,1128,1129,1132,1133,1134,1137,1140,1143,1146,1149,1150,1151,1152,1153,1154,1155][i - 741]! := by
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
      [1156,1159,1160,1161,1162,1163,1164,1167,1168,1169,1170,1171,1172,1173,1174,1175,1178,1179,1180,1183,1184,1187,1188,1189,1190,1193,1194,1195,1197,1198,1199,1200,1203,1204][i - 783]! := by
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
      [1205,1206,1207,1208,1211,1212,1213,1215,1216,1217,1220,1221,1222,1223,1224,1226,1227,1228,1230,1231,1232,1233,1234,1235,1236,1238,1239,1240,1241,1242,1243,1244,1245,1246,1249,1250,1251,1254,1255][i - 817]! := by
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
      [1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292][i - 856]! := by
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
      [1293,1294,1296,1297,1298,1299,1301,1302,1303,1304,1305,1306,1307,1310,1311,1312,1313,1314,1317,1318,1319,1320,1323,1324,1325,1328,1329,1332,1333,1334,1337,1338,1339,1340,1343,1344,1345,1346,1347,1348,1349,1350,1351][i - 893]! := by
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
      [1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1367,1368,1370,1371,1372,1375,1376,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398][i - 936]! := by
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
      [1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1414,1415,1417,1418,1419,1420,1421,1422,1424,1425,1426,1429,1430,1431,1434,1435,1436,1437,1438,1439,1440,1441][i - 977]! := by
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
      [1444,1445,1446,1447,1450,1451,1452,1455,1456,1457,1460,1461,1463,1464,1465,1466,1467,1468,1471,1472,1473,1474,1475,1478,1479,1480,1483,1484,1485,1486,1487,1489,1490,1491,1492,1493,1494,1496,1497,1498,1499][i - 1013]! := by
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
      [1500,1501,1502,1503,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1532,1533,1534,1535,1537,1538,1539,1540,1541,1543,1544,1545][i - 1054]! := by
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
      [1546,1549,1550,1551,1554,1555,1556,1557,1558,1561,1562,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577][i - 1095]! := by
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
      [1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1591,1592,1593,1594,1596,1597,1598,1599,1600,1602,1603,1604,1605,1608,1609,1610,1613,1614,1615,1616,1617,1618,1621,1622,1623,1626,1627,1628,1631,1632,1635][i - 1119]! := by
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
      [1636,1637,1638][i - 1162]! := by
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
      [1639,1640,1643,1644,1645,1646,1649,1650,1651,1652,1653,1654,1655,1658,1659,1660,1661][i - 1165]! := by
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
      [1662,1663,1664,1665,1667,1668,1669,1672,1673,1675,1678,1679,1682][i - 1182]! := by
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
      [1683,1684,1685,1688,1689,1690,1691,1692,1693,1694,1695,1698,1699,1701,1704,1705,1706,1707,1708,1710,1711,1712,1713,1715,1716,1717,1718,1720,1721,1722,1724,1725,1727,1728,1731][i - 1195]! := by
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
      [1732,1733,1734,1737,1738,1741,1742,1745,1748,1749,1752,1755][i - 1230]! := by
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
      [2434,2435,2436,2437,2438,2439,2440,2442,2443,2444,2445,2448,2449,2450,2452,2455,2456,2459,2462,2465,2468,2471,2472,2473,2474,2476,2477,2479,2480,2481,2482,2484,2485,2486,2488,2489,2491,2492,2493,2494,2495,2497,2498,2499,2501,2504][i - 1840]! := by
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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 647 = true :=
  Artifact.isValidJumpDest_index 450 (by rfl)

theorem jumpDest1526 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 884 = true :=
  Artifact.isValidJumpDest_index 628 (by rfl)

theorem jumpDest1548 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 906 = true :=
  Artifact.isValidJumpDest_index 638 (by rfl)

theorem jumpDest1565 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 921 = true :=
  Artifact.isValidJumpDest_index 645 (by rfl)

theorem jumpDest1584 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 940 = true :=
  Artifact.isValidJumpDest_index 657 (by rfl)

theorem jumpDest1599 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 955 = true :=
  Artifact.isValidJumpDest_index 668 (by rfl)

theorem jumpDest1611 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 967 = true :=
  Artifact.isValidJumpDest_index 676 (by rfl)

theorem jumpDest1635 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 991 = true :=
  Artifact.isValidJumpDest_index 688 (by rfl)

theorem jumpDest1670 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1026 = true :=
  Artifact.isValidJumpDest_index 709 (by rfl)

theorem jumpDest1678 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1034 = true :=
  Artifact.isValidJumpDest_index 714 (by rfl)

theorem jumpDest1697 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1053 = true :=
  Artifact.isValidJumpDest_index 723 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2642 = true :=
  Artifact.isValidJumpDest_index 1995 (by rfl)

theorem jumpDest1703 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1053 = true :=
  Artifact.isValidJumpDest_index 723 (by rfl)

theorem jumpDest1715 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1065 = true :=
  Artifact.isValidJumpDest_index 731 (by rfl)

theorem jumpDest1732 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1080 = true :=
  Artifact.isValidJumpDest_index 738 (by rfl)

theorem jumpDest1757 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1105 = true :=
  Artifact.isValidJumpDest_index 751 (by rfl)

theorem jumpDest1758 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1106 = true :=
  Artifact.isValidJumpDest_index 752 (by rfl)

theorem jumpDest1776 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1124 = true :=
  Artifact.isValidJumpDest_index 764 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1152 = true :=
  Artifact.isValidJumpDest_index 779 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1162 = true :=
  Artifact.isValidJumpDest_index 787 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1168 = true :=
  Artifact.isValidJumpDest_index 791 (by rfl)

theorem jumpDest1837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1179 = true :=
  Artifact.isValidJumpDest_index 800 (by rfl)

theorem jumpDest1841 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1183 = true :=
  Artifact.isValidJumpDest_index 802 (by rfl)

theorem jumpDest1852 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1194 = true :=
  Artifact.isValidJumpDest_index 809 (by rfl)

theorem jumpDest1865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1207 = true :=
  Artifact.isValidJumpDest_index 819 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1242 = true :=
  Artifact.isValidJumpDest_index 846 (by rfl)

theorem jumpDest1914 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1256 = true :=
  Artifact.isValidJumpDest_index 856 (by rfl)

theorem jumpDest2038 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1380 = true :=
  Artifact.isValidJumpDest_index 958 (by rfl)

theorem jumpDest2137 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1479 = true :=
  Artifact.isValidJumpDest_index 1037 (by rfl)

theorem jumpDest2168 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1510 = true :=
  Artifact.isValidJumpDest_index 1062 (by rfl)

theorem jumpDest2225 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1566 = true :=
  Artifact.isValidJumpDest_index 1107 (by rfl)

theorem jumpDest2299 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1639 = true :=
  Artifact.isValidJumpDest_index 1165 (by rfl)

theorem jumpDest2310 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1650 = true :=
  Artifact.isValidJumpDest_index 1172 (by rfl)

theorem jumpDest2322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1662 = true :=
  Artifact.isValidJumpDest_index 1182 (by rfl)

theorem jumpDest2343 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1683 = true :=
  Artifact.isValidJumpDest_index 1195 (by rfl)

theorem jumpDest2365 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1705 = true :=
  Artifact.isValidJumpDest_index 1210 (by rfl)

theorem jumpDest2392 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1732 = true :=
  Artifact.isValidJumpDest_index 1230 (by rfl)

theorem jumpDest3111 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2399 = true :=
  Artifact.isValidJumpDest_index 1817 (by rfl)

theorem jumpDest3146 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2434 = true :=
  Artifact.isValidJumpDest_index 1840 (by rfl)

theorem jumpDest3184 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2472 = true :=
  Artifact.isValidJumpDest_index 1862 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4349 = true :=
  Artifact.isValidJumpDest_index 3302 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4509 = true :=
  Artifact.isValidJumpDest_index 3417 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4756 = true :=
  Artifact.isValidJumpDest_index 3596 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4745 = true :=
  Artifact.isValidJumpDest_index 3589 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
