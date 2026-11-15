import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode,hplain,havailable⟩
def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rw [CycleSubmission.Artifact.instruction_get]; rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).1)
    (hplain : YulEvmCompiler.plainOp op := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).2.1)
    (havailable : op.availableInFork .Osaka = true := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).2.2) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.op op,hget,wfOp hopcode hplain havailable⟩
def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rw [CycleSubmission.Artifact.instruction_get]; rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.push width value,hget,hwf⟩
private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,List.take_add,
    assembleBytes_append,List.length_append]
private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one,hget,Option.toList_some,assembleBytes_append,
    assembleBytes_cons,assembleBytes_nil,List.append_nil,List.length_append]
private theorem fastPCAnchor0 :
    CycleSubmission.Artifact.artifact.instructionPC 598 = 819 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 626 = 857 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 663 = 904 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 841 = 1154 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 841 = 1154 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 842 = 1155 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 852 = 1177 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 853 = 1179 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fastPC0 (i : Nat) (hi : 598 ≤ i) (hii : i ≤ 625) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([819,820,822,823,825,826,827,829,830,833,834,836,837,838,839,841,842,843,845,846,847,849,850,852,853,854,855,856] : List Nat)[i - 598]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC1 (i : Nat) (hi : 626 ≤ i) (hii : i ≤ 662) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([857,858,859,860,861,863,864,865,866,867,868,869,870,871,872,873,875,876,877,879,880,881,882,884,885,886,888,889,892,893,894,895,896,898,899,900,903] : List Nat)[i - 626]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC2 (i : Nat) (hi : 663 ≤ i) (hii : i ≤ 841) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([904,905,908,909,910,911,912,913,914,915,916,917,918,920,921,922,924,927,928,929,930,933,934,935,938,939,942,945,948,949,951,952,955,956,959,960,962,963,964,965,966,969,970,971,972,974,975,976,977,980,981,982,983,984,987,988,989,990,991,992,993,995,996,997,998,1001,1002,1003,1004,1005,1008,1009,1010,1011,1012,1013,1014,1016,1017,1018,1019,1022,1023,1024,1025,1026,1029,1030,1031,1032,1033,1034,1035,1037,1038,1039,1040,1043,1044,1045,1046,1047,1050,1051,1052,1053,1054,1055,1056,1057,1059,1060,1061,1062,1065,1066,1067,1068,1069,1072,1073,1074,1075,1076,1077,1078,1080,1081,1082,1083,1086,1087,1088,1089,1090,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1106,1107,1108,1109,1110,1113,1114,1115,1116,1117,1118,1119,1122,1123,1124,1127,1128,1131,1132,1133,1136,1139,1140,1141,1142,1143,1144,1147,1150,1151,1152,1153,1154] : List Nat)[i - 663]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 841 ≤ i) (hii : i ≤ 841) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1154] : List Nat)[i - 841]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 841 ≤ i) (hii : i ≤ 841) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1154] : List Nat)[i - 841]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 842 ≤ i) (hii : i ≤ 852) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1155,1157,1158,1160,1161,1162,1164,1165,1166,1176,1177] : List Nat)[i - 842]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 852 ≤ i) (hii : i ≤ 852) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1177] : List Nat)[i - 852]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 853 ≤ i) (hii : i ≤ 862) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1179,1180,1181,1184,1185,1218,1219,1220,1221,1222] : List Nat)[i - 853]! := by
  interval_cases i <;>
    exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
@[simp] theorem fastPC15_part1 (i : Nat) (hi : 4905 ≤ i) (hii : i ≤ 4905) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([6699] : List Nat)[i - 4905]! := by
  interval_cases i
  exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 774 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 564
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 6642 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 4864
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10876 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8196
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1154 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 841
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1143 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 834
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1132 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 827
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast
