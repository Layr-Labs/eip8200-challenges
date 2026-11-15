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
    CycleSubmission.Artifact.artifact.instructionPC 564 = 774 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 592 = 812 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 629 = 859 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 807 = 1109 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 807 = 1109 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 808 = 1110 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 818 = 1132 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 819 = 1134 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fastPC0 (i : Nat) (hi : 564 ≤ i) (hii : i ≤ 591) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([774,775,777,778,780,781,782,784,785,788,789,791,792,793,794,796,797,798,800,801,802,804,805,807,808,809,810,811] : List Nat)[i - 564]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC1 (i : Nat) (hi : 592 ≤ i) (hii : i ≤ 628) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([812,813,814,815,816,818,819,820,821,822,823,824,825,826,827,828,830,831,832,834,835,836,837,839,840,841,843,844,847,848,849,850,851,853,854,855,858] : List Nat)[i - 592]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC2 (i : Nat) (hi : 629 ≤ i) (hii : i ≤ 807) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([859,860,863,864,865,866,867,868,869,870,871,872,873,875,876,877,879,882,883,884,885,888,889,890,893,894,897,900,903,904,906,907,910,911,914,915,917,918,919,920,921,924,925,926,927,929,930,931,932,935,936,937,938,939,942,943,944,945,946,947,948,950,951,952,953,956,957,958,959,960,963,964,965,966,967,968,969,971,972,973,974,977,978,979,980,981,984,985,986,987,988,989,990,992,993,994,995,998,999,1000,1001,1002,1005,1006,1007,1008,1009,1010,1011,1012,1014,1015,1016,1017,1020,1021,1022,1023,1024,1027,1028,1029,1030,1031,1032,1033,1035,1036,1037,1038,1041,1042,1043,1044,1045,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1061,1062,1063,1064,1065,1068,1069,1070,1071,1072,1073,1074,1077,1078,1079,1082,1083,1086,1087,1088,1091,1094,1095,1096,1097,1098,1099,1102,1105,1106,1107,1108,1109] : List Nat)[i - 629]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 807 ≤ i) (hii : i ≤ 807) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1109] : List Nat)[i - 807]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 807 ≤ i) (hii : i ≤ 807) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1109] : List Nat)[i - 807]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 808 ≤ i) (hii : i ≤ 818) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1110,1112,1113,1115,1116,1117,1119,1120,1121,1131,1132] : List Nat)[i - 808]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 818 ≤ i) (hii : i ≤ 818) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1132] : List Nat)[i - 818]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 819 ≤ i) (hii : i ≤ 829) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([1134,1135,1136,1139,1140,1173,1174,1175,1176,1177,1178] : List Nat)[i - 819]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 483 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 353
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2745 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2138
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10563 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7978
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1109 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 807
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1098 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 800
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1087 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 793
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast
