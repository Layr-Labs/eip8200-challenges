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
    CycleSubmission.Artifact.artifact.instructionPC 386 = 559 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 414 = 597 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 451 = 644 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 629 = 894 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 629 = 894 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 630 = 895 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 640 = 917 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 641 = 919 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fastPC0 (i : Nat) (hi : 386 ≤ i) (hii : i ≤ 413) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([559,560,562,563,565,566,567,569,570,573,574,576,577,578,579,581,582,583,585,586,587,589,590,592,593,594,595,596] : List Nat)[i - 386]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC1 (i : Nat) (hi : 414 ≤ i) (hii : i ≤ 450) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([597,598,599,600,601,603,604,605,606,607,608,609,610,611,612,613,615,616,617,619,620,621,622,624,625,626,628,629,632,633,634,635,636,638,639,640,643] : List Nat)[i - 414]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC2 (i : Nat) (hi : 451 ≤ i) (hii : i ≤ 629) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([644,645,648,649,650,651,652,653,654,655,656,657,658,660,661,662,664,667,668,669,670,673,674,675,678,679,682,685,688,689,691,692,695,696,699,700,702,703,704,705,706,709,710,711,712,714,715,716,717,720,721,722,723,724,727,728,729,730,731,732,733,735,736,737,738,741,742,743,744,745,748,749,750,751,752,753,754,756,757,758,759,762,763,764,765,766,769,770,771,772,773,774,775,777,778,779,780,783,784,785,786,787,790,791,792,793,794,795,796,797,799,800,801,802,805,806,807,808,809,812,813,814,815,816,817,818,820,821,822,823,826,827,828,829,830,833,834,835,836,837,838,839,840,841,842,843,846,847,848,849,850,853,854,855,856,857,858,859,862,863,864,867,868,871,872,873,876,879,880,881,882,883,884,887,890,891,892,893,894] : List Nat)[i - 451]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 629 ≤ i) (hii : i ≤ 629) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([894] : List Nat)[i - 629]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 629 ≤ i) (hii : i ≤ 629) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([894] : List Nat)[i - 629]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 630 ≤ i) (hii : i ≤ 640) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([895,897,898,900,901,902,904,905,906,916,917] : List Nat)[i - 630]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 640 ≤ i) (hii : i ≤ 640) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([917] : List Nat)[i - 640]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 641 ≤ i) (hii : i ≤ 649) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([919,920,921,924,925,927,929,930,931] : List Nat)[i - 641]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 514 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 352
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2501 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1961
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10322 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7804
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 894 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 629
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 883 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 622
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 872 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 615
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast
