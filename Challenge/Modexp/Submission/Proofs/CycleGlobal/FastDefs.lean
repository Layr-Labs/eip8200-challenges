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
    CycleSubmission.Artifact.artifact.instructionPC 391 = 564 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 419 = 602 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 456 = 649 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 637 = 902 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 637 = 902 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 638 = 903 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 648 = 925 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 649 = 927 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fastPC0 (i : Nat) (hi : 391 ≤ i) (hii : i ≤ 418) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([564,565,567,568,570,571,572,574,575,578,579,581,582,583,584,586,587,588,590,591,592,594,595,597,598,599,600,601] : List Nat)[i - 391]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC1 (i : Nat) (hi : 419 ≤ i) (hii : i ≤ 455) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([602,603,604,605,606,608,609,610,611,612,613,614,615,616,617,618,620,621,622,624,625,626,627,629,630,631,633,634,637,638,639,640,641,643,644,645,648] : List Nat)[i - 419]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC2 (i : Nat) (hi : 456 ≤ i) (hii : i ≤ 636) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([649,650,653,654,655,656,657,658,659,660,661,662,663,664,666,667,668,670,673,674,675,676,677,680,681,682,685,686,689,692,695,696,698,699,702,703,706,707,709,710,711,712,713,716,717,718,719,721,722,723,724,727,728,729,730,731,734,735,736,737,738,739,740,742,743,744,745,748,749,750,751,752,755,756,757,758,759,760,761,763,764,765,766,769,770,771,772,773,776,777,778,779,780,781,782,784,785,786,787,790,791,792,793,794,797,798,799,800,801,802,803,804,806,807,808,809,812,813,814,815,816,819,820,821,822,823,824,825,827,828,829,830,833,834,835,836,837,840,841,842,843,844,845,846,847,848,849,850,853,854,855,856,857,860,861,862,863,864,865,866,869,870,871,874,875,878,879,880,883,886,887,888,889,890,891,894,897,898,899,900,901] : List Nat)[i - 456]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 637 ≤ i) (hii : i ≤ 637) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([902] : List Nat)[i - 637]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 637 ≤ i) (hii : i ≤ 637) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([902] : List Nat)[i - 637]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 638 ≤ i) (hii : i ≤ 648) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([903,905,906,908,909,910,912,913,914,924,925] : List Nat)[i - 638]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 648 ≤ i) (hii : i ≤ 648) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([925] : List Nat)[i - 648]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 649 ≤ i) (hii : i ≤ 657) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([927,928,929,932,933,935,937,938,939] : List Nat)[i - 649]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 519 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 357
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2513 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1973
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10344 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7832
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 902 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 637
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 890 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 629
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 879 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 622
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast
