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
  ⟨hopcode, hplain, havailable⟩
def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rw [CycleSubmission.Artifact.instruction_get]; rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).1)
    (hplain : YulEvmCompiler.plainOp op := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).2.1)
    (havailable : op.availableInFork .Osaka = true := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).2.2) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩
def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rw [CycleSubmission.Artifact.instruction_get]; rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩
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
    CycleSubmission.Artifact.artifact.instructionPC 638 = 903 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 644 = 910 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 646 = 912 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 660 = 937 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 662 = 940 := by
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
@[simp] theorem fastPC2 (i : Nat) (hi : 456 ≤ i) (hii : i ≤ 637) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([649,650,653,654,655,656,657,658,659,660,661,662,663,664,666,667,668,670,673,674,677,678,679,680,683,684,685,686,687,690,693,696,697,699,700,703,704,707,708,710,711,712,713,714,717,718,719,720,722,723,724,725,728,729,730,731,732,735,736,737,738,739,740,741,743,744,745,746,749,750,751,752,753,756,757,758,759,760,761,762,764,765,766,767,770,771,772,773,774,777,778,779,780,781,782,783,785,786,787,788,791,792,793,794,795,798,799,800,801,802,803,804,805,807,808,809,810,813,814,815,816,817,820,821,822,823,824,825,826,828,829,830,831,834,835,836,837,838,841,842,843,844,845,846,847,848,849,850,851,854,855,856,857,858,861,862,863,864,865,866,867,870,871,872,875,876,879,880,881,884,887,888,889,890,891,892,895,898,899,900,901,902] : List Nat)[i - 456]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 638 ≤ i) (hii : i ≤ 643) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([903,904,905,906,908,909] : List Nat)[i - 638]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 644 ≤ i) (hii : i ≤ 645) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([910,911] : List Nat)[i - 644]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 646 ≤ i) (hii : i ≤ 659) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([912,918,920,921,922,925,926,927,928,930,931,933,934,936] : List Nat)[i - 646]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 660 ≤ i) (hii : i ≤ 661) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([937,938] : List Nat)[i - 660]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 662 ≤ i) (hii : i ≤ 670) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([940,941,942,945,946,948,950,951,952] : List Nat)[i - 662]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 519 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 357
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2522 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1982
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 9532 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7422
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 911 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 645
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 891 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 630
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 880 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 623
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast
