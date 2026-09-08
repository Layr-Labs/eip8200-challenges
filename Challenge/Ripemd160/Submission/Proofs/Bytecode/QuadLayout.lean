import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-! Exact cached-mask four-group layout. Replaced shared groups have only lane-boundary metadata; their old call/helper certificates are not used. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout

open EvmSemantics Challenge.EvmProof

abbrev A := Artifact.submissionArtifact

theorem code_bound : A.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide

theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (A.instructionPC index)).toNat = A.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (A.instructionPC_le_code_size index) code_bound)

def leftWrapperIndex : Nat → Nat
  | 0 => 371
  | 1 => 371
  | 2 => 371
  | 3 => 371
  | 4 => 771
  | 5 => 788
  | 6 => 805
  | 7 => 822
  | 8 => 944
  | 9 => 944
  | 10 => 944
  | 11 => 944
  | 12 => 1394
  | 13 => 1411
  | 14 => 1428
  | 15 => 1445
  | 16 => 1567
  | 17 => 1567
  | 18 => 1567
  | 19 => 1567
  | _ => 2017

def leftReturnIndex : Nat → Nat
  | 0 => 771
  | 1 => 771
  | 2 => 771
  | 3 => 771
  | 4 => 787
  | 5 => 804
  | 6 => 821
  | 7 => 943
  | 8 => 1394
  | 9 => 1394
  | 10 => 1394
  | 11 => 1394
  | 12 => 1410
  | 13 => 1427
  | 14 => 1444
  | 15 => 1566
  | 16 => 2017
  | 17 => 2017
  | 18 => 2017
  | 19 => 2017
  | _ => 2017

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 371
  | 1 => 836
  | 2 => 944
  | 3 => 1459
  | _ => 1567

def leftHelperJumpIndex : Nat → Nat
  | 0 => 770
  | 1 => 942
  | 2 => 1393
  | 3 => 1565
  | _ => 2016

def leftHelperPCNat : Nat → Nat
  | 0 => 648
  | 1 => 1282
  | 2 => 1414
  | 3 => 2102
  | _ => 2234

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2026
  | 1 => 2026
  | 2 => 2026
  | 3 => 2026
  | 4 => 2475
  | 5 => 2475
  | 6 => 2475
  | 7 => 2475
  | 8 => 2940
  | 9 => 2940
  | 10 => 2940
  | 11 => 2940
  | 12 => 3390
  | 13 => 3406
  | 14 => 3423
  | 15 => 3440
  | 16 => 3562
  | 17 => 3562
  | 18 => 3562
  | 19 => 3562
  | _ => 3962

def rightReturnIndex : Nat → Nat
  | 0 => 2475
  | 1 => 2475
  | 2 => 2475
  | 3 => 2475
  | 4 => 2940
  | 5 => 2940
  | 6 => 2940
  | 7 => 2940
  | 8 => 3390
  | 9 => 3390
  | 10 => 3390
  | 11 => 3390
  | 12 => 3405
  | 13 => 3422
  | 14 => 3439
  | 15 => 3561
  | 16 => 3962
  | 17 => 3962
  | 18 => 3962
  | 19 => 3962
  | _ => 3962

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2026
  | 1 => 2475
  | 2 => 2940
  | 3 => 3454
  | _ => 3562

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2474
  | 1 => 2939
  | 2 => 3388
  | 3 => 3560
  | _ => 3961

def rightHelperPCNat : Nat → Nat
  | 0 => 2751
  | 1 => 3252
  | 2 => 3769
  | 3 => 4457
  | _ => 4605

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2015
theorem route_pc : A.instructionPC routeIndex = 2735 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2016
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2736 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3962
theorem tail_pc : A.instructionPC tailIndex = 5053 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 4009
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 296
theorem schedule_pc : A.instructionPC scheduleIndex = 532 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 4010
theorem output_pc : A.instructionPC outputIndex = 5116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4063
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
