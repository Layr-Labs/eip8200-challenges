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
  | 3 => 2103
  | _ => 2235

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2028
  | 1 => 2028
  | 2 => 2028
  | 3 => 2028
  | 4 => 2478
  | 5 => 2478
  | 6 => 2478
  | 7 => 2478
  | 8 => 2944
  | 9 => 2944
  | 10 => 2944
  | 11 => 2944
  | 12 => 3394
  | 13 => 3411
  | 14 => 3428
  | 15 => 3445
  | 16 => 3567
  | 17 => 3567
  | 18 => 3567
  | 19 => 3567
  | _ => 3967

def rightReturnIndex : Nat → Nat
  | 0 => 2478
  | 1 => 2478
  | 2 => 2478
  | 3 => 2478
  | 4 => 2944
  | 5 => 2944
  | 6 => 2944
  | 7 => 2944
  | 8 => 3394
  | 9 => 3394
  | 10 => 3394
  | 11 => 3394
  | 12 => 3410
  | 13 => 3427
  | 14 => 3444
  | 15 => 3566
  | 16 => 3967
  | 17 => 3967
  | 18 => 3967
  | 19 => 3967
  | _ => 3967

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2028
  | 1 => 2478
  | 2 => 2944
  | 3 => 3459
  | _ => 3567

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2477
  | 1 => 2943
  | 2 => 3393
  | 3 => 3565
  | _ => 3966

def rightHelperPCNat : Nat → Nat
  | 0 => 2753
  | 1 => 3255
  | 2 => 3773
  | 3 => 4462
  | _ => 4610

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2017
theorem route_pc : A.instructionPC routeIndex = 2737 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2018
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2738 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3967
theorem tail_pc : A.instructionPC tailIndex = 5058 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 4014
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 296
theorem schedule_pc : A.instructionPC scheduleIndex = 532 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 4015
theorem output_pc : A.instructionPC outputIndex = 5116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4068
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
