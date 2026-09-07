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
  | 0 => 341
  | 1 => 341
  | 2 => 341
  | 3 => 341
  | 4 => 741
  | 5 => 758
  | 6 => 775
  | 7 => 792
  | 8 => 914
  | 9 => 914
  | 10 => 914
  | 11 => 914
  | 12 => 1364
  | 13 => 1381
  | 14 => 1398
  | 15 => 1415
  | 16 => 1537
  | 17 => 1537
  | 18 => 1537
  | 19 => 1537
  | _ => 1987

def leftReturnIndex : Nat → Nat
  | 0 => 741
  | 1 => 741
  | 2 => 741
  | 3 => 741
  | 4 => 757
  | 5 => 774
  | 6 => 791
  | 7 => 913
  | 8 => 1364
  | 9 => 1364
  | 10 => 1364
  | 11 => 1364
  | 12 => 1380
  | 13 => 1397
  | 14 => 1414
  | 15 => 1536
  | 16 => 1987
  | 17 => 1987
  | 18 => 1987
  | 19 => 1987
  | _ => 1987

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 341
  | 1 => 806
  | 2 => 914
  | 3 => 1429
  | _ => 1537

def leftHelperJumpIndex : Nat → Nat
  | 0 => 740
  | 1 => 912
  | 2 => 1363
  | 3 => 1535
  | _ => 1986

def leftHelperPCNat : Nat → Nat
  | 0 => 724
  | 1 => 1358
  | 2 => 1490
  | 3 => 2179
  | _ => 2311

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1998
  | 1 => 1998
  | 2 => 1998
  | 3 => 1998
  | 4 => 2448
  | 5 => 2448
  | 6 => 2448
  | 7 => 2448
  | 8 => 2914
  | 9 => 2914
  | 10 => 2914
  | 11 => 2914
  | 12 => 3364
  | 13 => 3381
  | 14 => 3398
  | 15 => 3415
  | 16 => 3537
  | 17 => 3537
  | 18 => 3537
  | 19 => 3537
  | _ => 3937

def rightReturnIndex : Nat → Nat
  | 0 => 2448
  | 1 => 2448
  | 2 => 2448
  | 3 => 2448
  | 4 => 2914
  | 5 => 2914
  | 6 => 2914
  | 7 => 2914
  | 8 => 3364
  | 9 => 3364
  | 10 => 3364
  | 11 => 3364
  | 12 => 3380
  | 13 => 3397
  | 14 => 3414
  | 15 => 3536
  | 16 => 3937
  | 17 => 3937
  | 18 => 3937
  | 19 => 3937
  | _ => 3937

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 1998
  | 1 => 2448
  | 2 => 2914
  | 3 => 3429
  | _ => 3537

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2447
  | 1 => 2913
  | 2 => 3363
  | 3 => 3535
  | _ => 3936

def rightHelperPCNat : Nat → Nat
  | 0 => 2829
  | 1 => 3331
  | 2 => 3849
  | 3 => 4538
  | _ => 4686

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1987
theorem route_pc : A.instructionPC routeIndex = 2813 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1988
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2814 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3937
theorem tail_pc : A.instructionPC tailIndex = 5134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3984
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 278
theorem schedule_pc : A.instructionPC scheduleIndex = 508 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3985
theorem output_pc : A.instructionPC outputIndex = 5192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4038
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
