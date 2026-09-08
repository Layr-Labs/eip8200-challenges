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
  | 0 => 352
  | 1 => 352
  | 2 => 352
  | 3 => 352
  | 4 => 749
  | 5 => 766
  | 6 => 783
  | 7 => 800
  | 8 => 922
  | 9 => 922
  | 10 => 922
  | 11 => 922
  | 12 => 1369
  | 13 => 1386
  | 14 => 1403
  | 15 => 1420
  | 16 => 1542
  | 17 => 1542
  | 18 => 1542
  | 19 => 1542
  | _ => 1989

def leftReturnIndex : Nat → Nat
  | 0 => 749
  | 1 => 749
  | 2 => 749
  | 3 => 749
  | 4 => 765
  | 5 => 782
  | 6 => 799
  | 7 => 921
  | 8 => 1369
  | 9 => 1369
  | 10 => 1369
  | 11 => 1369
  | 12 => 1385
  | 13 => 1402
  | 14 => 1419
  | 15 => 1541
  | 16 => 1989
  | 17 => 1989
  | 18 => 1989
  | 19 => 1989
  | _ => 1989

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 352
  | 1 => 814
  | 2 => 922
  | 3 => 1434
  | _ => 1542

def leftHelperJumpIndex : Nat → Nat
  | 0 => 748
  | 1 => 920
  | 2 => 1368
  | 3 => 1540
  | _ => 1988

def leftHelperPCNat : Nat → Nat
  | 0 => 739
  | 1 => 1367
  | 2 => 1499
  | 3 => 2182
  | _ => 2314

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2000
  | 1 => 2000
  | 2 => 2000
  | 3 => 2000
  | 4 => 2447
  | 5 => 2447
  | 6 => 2447
  | 7 => 2447
  | 8 => 2910
  | 9 => 2910
  | 10 => 2910
  | 11 => 2910
  | 12 => 3357
  | 13 => 3374
  | 14 => 3391
  | 15 => 3408
  | 16 => 3530
  | 17 => 3530
  | 18 => 3530
  | 19 => 3530
  | _ => 3927

def rightReturnIndex : Nat → Nat
  | 0 => 2447
  | 1 => 2447
  | 2 => 2447
  | 3 => 2447
  | 4 => 2910
  | 5 => 2910
  | 6 => 2910
  | 7 => 2910
  | 8 => 3357
  | 9 => 3357
  | 10 => 3357
  | 11 => 3357
  | 12 => 3373
  | 13 => 3390
  | 14 => 3407
  | 15 => 3529
  | 16 => 3927
  | 17 => 3927
  | 18 => 3927
  | 19 => 3927
  | _ => 3927

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2000
  | 1 => 2447
  | 2 => 2910
  | 3 => 3422
  | _ => 3530

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2446
  | 1 => 2909
  | 2 => 3356
  | 3 => 3528
  | _ => 3926

def rightHelperPCNat : Nat → Nat
  | 0 => 2826
  | 1 => 3322
  | 2 => 3834
  | 3 => 4517
  | _ => 4665

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1989
theorem route_pc : A.instructionPC routeIndex = 2810 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1990
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2811 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3927
theorem tail_pc : A.instructionPC tailIndex = 5107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3977
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 283
theorem schedule_pc : A.instructionPC scheduleIndex = 514 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3978
theorem output_pc : A.instructionPC outputIndex = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4031
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
