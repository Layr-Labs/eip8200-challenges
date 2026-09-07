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
  | 0 => 907
  | 1 => 907
  | 2 => 907
  | 3 => 907
  | 4 => 1361
  | 5 => 1378
  | 6 => 1395
  | 7 => 1412
  | 8 => 1534
  | 9 => 1534
  | 10 => 1534
  | 11 => 1534
  | 12 => 1537
  | 13 => 1554
  | 14 => 1571
  | 15 => 1588
  | 16 => 1710
  | 17 => 1710
  | 18 => 1710
  | 19 => 1710
  | _ => 2161

def leftReturnIndex : Nat → Nat
  | 0 => 1360
  | 1 => 1360
  | 2 => 1360
  | 3 => 1360
  | 4 => 1377
  | 5 => 1394
  | 6 => 1411
  | 7 => 1533
  | 8 => 1536
  | 9 => 1536
  | 10 => 1536
  | 11 => 1536
  | 12 => 1553
  | 13 => 1570
  | 14 => 1587
  | 15 => 1709
  | 16 => 2160
  | 17 => 2160
  | 18 => 2160
  | 19 => 2160
  | _ => 2161

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 2
  | 1 => 1426
  | 2 => 909
  | 3 => 1602
  | _ => 1710

def leftHelperJumpIndex : Nat → Nat
  | 0 => 402
  | 1 => 1532
  | 2 => 1357
  | 3 => 1708
  | _ => 2157

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1833
  | 2 => 1081
  | 3 => 2157
  | _ => 2289

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2172
  | 1 => 2285
  | 2 => 2398
  | 3 => 2511
  | 4 => 2624
  | 5 => 2641
  | 6 => 2658
  | 7 => 2675
  | 8 => 2797
  | 9 => 2814
  | 10 => 2831
  | 11 => 2848
  | 12 => 2966
  | 13 => 2983
  | 14 => 3000
  | 15 => 3017
  | 16 => 3139
  | 17 => 3139
  | 18 => 3139
  | 19 => 3139
  | _ => 3142

def rightReturnIndex : Nat → Nat
  | 0 => 2284
  | 1 => 2397
  | 2 => 2510
  | 3 => 2623
  | 4 => 2640
  | 5 => 2657
  | 6 => 2674
  | 7 => 2796
  | 8 => 2813
  | 9 => 2830
  | 10 => 2847
  | 11 => 2965
  | 12 => 2982
  | 13 => 2999
  | 14 => 3016
  | 15 => 3138
  | 16 => 3141
  | 17 => 3141
  | 18 => 3141
  | 19 => 3141
  | _ => 3142

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2521
  | 1 => 2689
  | 2 => 2862
  | 3 => 3031
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2622
  | 1 => 2795
  | 2 => 2964
  | 3 => 3137
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3304
  | 1 => 3620
  | 2 => 3953
  | 3 => 4284
  | _ => 519

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2161
theorem route_pc : A.instructionPC routeIndex = 0xb26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2162
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb27 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3142
theorem tail_pc : A.instructionPC tailIndex = 0x1155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3189
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4494 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 3190
theorem schedule_pc : A.instructionPC scheduleIndex = 4495 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3241
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4693 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3242
theorem output_pc : A.instructionPC outputIndex = 4694 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3289
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4822 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
