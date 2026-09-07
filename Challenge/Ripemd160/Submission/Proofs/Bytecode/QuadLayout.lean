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
  | 1 => 1892
  | 2 => 1124
  | 3 => 2216
  | _ => 2348

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
  | 3 => 2415
  | 4 => 2533
  | 5 => 2550
  | 6 => 2567
  | 7 => 2584
  | 8 => 2706
  | 9 => 2723
  | 10 => 2740
  | 11 => 2757
  | 12 => 2875
  | 13 => 2892
  | 14 => 2909
  | 15 => 2926
  | 16 => 3048
  | 17 => 3048
  | 18 => 3048
  | 19 => 3048
  | _ => 3051

def rightReturnIndex : Nat → Nat
  | 0 => 2284
  | 1 => 2397
  | 2 => 2414
  | 3 => 2532
  | 4 => 2549
  | 5 => 2566
  | 6 => 2583
  | 7 => 2705
  | 8 => 2722
  | 9 => 2739
  | 10 => 2756
  | 11 => 2874
  | 12 => 2891
  | 13 => 2908
  | 14 => 2925
  | 15 => 3047
  | 16 => 3050
  | 17 => 3050
  | 18 => 3050
  | 19 => 3050
  | _ => 3051

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2429
  | 1 => 2598
  | 2 => 2771
  | 3 => 2940
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2531
  | 1 => 2704
  | 2 => 2873
  | 3 => 3046
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3325
  | 1 => 3655
  | 2 => 3988
  | 3 => 4319
  | _ => 542

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2161
theorem route_pc : A.instructionPC routeIndex = 0xb71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2162
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3051
theorem tail_pc : A.instructionPC tailIndex = 0x1178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3098
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4529 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 3099
theorem schedule_pc : A.instructionPC scheduleIndex = 4530 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3150
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4728 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3151
theorem output_pc : A.instructionPC outputIndex = 4729 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3200
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4914 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
