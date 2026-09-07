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
  | 0 => 340
  | 1 => 340
  | 2 => 340
  | 3 => 340
  | 4 => 740
  | 5 => 757
  | 6 => 774
  | 7 => 791
  | 8 => 913
  | 9 => 913
  | 10 => 913
  | 11 => 913
  | 12 => 1361
  | 13 => 1378
  | 14 => 1395
  | 15 => 1412
  | 16 => 1534
  | 17 => 1534
  | 18 => 1534
  | 19 => 1534
  | _ => 1982

def leftReturnIndex : Nat → Nat
  | 0 => 740
  | 1 => 740
  | 2 => 740
  | 3 => 740
  | 4 => 756
  | 5 => 773
  | 6 => 790
  | 7 => 912
  | 8 => 1361
  | 9 => 1361
  | 10 => 1361
  | 11 => 1361
  | 12 => 1377
  | 13 => 1394
  | 14 => 1411
  | 15 => 1533
  | 16 => 1982
  | 17 => 1982
  | 18 => 1982
  | 19 => 1982
  | _ => 1982

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 340
  | 1 => 805
  | 2 => 913
  | 3 => 1426
  | _ => 1534

def leftHelperJumpIndex : Nat → Nat
  | 0 => 739
  | 1 => 911
  | 2 => 1360
  | 3 => 1532
  | _ => 1981

def leftHelperPCNat : Nat → Nat
  | 0 => 697
  | 1 => 1347
  | 2 => 1479
  | 3 => 2242
  | _ => 2374

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1993
  | 1 => 2105
  | 2 => 2217
  | 3 => 2329
  | 4 => 2441
  | 5 => 2557
  | 6 => 2574
  | 7 => 2591
  | 8 => 2713
  | 9 => 2730
  | 10 => 2747
  | 11 => 2764
  | 12 => 2882
  | 13 => 2899
  | 14 => 2916
  | 15 => 2933
  | 16 => 3055
  | 17 => 3055
  | 18 => 3055
  | 19 => 3055
  | _ => 3455

def rightReturnIndex : Nat → Nat
  | 0 => 2105
  | 1 => 2217
  | 2 => 2329
  | 3 => 2441
  | 4 => 2557
  | 5 => 2573
  | 6 => 2590
  | 7 => 2712
  | 8 => 2729
  | 9 => 2746
  | 10 => 2763
  | 11 => 2881
  | 12 => 2898
  | 13 => 2915
  | 14 => 2932
  | 15 => 3054
  | 16 => 3455
  | 17 => 3455
  | 18 => 3455
  | 19 => 3455
  | _ => 3455

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2339
  | 1 => 2605
  | 2 => 2778
  | 3 => 2947
  | _ => 3055

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2440
  | 1 => 2711
  | 2 => 2880
  | 3 => 3053
  | _ => 3454

def rightHelperPCNat : Nat → Nat
  | 0 => 3410
  | 1 => 3828
  | 2 => 4161
  | 3 => 4492
  | _ => 4640

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1982
theorem route_pc : A.instructionPC routeIndex = 0xb86 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1983
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb87 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3455
theorem tail_pc : A.instructionPC tailIndex = 0x13f0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3502
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 275
theorem schedule_pc : A.instructionPC scheduleIndex = 477 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 326
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 669 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3503
theorem output_pc : A.instructionPC outputIndex = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3556
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
