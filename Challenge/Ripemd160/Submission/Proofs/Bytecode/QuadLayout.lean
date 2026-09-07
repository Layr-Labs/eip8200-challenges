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
  | 0 => 879
  | 1 => 879
  | 2 => 879
  | 3 => 879
  | 4 => 1067
  | 5 => 1080
  | 6 => 1093
  | 7 => 1106
  | 8 => 1231
  | 9 => 1231
  | 10 => 1231
  | 11 => 1231
  | 12 => 1447
  | 13 => 1460
  | 14 => 1473
  | 15 => 1486
  | 16 => 1611
  | 17 => 1611
  | 18 => 1611
  | 19 => 1611
  | _ => 1827

def leftReturnIndex : Nat → Nat
  | 0 => 1066
  | 1 => 1066
  | 2 => 1066
  | 3 => 1066
  | 4 => 1079
  | 5 => 1092
  | 6 => 1105
  | 7 => 1230
  | 8 => 1446
  | 9 => 1446
  | 10 => 1446
  | 11 => 1446
  | 12 => 1459
  | 13 => 1472
  | 14 => 1485
  | 15 => 1610
  | 16 => 1826
  | 17 => 1826
  | 18 => 1826
  | 19 => 1826
  | _ => 1827

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 11))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 2
  | 1 => 1116
  | 2 => 885
  | 3 => 1496
  | _ => 1611

def leftHelperJumpIndex : Nat → Nat
  | 0 => 403
  | 1 => 1229
  | 2 => 1065
  | 3 => 1609
  | _ => 1825

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1518
  | 2 => 1098
  | 3 => 2125
  | _ => 2264

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1838
  | 1 => 1851
  | 2 => 1864
  | 3 => 1877
  | 4 => 1998
  | 5 => 2011
  | 6 => 2024
  | 7 => 2037
  | 8 => 2162
  | 9 => 2175
  | 10 => 2188
  | 11 => 2201
  | 12 => 2322
  | 13 => 2335
  | 14 => 2348
  | 15 => 2361
  | 16 => 2486
  | 17 => 2486
  | 18 => 2486
  | 19 => 2486
  | _ => 2682

def rightReturnIndex : Nat → Nat
  | 0 => 1850
  | 1 => 1863
  | 2 => 1876
  | 3 => 1997
  | 4 => 2010
  | 5 => 2023
  | 6 => 2036
  | 7 => 2161
  | 8 => 2174
  | 9 => 2187
  | 10 => 2200
  | 11 => 2321
  | 12 => 2334
  | 13 => 2347
  | 14 => 2360
  | 15 => 2485
  | 16 => 2681
  | 17 => 2681
  | 18 => 2681
  | 19 => 2681
  | _ => 2682

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 1887
  | 1 => 2047
  | 2 => 2211
  | 3 => 2371
  | _ => 450

def rightHelperJumpIndex : Nat → Nat
  | 0 => 1996
  | 1 => 2160
  | 2 => 2320
  | 3 => 2484
  | _ => 825

def rightHelperPCNat : Nat → Nat
  | 0 => 2748
  | 1 => 3085
  | 2 => 3425
  | 3 => 3763
  | _ => 541

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1827
theorem route_pc : A.instructionPC routeIndex = 0x9f1 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1828
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0x9f2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2682
theorem tail_pc : A.instructionPC tailIndex = 0x104a := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2729
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2787
theorem schedule_pc : A.instructionPC scheduleIndex = 4301 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2838
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4499 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2926
theorem output_pc : A.instructionPC outputIndex = 4613 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2975
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4798 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
