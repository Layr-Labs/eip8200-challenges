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
  | 5 => 1079
  | 6 => 1091
  | 7 => 1103
  | 8 => 1229
  | 9 => 1229
  | 10 => 1229
  | 11 => 1229
  | 12 => 1445
  | 13 => 1457
  | 14 => 1469
  | 15 => 1481
  | 16 => 1607
  | 17 => 1607
  | 18 => 1607
  | 19 => 1607
  | _ => 1823

def leftReturnIndex : Nat → Nat
  | 0 => 1066
  | 1 => 1066
  | 2 => 1066
  | 3 => 1066
  | 4 => 1078
  | 5 => 1090
  | 6 => 1102
  | 7 => 1228
  | 8 => 1444
  | 9 => 1444
  | 10 => 1444
  | 11 => 1444
  | 12 => 1456
  | 13 => 1468
  | 14 => 1480
  | 15 => 1606
  | 16 => 1822
  | 17 => 1822
  | 18 => 1822
  | 19 => 1822
  | _ => 1823

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 10))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 2
  | 1 => 1112
  | 2 => 885
  | 3 => 1490
  | _ => 1607

def leftHelperJumpIndex : Nat → Nat
  | 0 => 403
  | 1 => 1227
  | 2 => 1065
  | 3 => 1605
  | _ => 1821

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1514
  | 2 => 1098
  | 3 => 2119
  | _ => 2260

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1834
  | 1 => 1846
  | 2 => 1858
  | 3 => 1870
  | 4 => 1992
  | 5 => 2004
  | 6 => 2016
  | 7 => 2028
  | 8 => 2154
  | 9 => 2166
  | 10 => 2178
  | 11 => 2190
  | 12 => 2312
  | 13 => 2324
  | 14 => 2336
  | 15 => 2348
  | 16 => 2474
  | 17 => 2474
  | 18 => 2474
  | 19 => 2474
  | _ => 2670

def rightReturnIndex : Nat → Nat
  | 0 => 1845
  | 1 => 1857
  | 2 => 1869
  | 3 => 1991
  | 4 => 2003
  | 5 => 2015
  | 6 => 2027
  | 7 => 2153
  | 8 => 2165
  | 9 => 2177
  | 10 => 2189
  | 11 => 2311
  | 12 => 2323
  | 13 => 2335
  | 14 => 2347
  | 15 => 2473
  | 16 => 2669
  | 17 => 2669
  | 18 => 2669
  | 19 => 2669
  | _ => 2670

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 1879
  | 1 => 2037
  | 2 => 2199
  | 3 => 2357
  | _ => 450

def rightHelperJumpIndex : Nat → Nat
  | 0 => 1990
  | 1 => 2152
  | 2 => 2310
  | 3 => 2472
  | _ => 825

def rightHelperPCNat : Nat → Nat
  | 0 => 2740
  | 1 => 3075
  | 2 => 3413
  | 3 => 3749
  | _ => 541

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1823
theorem route_pc : A.instructionPC routeIndex = 0x9ed := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1824
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0x9ee := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2670
theorem tail_pc : A.instructionPC tailIndex = 0x103e := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2717
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2775
theorem schedule_pc : A.instructionPC scheduleIndex = 4289 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2826
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4487 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2914
theorem output_pc : A.instructionPC outputIndex = 4601 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2963
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4786 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
