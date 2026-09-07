import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-! Exact location data for the frozen combined H30b+H31b artifact. -/
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

def leftWrapperIndex (k : Nat) : Nat := 671 + 12 * k
def leftPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 10))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 11))

def leftWrapperPCNat : Nat → Nat
  | 0 => 0x3d9
  | 1 => 0x409
  | 2 => 0x437
  | 3 => 0x467
  | 4 => 0x495
  | 5 => 0x4c3
  | 6 => 0x4f2
  | 7 => 0x521
  | 8 => 0x550
  | 9 => 0x57e
  | 10 => 0x5ae
  | 11 => 0x5dd
  | 12 => 0x60a
  | 13 => 0x63a
  | 14 => 0x66a
  | 15 => 0x698
  | 16 => 0x6c6
  | 17 => 0x6f5
  | 18 => 0x724
  | 19 => 0x753
  | _ => 0x781

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = leftWrapperPCNat k.val := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 1230
  | 1 => 1332
  | 2 => 1450
  | 3 => 1564
  | _ => 1682

def leftHelperJumpIndex : Nat → Nat
  | 0 => 1331
  | 1 => 1449
  | 2 => 1563
  | 3 => 1681
  | _ => 1795

def leftHelperPCNat : Nat → Nat
  | 0 => 0xb9b
  | 1 => 0xc09
  | 2 => 0xc97
  | 3 => 0xd21
  | _ => 0xdaf

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex (k : Nat) : Nat := 927 + 12 * k
def rightPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))

def rightWrapperPCNat : Nat → Nat
  | 0 => 0x796
  | 1 => 0x7c6
  | 2 => 0x7f5
  | 3 => 0x823
  | 4 => 0x852
  | 5 => 0x881
  | 6 => 0x8b1
  | 7 => 0x8de
  | 8 => 0x90d
  | 9 => 0x93c
  | 10 => 0x96a
  | 11 => 0x999
  | 12 => 0x9c7
  | 13 => 0x9f6
  | 14 => 0xa25
  | 15 => 0xa54
  | 16 => 0xa83
  | 17 => 0xab2
  | 18 => 0xae0
  | 19 => 0xb0e
  | _ => 0xb3e

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = rightWrapperPCNat k.val := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 1796
  | 1 => 1910
  | 2 => 2030
  | 3 => 2147
  | _ => 2268

def rightHelperJumpIndex : Nat → Nat
  | 0 => 1909
  | 1 => 2027
  | 2 => 2143
  | 3 => 2264
  | _ => 2369

def rightHelperPCNat : Nat → Nat
  | 0 => 0xe39
  | 1 => 0xec3
  | 2 => 0xf53
  | 3 => 0xfe0
  | _ => 0x1071

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 911
theorem route_pc : A.instructionPC routeIndex = 0x781 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 917
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0x787 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 1167
theorem tail_pc : A.instructionPC tailIndex = 0xb3e := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 1220
theorem tailJump_pc : A.instructionPC tailJumpIndex = 0xb91 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2373
theorem schedule_pc : A.instructionPC scheduleIndex = 0x10e2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2428
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 0x1226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2429
theorem output_pc : A.instructionPC outputIndex = 0x1227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2478
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 0x12e0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
