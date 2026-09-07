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

def leftWrapperIndex (k : Nat) : Nat := 932 + 12 * k
def leftPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 10))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 11))

def leftWrapperPCNat : Nat → Nat
  | 0 => 0x53e
  | 1 => 0x56e
  | 2 => 0x59c
  | 3 => 0x5cc
  | 4 => 0x5fa
  | 5 => 0x628
  | 6 => 0x657
  | 7 => 0x686
  | 8 => 0x6b5
  | 9 => 0x6e3
  | 10 => 0x713
  | 11 => 0x742
  | 12 => 0x76f
  | 13 => 0x79f
  | 14 => 0x7cf
  | 15 => 0x7fd
  | 16 => 0x82b
  | 17 => 0x85a
  | 18 => 0x889
  | 19 => 0x8b8
  | _ => 0x8e6

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = leftWrapperPCNat k.val := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 1491
  | 1 => 1596
  | 2 => 1717
  | 3 => 1834
  | _ => 1955

def leftHelperJumpIndex : Nat → Nat
  | 0 => 1592
  | 1 => 1713
  | 2 => 1830
  | 3 => 1951
  | _ => 2068

def leftHelperPCNat : Nat → Nat
  | 0 => 0xb88
  | 1 => 0xbf9
  | 2 => 0xc8a
  | 3 => 0xd17
  | _ => 0xda8

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex (k : Nat) : Nat := 1188 + 12 * k
def rightPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))

def rightWrapperPCNat : Nat → Nat
  | 0 => 0x8fb
  | 1 => 0x92b
  | 2 => 0x95a
  | 3 => 0x988
  | 4 => 0x9b7
  | 5 => 0x9e6
  | 6 => 0xa16
  | 7 => 0xa43
  | 8 => 0xa72
  | 9 => 0xaa1
  | 10 => 0xacf
  | 11 => 0xafe
  | 12 => 0xb2c
  | 13 => 0xb5b
  | 14 => 0xb8a
  | 15 => 0xbb9
  | 16 => 0xbe8
  | 17 => 0xc17
  | 18 => 0xc45
  | 19 => 0xc73
  | _ => 0xca3

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = rightWrapperPCNat k.val := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2072
  | 1 => 2189
  | 2 => 2310
  | 3 => 2427
  | _ => 2548

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2185
  | 1 => 2306
  | 2 => 2423
  | 3 => 2544
  | _ => 2649

def rightHelperPCNat : Nat → Nat
  | 0 => 0xfad
  | 1 => 0x103a
  | 2 => 0x10cb
  | 3 => 0x1158
  | _ => 0x11e9

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1172
theorem route_pc : A.instructionPC routeIndex = 0x8e6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1178
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0x8ec := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 1428
theorem tail_pc : A.instructionPC tailIndex = 0xca3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 1481
theorem tailJump_pc : A.instructionPC tailJumpIndex = 0xcf6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2653
theorem schedule_pc : A.instructionPC scheduleIndex = 0x125a := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2708
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 0x139e := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2709
theorem output_pc : A.instructionPC outputIndex = 0x139f := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2758
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 0x1458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
