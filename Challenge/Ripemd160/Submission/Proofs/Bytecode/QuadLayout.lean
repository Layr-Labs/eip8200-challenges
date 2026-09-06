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

def leftWrapperIndex (k : Nat) : Nat := if k = 0 then 931 else 932 + 12 * k
def leftPC (k : Nat) : UInt256 :=
  UInt256.ofNat (1337 + 28 * k)
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 10))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (1364 + 28 * k)

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = 1337 + 28 * k.val := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 1486
  | 1 => 1595
  | 2 => 1720
  | 3 => 1841
  | _ => 1966

def leftHelperJumpIndex : Nat → Nat
  | 0 => 1594
  | 1 => 1719
  | 2 => 1840
  | 3 => 1965
  | _ => 2086

def leftHelperPCNat : Nat → Nat
  | 0 => 2565
  | 1 => 2710
  | 2 => 2887
  | 3 => 3060
  | _ => 3237

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex (k : Nat) : Nat := if k = 0 then 1183 else 1184 + 12 * k
def rightPC (k : Nat) : UInt256 :=
  UInt256.ofNat (1913 + 28 * k)
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (1940 + 28 * k)

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = 1913 + 28 * k.val := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2087
  | 1 => 2208
  | 2 => 2333
  | 3 => 2454
  | _ => 2579

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2207
  | 1 => 2332
  | 2 => 2453
  | 3 => 2578
  | _ => 2687

def rightHelperPCNat : Nat → Nat
  | 0 => 3410
  | 1 => 3583
  | 2 => 3760
  | 3 => 3933
  | _ => 4110

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1172
theorem route_pc : A.instructionPC routeIndex = 1897 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1173
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 1898 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 1424
theorem tail_pc : A.instructionPC tailIndex = 2473 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 1477
theorem tailJump_pc : A.instructionPC tailJumpIndex = 2556 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2688
theorem schedule_pc : A.instructionPC scheduleIndex = 4255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2743
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4579 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2744
theorem output_pc : A.instructionPC outputIndex = 4580 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2793
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4765 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
