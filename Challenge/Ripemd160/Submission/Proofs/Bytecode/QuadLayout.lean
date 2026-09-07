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
  | 0 => 331
  | 1 => 331
  | 2 => 331
  | 3 => 331
  | 4 => 731
  | 5 => 748
  | 6 => 765
  | 7 => 782
  | 8 => 904
  | 9 => 904
  | 10 => 904
  | 11 => 904
  | 12 => 1352
  | 13 => 1369
  | 14 => 1386
  | 15 => 1403
  | 16 => 1525
  | 17 => 1525
  | 18 => 1525
  | 19 => 1525
  | _ => 1973

def leftReturnIndex : Nat → Nat
  | 0 => 731
  | 1 => 731
  | 2 => 731
  | 3 => 731
  | 4 => 747
  | 5 => 764
  | 6 => 781
  | 7 => 903
  | 8 => 1352
  | 9 => 1352
  | 10 => 1352
  | 11 => 1352
  | 12 => 1368
  | 13 => 1385
  | 14 => 1402
  | 15 => 1524
  | 16 => 1973
  | 17 => 1973
  | 18 => 1973
  | 19 => 1973
  | _ => 1973

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 331
  | 1 => 796
  | 2 => 904
  | 3 => 1417
  | _ => 1525

def leftHelperJumpIndex : Nat → Nat
  | 0 => 730
  | 1 => 902
  | 2 => 1351
  | 3 => 1523
  | _ => 1972

def leftHelperPCNat : Nat → Nat
  | 0 => 709
  | 1 => 1343
  | 2 => 1475
  | 3 => 2222
  | _ => 2354

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1984
  | 1 => 2096
  | 2 => 2208
  | 3 => 2320
  | 4 => 2432
  | 5 => 2548
  | 6 => 2664
  | 7 => 2780
  | 8 => 2896
  | 9 => 2913
  | 10 => 2930
  | 11 => 2947
  | 12 => 3065
  | 13 => 3082
  | 14 => 3099
  | 15 => 3116
  | 16 => 3238
  | 17 => 3238
  | 18 => 3238
  | 19 => 3238
  | _ => 3638

def rightReturnIndex : Nat → Nat
  | 0 => 2096
  | 1 => 2208
  | 2 => 2320
  | 3 => 2432
  | 4 => 2548
  | 5 => 2664
  | 6 => 2780
  | 7 => 2896
  | 8 => 2912
  | 9 => 2929
  | 10 => 2946
  | 11 => 3064
  | 12 => 3081
  | 13 => 3098
  | 14 => 3115
  | 15 => 3237
  | 16 => 3638
  | 17 => 3638
  | 18 => 3638
  | 19 => 3638
  | _ => 3638

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2330
  | 1 => 2961
  | 2 => 2961
  | 3 => 3130
  | _ => 3238

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2431
  | 1 => 3063
  | 2 => 3063
  | 3 => 3236
  | _ => 3637

def rightHelperPCNat : Nat → Nat
  | 0 => 3361
  | 1 => 4251
  | 2 => 4251
  | 3 => 4582
  | _ => 4730

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1973
theorem route_pc : A.instructionPC routeIndex = 0xb62 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1974
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3638
theorem tail_pc : A.instructionPC tailIndex = 0x143a := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3685
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 268
theorem schedule_pc : A.instructionPC scheduleIndex = 493 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3686
theorem output_pc : A.instructionPC outputIndex = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3739
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
