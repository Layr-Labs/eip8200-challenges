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
  | 0 => 341
  | 1 => 341
  | 2 => 341
  | 3 => 341
  | 4 => 741
  | 5 => 758
  | 6 => 775
  | 7 => 792
  | 8 => 914
  | 9 => 914
  | 10 => 914
  | 11 => 914
  | 12 => 1362
  | 13 => 1379
  | 14 => 1396
  | 15 => 1413
  | 16 => 1535
  | 17 => 1535
  | 18 => 1535
  | 19 => 1535
  | _ => 1983

def leftReturnIndex : Nat → Nat
  | 0 => 741
  | 1 => 741
  | 2 => 741
  | 3 => 741
  | 4 => 757
  | 5 => 774
  | 6 => 791
  | 7 => 913
  | 8 => 1362
  | 9 => 1362
  | 10 => 1362
  | 11 => 1362
  | 12 => 1378
  | 13 => 1395
  | 14 => 1412
  | 15 => 1534
  | 16 => 1983
  | 17 => 1983
  | 18 => 1983
  | 19 => 1983
  | _ => 1983

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 341
  | 1 => 806
  | 2 => 914
  | 3 => 1427
  | _ => 1535

def leftHelperJumpIndex : Nat → Nat
  | 0 => 740
  | 1 => 912
  | 2 => 1361
  | 3 => 1533
  | _ => 1982

def leftHelperPCNat : Nat → Nat
  | 0 => 724
  | 1 => 1358
  | 2 => 1490
  | 3 => 2237
  | _ => 2369

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1994
  | 1 => 2106
  | 2 => 2218
  | 3 => 2330
  | 4 => 2442
  | 5 => 2558
  | 6 => 2674
  | 7 => 2790
  | 8 => 2906
  | 9 => 2923
  | 10 => 2940
  | 11 => 2957
  | 12 => 3075
  | 13 => 3092
  | 14 => 3109
  | 15 => 3126
  | 16 => 3248
  | 17 => 3248
  | 18 => 3248
  | 19 => 3248
  | _ => 3648

def rightReturnIndex : Nat → Nat
  | 0 => 2106
  | 1 => 2218
  | 2 => 2330
  | 3 => 2442
  | 4 => 2558
  | 5 => 2674
  | 6 => 2790
  | 7 => 2906
  | 8 => 2922
  | 9 => 2939
  | 10 => 2956
  | 11 => 3074
  | 12 => 3091
  | 13 => 3108
  | 14 => 3125
  | 15 => 3247
  | 16 => 3648
  | 17 => 3648
  | 18 => 3648
  | 19 => 3648
  | _ => 3648

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2340
  | 1 => 2971
  | 2 => 2971
  | 3 => 3140
  | _ => 3248

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2441
  | 1 => 3073
  | 2 => 3073
  | 3 => 3246
  | _ => 3647

def rightHelperPCNat : Nat → Nat
  | 0 => 3376
  | 1 => 4266
  | 2 => 4266
  | 3 => 4597
  | _ => 4745

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1983
theorem route_pc : A.instructionPC routeIndex = 0xb71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1984
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3648
theorem tail_pc : A.instructionPC tailIndex = 0x1449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3695
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 278
theorem schedule_pc : A.instructionPC scheduleIndex = 508 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3696
theorem output_pc : A.instructionPC outputIndex = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3749
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
