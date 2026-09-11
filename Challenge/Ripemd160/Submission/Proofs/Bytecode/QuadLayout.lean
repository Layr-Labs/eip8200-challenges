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
  | 0 => 335
  | 1 => 335
  | 2 => 335
  | 3 => 335
  | 4 => 735
  | 5 => 752
  | 6 => 769
  | 7 => 786
  | 8 => 908
  | 9 => 908
  | 10 => 908
  | 11 => 908
  | 12 => 1356
  | 13 => 1373
  | 14 => 1390
  | 15 => 1407
  | 16 => 1529
  | 17 => 1529
  | 18 => 1529
  | 19 => 1529
  | _ => 1977

def leftReturnIndex : Nat → Nat
  | 0 => 735
  | 1 => 735
  | 2 => 735
  | 3 => 735
  | 4 => 751
  | 5 => 768
  | 6 => 785
  | 7 => 907
  | 8 => 1356
  | 9 => 1356
  | 10 => 1356
  | 11 => 1356
  | 12 => 1372
  | 13 => 1389
  | 14 => 1406
  | 15 => 1528
  | 16 => 1977
  | 17 => 1977
  | 18 => 1977
  | 19 => 1977
  | _ => 1977

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 335
  | 1 => 800
  | 2 => 908
  | 3 => 1421
  | _ => 1529

def leftHelperJumpIndex : Nat → Nat
  | 0 => 734
  | 1 => 906
  | 2 => 1355
  | 3 => 1527
  | _ => 1976

def leftHelperPCNat : Nat → Nat
  | 0 => 680
  | 1 => 1314
  | 2 => 1446
  | 3 => 2193
  | _ => 2325

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1988
  | 1 => 2096
  | 2 => 2208
  | 3 => 2320
  | 4 => 2432
  | 5 => 2548
  | 6 => 2565
  | 7 => 2582
  | 8 => 2704
  | 9 => 2816
  | 10 => 2928
  | 11 => 3040
  | 12 => 3152
  | 13 => 3169
  | 14 => 3186
  | 15 => 3203
  | 16 => 3325
  | 17 => 3325
  | 18 => 3325
  | 19 => 3325
  | _ => 3725

def rightReturnIndex : Nat → Nat
  | 0 => 2096
  | 1 => 2208
  | 2 => 2320
  | 3 => 2432
  | 4 => 2548
  | 5 => 2564
  | 6 => 2581
  | 7 => 2703
  | 8 => 2816
  | 9 => 2928
  | 10 => 3040
  | 11 => 3152
  | 12 => 3168
  | 13 => 3185
  | 14 => 3202
  | 15 => 3324
  | 16 => 3725
  | 17 => 3725
  | 18 => 3725
  | 19 => 3725
  | _ => 3725

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
  | 1 => 2596
  | 2 => 2876
  | 3 => 3217
  | _ => 3325

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2431
  | 1 => 2702
  | 2 => 3146
  | 3 => 3323
  | _ => 3724

def rightHelperPCNat : Nat → Nat
  | 0 => 3338
  | 1 => 3749
  | 2 => 4112
  | 3 => 4644
  | _ => 4792

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1977
theorem route_pc : A.instructionPC routeIndex = 0xb4b := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1978
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb4c := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3725
theorem tail_pc : A.instructionPC tailIndex = 0x1478 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3772
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5297 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 272
theorem schedule_pc : A.instructionPC scheduleIndex = 464 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 323
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 654 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3773
theorem output_pc : A.instructionPC outputIndex = 5298 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3826
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5373 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
