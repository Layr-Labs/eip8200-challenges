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
  | 1 => 2100
  | 2 => 2212
  | 3 => 2324
  | 4 => 2436
  | 5 => 2552
  | 6 => 2569
  | 7 => 2586
  | 8 => 2708
  | 9 => 2820
  | 10 => 2932
  | 11 => 3044
  | 12 => 3156
  | 13 => 3173
  | 14 => 3190
  | 15 => 3207
  | 16 => 3329
  | 17 => 3329
  | 18 => 3329
  | 19 => 3329
  | _ => 3729

def rightReturnIndex : Nat → Nat
  | 0 => 2100
  | 1 => 2212
  | 2 => 2324
  | 3 => 2436
  | 4 => 2552
  | 5 => 2568
  | 6 => 2585
  | 7 => 2707
  | 8 => 2820
  | 9 => 2932
  | 10 => 3044
  | 11 => 3156
  | 12 => 3172
  | 13 => 3189
  | 14 => 3206
  | 15 => 3328
  | 16 => 3729
  | 17 => 3729
  | 18 => 3729
  | 19 => 3729
  | _ => 3729

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2334
  | 1 => 2600
  | 2 => 2880
  | 3 => 3221
  | _ => 3329

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2435
  | 1 => 2706
  | 2 => 3150
  | 3 => 3327
  | _ => 3728

def rightHelperPCNat : Nat → Nat
  | 0 => 3332
  | 1 => 3743
  | 2 => 4106
  | 3 => 4638
  | _ => 4786

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1977
theorem route_pc : A.instructionPC routeIndex = 0xb45 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1978
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb46 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3729
theorem tail_pc : A.instructionPC tailIndex = 0x1472 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3776
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5291 := by
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

def outputIndex : Nat := 3777
theorem output_pc : A.instructionPC outputIndex = 5292 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3830
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 0x1512 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
