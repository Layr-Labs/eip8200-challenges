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
  | 0 => 336
  | 1 => 336
  | 2 => 336
  | 3 => 336
  | 4 => 736
  | 5 => 753
  | 6 => 770
  | 7 => 787
  | 8 => 909
  | 9 => 909
  | 10 => 909
  | 11 => 909
  | 12 => 1357
  | 13 => 1374
  | 14 => 1391
  | 15 => 1408
  | 16 => 1530
  | 17 => 1530
  | 18 => 1530
  | 19 => 1530
  | _ => 1978

def leftReturnIndex : Nat → Nat
  | 0 => 736
  | 1 => 736
  | 2 => 736
  | 3 => 736
  | 4 => 752
  | 5 => 769
  | 6 => 786
  | 7 => 908
  | 8 => 1357
  | 9 => 1357
  | 10 => 1357
  | 11 => 1357
  | 12 => 1373
  | 13 => 1390
  | 14 => 1407
  | 15 => 1529
  | 16 => 1978
  | 17 => 1978
  | 18 => 1978
  | 19 => 1978
  | _ => 1978

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 336
  | 1 => 801
  | 2 => 909
  | 3 => 1422
  | _ => 1530

def leftHelperJumpIndex : Nat → Nat
  | 0 => 735
  | 1 => 907
  | 2 => 1356
  | 3 => 1528
  | _ => 1977

def leftHelperPCNat : Nat → Nat
  | 0 => 714
  | 1 => 1348
  | 2 => 1480
  | 3 => 2227
  | _ => 2359

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1989
  | 1 => 2102
  | 2 => 2215
  | 3 => 2232
  | 4 => 2350
  | 5 => 2367
  | 6 => 2384
  | 7 => 2401
  | 8 => 2523
  | 9 => 2523
  | 10 => 2523
  | 11 => 2523
  | 12 => 2971
  | 13 => 2988
  | 14 => 3005
  | 15 => 3022
  | 16 => 3144
  | 17 => 3144
  | 18 => 3144
  | 19 => 3144
  | _ => 3544

def rightReturnIndex : Nat → Nat
  | 0 => 2101
  | 1 => 2214
  | 2 => 2231
  | 3 => 2349
  | 4 => 2366
  | 5 => 2383
  | 6 => 2400
  | 7 => 2522
  | 8 => 2971
  | 9 => 2971
  | 10 => 2971
  | 11 => 2971
  | 12 => 2987
  | 13 => 3004
  | 14 => 3021
  | 15 => 3143
  | 16 => 3544
  | 17 => 3544
  | 18 => 3544
  | 19 => 3544
  | _ => 3544

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2246
  | 1 => 2415
  | 2 => 2523
  | 3 => 3036
  | _ => 3144

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2348
  | 1 => 2521
  | 2 => 2970
  | 3 => 3142
  | _ => 3543

def rightHelperPCNat : Nat → Nat
  | 0 => 3307
  | 1 => 3637
  | 2 => 3785
  | 3 => 4532
  | _ => 4680

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1978
theorem route_pc : A.instructionPC routeIndex = 0xb67 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1979
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb68 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3544
theorem tail_pc : A.instructionPC tailIndex = 0x1408 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3591
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 273
theorem schedule_pc : A.instructionPC scheduleIndex = 498 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3592
theorem output_pc : A.instructionPC outputIndex = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3641
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5371 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
