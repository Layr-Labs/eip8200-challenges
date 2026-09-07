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
  | 0 => 907
  | 1 => 907
  | 2 => 907
  | 3 => 907
  | 4 => 1361
  | 5 => 1378
  | 6 => 1395
  | 7 => 1412
  | 8 => 1534
  | 9 => 1534
  | 10 => 1534
  | 11 => 1534
  | 12 => 1537
  | 13 => 1554
  | 14 => 1571
  | 15 => 1588
  | 16 => 1710
  | 17 => 1710
  | 18 => 1710
  | 19 => 1710
  | _ => 2158

def leftReturnIndex : Nat → Nat
  | 0 => 1360
  | 1 => 1360
  | 2 => 1360
  | 3 => 1360
  | 4 => 1377
  | 5 => 1394
  | 6 => 1411
  | 7 => 1533
  | 8 => 1536
  | 9 => 1536
  | 10 => 1536
  | 11 => 1536
  | 12 => 1553
  | 13 => 1570
  | 14 => 1587
  | 15 => 1709
  | 16 => 2158
  | 17 => 2158
  | 18 => 2158
  | 19 => 2158
  | _ => 2158

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 2
  | 1 => 1426
  | 2 => 909
  | 3 => 1602
  | _ => 1710

def leftHelperJumpIndex : Nat → Nat
  | 0 => 402
  | 1 => 1532
  | 2 => 1357
  | 3 => 1708
  | _ => 2157

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1833
  | 2 => 1081
  | 3 => 2157
  | _ => 2289

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2169
  | 1 => 2281
  | 2 => 2393
  | 3 => 2505
  | 4 => 2617
  | 5 => 2733
  | 6 => 2849
  | 7 => 2965
  | 8 => 3081
  | 9 => 3098
  | 10 => 3115
  | 11 => 3132
  | 12 => 3250
  | 13 => 3267
  | 14 => 3284
  | 15 => 3301
  | 16 => 3423
  | 17 => 3423
  | 18 => 3423
  | 19 => 3423
  | _ => 3426

def rightReturnIndex : Nat → Nat
  | 0 => 2281
  | 1 => 2393
  | 2 => 2505
  | 3 => 2617
  | 4 => 2733
  | 5 => 2849
  | 6 => 2965
  | 7 => 3081
  | 8 => 3097
  | 9 => 3114
  | 10 => 3131
  | 11 => 3249
  | 12 => 3266
  | 13 => 3283
  | 14 => 3300
  | 15 => 3422
  | 16 => 3425
  | 17 => 3425
  | 18 => 3425
  | 19 => 3425
  | _ => 3426

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2515
  | 1 => 3146
  | 2 => 3146
  | 3 => 3315
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2616
  | 1 => 3248
  | 2 => 3248
  | 3 => 3421
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3296
  | 1 => 4186
  | 2 => 4186
  | 3 => 4517
  | _ => 519

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2158
theorem route_pc : A.instructionPC routeIndex = 0xb21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2159
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3426
theorem tail_pc : A.instructionPC tailIndex = 0x123e := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3473
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4727 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 3474
theorem schedule_pc : A.instructionPC scheduleIndex = 4728 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3525
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4918 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3526
theorem output_pc : A.instructionPC outputIndex = 4919 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3579
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4994 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
