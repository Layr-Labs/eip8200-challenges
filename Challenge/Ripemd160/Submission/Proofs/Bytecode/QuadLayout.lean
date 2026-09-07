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
  | 0 => 906
  | 1 => 906
  | 2 => 906
  | 3 => 906
  | 4 => 1360
  | 5 => 1377
  | 6 => 1394
  | 7 => 1411
  | 8 => 1533
  | 9 => 1533
  | 10 => 1533
  | 11 => 1533
  | 12 => 1536
  | 13 => 1553
  | 14 => 1570
  | 15 => 1587
  | 16 => 1709
  | 17 => 1709
  | 18 => 1709
  | 19 => 1709
  | _ => 2157

def leftReturnIndex : Nat → Nat
  | 0 => 1359
  | 1 => 1359
  | 2 => 1359
  | 3 => 1359
  | 4 => 1376
  | 5 => 1393
  | 6 => 1410
  | 7 => 1532
  | 8 => 1535
  | 9 => 1535
  | 10 => 1535
  | 11 => 1535
  | 12 => 1552
  | 13 => 1569
  | 14 => 1586
  | 15 => 1708
  | 16 => 2157
  | 17 => 2157
  | 18 => 2157
  | 19 => 2157
  | _ => 2157

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
  | 1 => 1425
  | 2 => 908
  | 3 => 1601
  | _ => 1709

def leftHelperJumpIndex : Nat → Nat
  | 0 => 402
  | 1 => 1531
  | 2 => 1356
  | 3 => 1707
  | _ => 2156

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1880
  | 2 => 1112
  | 3 => 2204
  | _ => 2336

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2168
  | 1 => 2280
  | 2 => 2392
  | 3 => 2504
  | 4 => 2616
  | 5 => 2732
  | 6 => 2749
  | 7 => 2766
  | 8 => 2888
  | 9 => 2905
  | 10 => 2922
  | 11 => 2939
  | 12 => 3057
  | 13 => 3074
  | 14 => 3091
  | 15 => 3108
  | 16 => 3230
  | 17 => 3230
  | 18 => 3230
  | 19 => 3230
  | _ => 3233

def rightReturnIndex : Nat → Nat
  | 0 => 2280
  | 1 => 2392
  | 2 => 2504
  | 3 => 2616
  | 4 => 2732
  | 5 => 2748
  | 6 => 2765
  | 7 => 2887
  | 8 => 2904
  | 9 => 2921
  | 10 => 2938
  | 11 => 3056
  | 12 => 3073
  | 13 => 3090
  | 14 => 3107
  | 15 => 3229
  | 16 => 3232
  | 17 => 3232
  | 18 => 3232
  | 19 => 3232
  | _ => 3233

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2514
  | 1 => 2780
  | 2 => 2953
  | 3 => 3122
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2615
  | 1 => 2886
  | 2 => 3055
  | 3 => 3228
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3372
  | 1 => 3790
  | 2 => 4123
  | 3 => 4454
  | _ => 535

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2157
theorem route_pc : A.instructionPC routeIndex = 0xb60 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2158
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3233
theorem tail_pc : A.instructionPC tailIndex = 0x11ff := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3280
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4664 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 3281
theorem schedule_pc : A.instructionPC scheduleIndex = 4665 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3332
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4857 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3333
theorem output_pc : A.instructionPC outputIndex = 4858 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3386
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4933 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
