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
  | 0 => 352
  | 1 => 352
  | 2 => 352
  | 3 => 352
  | 4 => 752
  | 5 => 769
  | 6 => 786
  | 7 => 803
  | 8 => 925
  | 9 => 925
  | 10 => 925
  | 11 => 925
  | 12 => 1373
  | 13 => 1390
  | 14 => 1407
  | 15 => 1424
  | 16 => 1546
  | 17 => 1546
  | 18 => 1546
  | 19 => 1546
  | _ => 1994

def leftReturnIndex : Nat → Nat
  | 0 => 752
  | 1 => 752
  | 2 => 752
  | 3 => 752
  | 4 => 768
  | 5 => 785
  | 6 => 802
  | 7 => 924
  | 8 => 1373
  | 9 => 1373
  | 10 => 1373
  | 11 => 1373
  | 12 => 1389
  | 13 => 1406
  | 14 => 1423
  | 15 => 1545
  | 16 => 1994
  | 17 => 1994
  | 18 => 1994
  | 19 => 1994
  | _ => 1994

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 352
  | 1 => 817
  | 2 => 925
  | 3 => 1438
  | _ => 1546

def leftHelperJumpIndex : Nat → Nat
  | 0 => 751
  | 1 => 923
  | 2 => 1372
  | 3 => 1544
  | _ => 1993

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
  | 0 => 2005
  | 1 => 2117
  | 2 => 2229
  | 3 => 2341
  | 4 => 2453
  | 5 => 2569
  | 6 => 2685
  | 7 => 2801
  | 8 => 2917
  | 9 => 2934
  | 10 => 2951
  | 11 => 2968
  | 12 => 3086
  | 13 => 3103
  | 14 => 3120
  | 15 => 3137
  | 16 => 3259
  | 17 => 3259
  | 18 => 3259
  | 19 => 3259
  | _ => 3659

def rightReturnIndex : Nat → Nat
  | 0 => 2117
  | 1 => 2229
  | 2 => 2341
  | 3 => 2453
  | 4 => 2569
  | 5 => 2685
  | 6 => 2801
  | 7 => 2917
  | 8 => 2933
  | 9 => 2950
  | 10 => 2967
  | 11 => 3085
  | 12 => 3102
  | 13 => 3119
  | 14 => 3136
  | 15 => 3258
  | 16 => 3659
  | 17 => 3659
  | 18 => 3659
  | 19 => 3659
  | _ => 3659

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2351
  | 1 => 2982
  | 2 => 2982
  | 3 => 3151
  | _ => 3259

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2452
  | 1 => 3084
  | 2 => 3084
  | 3 => 3257
  | _ => 3658

def rightHelperPCNat : Nat → Nat
  | 0 => 3332
  | 1 => 4222
  | 2 => 4222
  | 3 => 4553
  | _ => 4701

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1994
theorem route_pc : A.instructionPC routeIndex = 0xb45 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1995
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb46 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3659
theorem tail_pc : A.instructionPC tailIndex = 0x141d := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3706
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5206 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 283
theorem schedule_pc : A.instructionPC scheduleIndex = 514 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3707
theorem output_pc : A.instructionPC outputIndex = 5207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3760
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5282 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
