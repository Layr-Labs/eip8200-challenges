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
  | 1 => 1881
  | 2 => 1113
  | 3 => 2205
  | _ => 2337

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2169
  | 1 => 2282
  | 2 => 2395
  | 3 => 2508
  | 4 => 2621
  | 5 => 2738
  | 6 => 2755
  | 7 => 2772
  | 8 => 2894
  | 9 => 2911
  | 10 => 2928
  | 11 => 2945
  | 12 => 3063
  | 13 => 3080
  | 14 => 3097
  | 15 => 3114
  | 16 => 3236
  | 17 => 3236
  | 18 => 3236
  | 19 => 3236
  | _ => 3239

def rightReturnIndex : Nat → Nat
  | 0 => 2281
  | 1 => 2394
  | 2 => 2507
  | 3 => 2620
  | 4 => 2737
  | 5 => 2754
  | 6 => 2771
  | 7 => 2893
  | 8 => 2910
  | 9 => 2927
  | 10 => 2944
  | 11 => 3062
  | 12 => 3079
  | 13 => 3096
  | 14 => 3113
  | 15 => 3235
  | 16 => 3238
  | 17 => 3238
  | 18 => 3238
  | 19 => 3238
  | _ => 3239

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2518
  | 1 => 2786
  | 2 => 2959
  | 3 => 3128
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2619
  | 1 => 2892
  | 2 => 3061
  | 3 => 3234
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3376
  | 1 => 3796
  | 2 => 4129
  | 3 => 4460
  | _ => 535

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2158
theorem route_pc : A.instructionPC routeIndex = 0xb61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2159
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb62 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3239
theorem tail_pc : A.instructionPC tailIndex = 0x1205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3286
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4670 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 3287
theorem schedule_pc : A.instructionPC scheduleIndex = 4671 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3338
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4863 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3339
theorem output_pc : A.instructionPC outputIndex = 4864 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3392
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4939 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
