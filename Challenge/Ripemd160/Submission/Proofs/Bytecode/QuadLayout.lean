import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-! Exact cached-mask three-group layout. Replaced shared groups have only lane-boundary metadata; their old call/helper certificates are not used. -/
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
  | 0 => 1106
  | 1 => 1106
  | 2 => 1106
  | 3 => 1106
  | 4 => 1298
  | 5 => 1310
  | 6 => 1322
  | 7 => 1334
  | 8 => 1460
  | 9 => 1460
  | 10 => 1460
  | 11 => 1460
  | 12 => 1676
  | 13 => 1688
  | 14 => 1700
  | 15 => 1712
  | 16 => 1838
  | 17 => 1850
  | 18 => 1862
  | 19 => 1874
  | _ => 1996

def leftReturnIndex : Nat → Nat
  | 0 => 1297
  | 1 => 1297
  | 2 => 1297
  | 3 => 1297
  | 4 => 1309
  | 5 => 1321
  | 6 => 1333
  | 7 => 1459
  | 8 => 1675
  | 9 => 1675
  | 10 => 1675
  | 11 => 1675
  | 12 => 1687
  | 13 => 1699
  | 14 => 1711
  | 15 => 1837
  | 16 => 1849
  | 17 => 1861
  | 18 => 1873
  | 19 => 1995
  | _ => 1996

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 10))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 2
  | 1 => 1343
  | 2 => 1112
  | 3 => 1721
  | _ => 1883

def leftHelperJumpIndex : Nat → Nat
  | 0 => 403
  | 1 => 1458
  | 2 => 1292
  | 3 => 1836
  | _ => 1994

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1772
  | 2 => 1352
  | 3 => 2377
  | _ => 2700

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2007
  | 1 => 2019
  | 2 => 2031
  | 3 => 2043
  | 4 => 2165
  | 5 => 2177
  | 6 => 2189
  | 7 => 2201
  | 8 => 2327
  | 9 => 2339
  | 10 => 2351
  | 11 => 2363
  | 12 => 2485
  | 13 => 2497
  | 14 => 2509
  | 15 => 2521
  | 16 => 2647
  | 17 => 2647
  | 18 => 2647
  | 19 => 2647
  | _ => 2749

def rightReturnIndex : Nat → Nat
  | 0 => 2018
  | 1 => 2030
  | 2 => 2042
  | 3 => 2164
  | 4 => 2176
  | 5 => 2188
  | 6 => 2200
  | 7 => 2326
  | 8 => 2338
  | 9 => 2350
  | 10 => 2362
  | 11 => 2484
  | 12 => 2496
  | 13 => 2508
  | 14 => 2520
  | 15 => 2646
  | 16 => 2748
  | 17 => 2748
  | 18 => 2748
  | 19 => 2748
  | _ => 2749

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2052
  | 1 => 2210
  | 2 => 2372
  | 3 => 2530
  | _ => 473

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2163
  | 1 => 2325
  | 2 => 2483
  | 3 => 2645
  | _ => 848

def rightHelperPCNat : Nat → Nat
  | 0 => 3036
  | 1 => 3371
  | 2 => 3709
  | 3 => 4045
  | _ => 561

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1996
theorem route_pc : A.instructionPC routeIndex = 0xb15 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1997
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2749
theorem tail_pc : A.instructionPC tailIndex = 0x10eb := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2796
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4388 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2803
theorem schedule_pc : A.instructionPC scheduleIndex = 4395 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2854
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4593 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2855
theorem output_pc : A.instructionPC outputIndex = 4594 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2904
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4779 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
