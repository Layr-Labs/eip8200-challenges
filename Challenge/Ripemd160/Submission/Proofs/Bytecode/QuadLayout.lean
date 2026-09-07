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
  | 5 => 1374
  | 6 => 1387
  | 7 => 1400
  | 8 => 1525
  | 9 => 1525
  | 10 => 1525
  | 11 => 1525
  | 12 => 1528
  | 13 => 1541
  | 14 => 1554
  | 15 => 1567
  | 16 => 1692
  | 17 => 1692
  | 18 => 1692
  | 19 => 1692
  | _ => 2143

def leftReturnIndex : Nat → Nat
  | 0 => 1360
  | 1 => 1360
  | 2 => 1360
  | 3 => 1360
  | 4 => 1373
  | 5 => 1386
  | 6 => 1399
  | 7 => 1524
  | 8 => 1527
  | 9 => 1527
  | 10 => 1527
  | 11 => 1527
  | 12 => 1540
  | 13 => 1553
  | 14 => 1566
  | 15 => 1691
  | 16 => 2142
  | 17 => 2142
  | 18 => 2142
  | 19 => 2142
  | _ => 2143

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 11))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 2
  | 1 => 1410
  | 2 => 909
  | 3 => 1577
  | _ => 1692

def leftHelperJumpIndex : Nat → Nat
  | 0 => 402
  | 1 => 1523
  | 2 => 1357
  | 3 => 1690
  | _ => 2139

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1892
  | 2 => 1124
  | 3 => 2223
  | _ => 2362

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2154
  | 1 => 2267
  | 2 => 2280
  | 3 => 2293
  | 4 => 2414
  | 5 => 2427
  | 6 => 2440
  | 7 => 2453
  | 8 => 2578
  | 9 => 2591
  | 10 => 2604
  | 11 => 2617
  | 12 => 2738
  | 13 => 2751
  | 14 => 2764
  | 15 => 2777
  | 16 => 2902
  | 17 => 2902
  | 18 => 2902
  | 19 => 2902
  | _ => 2905

def rightReturnIndex : Nat → Nat
  | 0 => 2266
  | 1 => 2279
  | 2 => 2292
  | 3 => 2413
  | 4 => 2426
  | 5 => 2439
  | 6 => 2452
  | 7 => 2577
  | 8 => 2590
  | 9 => 2603
  | 10 => 2616
  | 11 => 2737
  | 12 => 2750
  | 13 => 2763
  | 14 => 2776
  | 15 => 2901
  | 16 => 2904
  | 17 => 2904
  | 18 => 2904
  | 19 => 2904
  | _ => 2905

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2303
  | 1 => 2463
  | 2 => 2627
  | 3 => 2787
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2412
  | 1 => 2576
  | 2 => 2736
  | 3 => 2900
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3242
  | 1 => 3579
  | 2 => 3919
  | 3 => 4257
  | _ => 542

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2143
theorem route_pc : A.instructionPC routeIndex = 0xb7f := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2144
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb80 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2905
theorem tail_pc : A.instructionPC tailIndex = 0x1141 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2952
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4474 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2953
theorem schedule_pc : A.instructionPC scheduleIndex = 4475 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3004
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4673 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3005
theorem output_pc : A.instructionPC outputIndex = 4674 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3054
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4859 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
