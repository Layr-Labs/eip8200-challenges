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
  | 1 => 2167
  | 2 => 2180
  | 3 => 2193
  | 4 => 2314
  | 5 => 2327
  | 6 => 2340
  | 7 => 2353
  | 8 => 2478
  | 9 => 2491
  | 10 => 2504
  | 11 => 2517
  | 12 => 2638
  | 13 => 2651
  | 14 => 2664
  | 15 => 2677
  | 16 => 2802
  | 17 => 2802
  | 18 => 2802
  | 19 => 2802
  | _ => 2805

def rightReturnIndex : Nat → Nat
  | 0 => 2166
  | 1 => 2179
  | 2 => 2192
  | 3 => 2313
  | 4 => 2326
  | 5 => 2339
  | 6 => 2352
  | 7 => 2477
  | 8 => 2490
  | 9 => 2503
  | 10 => 2516
  | 11 => 2637
  | 12 => 2650
  | 13 => 2663
  | 14 => 2676
  | 15 => 2801
  | 16 => 2804
  | 17 => 2804
  | 18 => 2804
  | 19 => 2804
  | _ => 2805

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2203
  | 1 => 2363
  | 2 => 2527
  | 3 => 2687
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2312
  | 1 => 2476
  | 2 => 2636
  | 3 => 2800
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3146
  | 1 => 3483
  | 2 => 3823
  | 3 => 4161
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

def tailIndex : Nat := 2805
theorem tail_pc : A.instructionPC tailIndex = 0x10e1 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2852
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4378 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2853
theorem schedule_pc : A.instructionPC scheduleIndex = 4379 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2904
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4577 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2905
theorem output_pc : A.instructionPC outputIndex = 4578 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2954
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4763 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
