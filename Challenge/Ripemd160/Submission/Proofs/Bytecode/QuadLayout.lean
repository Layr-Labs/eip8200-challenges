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
  | 1 => 1881
  | 2 => 1113
  | 3 => 2212
  | _ => 2351

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2154
  | 1 => 2267
  | 2 => 2380
  | 3 => 2493
  | 4 => 2606
  | 5 => 2723
  | 6 => 2736
  | 7 => 2749
  | 8 => 2874
  | 9 => 2887
  | 10 => 2900
  | 11 => 2913
  | 12 => 3034
  | 13 => 3047
  | 14 => 3060
  | 15 => 3073
  | 16 => 3198
  | 17 => 3198
  | 18 => 3198
  | 19 => 3198
  | _ => 3201

def rightReturnIndex : Nat → Nat
  | 0 => 2266
  | 1 => 2379
  | 2 => 2492
  | 3 => 2605
  | 4 => 2722
  | 5 => 2735
  | 6 => 2748
  | 7 => 2873
  | 8 => 2886
  | 9 => 2899
  | 10 => 2912
  | 11 => 3033
  | 12 => 3046
  | 13 => 3059
  | 14 => 3072
  | 15 => 3197
  | 16 => 3200
  | 17 => 3200
  | 18 => 3200
  | 19 => 3200
  | _ => 3201

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2503
  | 1 => 2759
  | 2 => 2923
  | 3 => 3083
  | _ => 451

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2604
  | 1 => 2872
  | 2 => 3032
  | 3 => 3196
  | _ => 851

def rightHelperPCNat : Nat → Nat
  | 0 => 3395
  | 1 => 3815
  | 2 => 4155
  | 3 => 4493
  | _ => 535

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2143
theorem route_pc : A.instructionPC routeIndex = 0xb74 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2144
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb75 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3201
theorem tail_pc : A.instructionPC tailIndex = 0x122d := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3248
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4710 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 3249
theorem schedule_pc : A.instructionPC scheduleIndex = 4711 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 3300
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4903 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3301
theorem output_pc : A.instructionPC outputIndex = 4904 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3354
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4979 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
