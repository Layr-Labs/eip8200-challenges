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
  | 0 => 1093
  | 1 => 1093
  | 2 => 1093
  | 3 => 1093
  | 4 => 1282
  | 5 => 1294
  | 6 => 1306
  | 7 => 1318
  | 8 => 1453
  | 9 => 1453
  | 10 => 1453
  | 11 => 1453
  | 12 => 1669
  | 13 => 1681
  | 14 => 1693
  | 15 => 1705
  | 16 => 1840
  | 17 => 1852
  | 18 => 1864
  | 19 => 1876
  | _ => 2007

def leftReturnIndex : Nat → Nat
  | 0 => 1281
  | 1 => 1281
  | 2 => 1281
  | 3 => 1281
  | 4 => 1293
  | 5 => 1305
  | 6 => 1317
  | 7 => 1452
  | 8 => 1668
  | 9 => 1668
  | 10 => 1668
  | 11 => 1668
  | 12 => 1680
  | 13 => 1692
  | 14 => 1704
  | 15 => 1839
  | 16 => 1851
  | 17 => 1863
  | 18 => 1875
  | 19 => 2006
  | _ => 2007

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
  | 1 => 1327
  | 2 => 1099
  | 3 => 1714
  | _ => 1885

def leftHelperJumpIndex : Nat → Nat
  | 0 => 403
  | 1 => 1446
  | 2 => 1279
  | 3 => 1833
  | _ => 2000

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1697
  | 2 => 1352
  | 3 => 2263
  | _ => 2548

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2018
  | 1 => 2030
  | 2 => 2042
  | 3 => 2054
  | 4 => 2185
  | 5 => 2197
  | 6 => 2209
  | 7 => 2221
  | 8 => 2356
  | 9 => 2368
  | 10 => 2380
  | 11 => 2392
  | 12 => 2523
  | 13 => 2535
  | 14 => 2547
  | 15 => 2559
  | 16 => 2694
  | 17 => 2694
  | 18 => 2694
  | 19 => 2694
  | _ => 2816

def rightReturnIndex : Nat → Nat
  | 0 => 2029
  | 1 => 2041
  | 2 => 2053
  | 3 => 2184
  | 4 => 2196
  | 5 => 2208
  | 6 => 2220
  | 7 => 2355
  | 8 => 2367
  | 9 => 2379
  | 10 => 2391
  | 11 => 2522
  | 12 => 2534
  | 13 => 2546
  | 14 => 2558
  | 15 => 2693
  | 16 => 2815
  | 17 => 2815
  | 18 => 2815
  | 19 => 2815
  | _ => 2816

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2063
  | 1 => 2230
  | 2 => 2401
  | 3 => 2568
  | _ => 466

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2178
  | 1 => 2349
  | 2 => 2516
  | 3 => 2687
  | _ => 841

def rightHelperPCNat : Nat → Nat
  | 0 => 2845
  | 1 => 3126
  | 2 => 3411
  | 3 => 3692
  | _ => 561

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2007
theorem route_pc : A.instructionPC routeIndex = 0xaa2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2008
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xaa3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2816
theorem tail_pc : A.instructionPC tailIndex = 0x101b := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2869
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2898
theorem schedule_pc : A.instructionPC scheduleIndex = 4255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2949
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2954
theorem output_pc : A.instructionPC outputIndex = 4580 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3003
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4765 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
