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
  | 8 => 1444
  | 9 => 1444
  | 10 => 1444
  | 11 => 1444
  | 12 => 1660
  | 13 => 1672
  | 14 => 1684
  | 15 => 1696
  | 16 => 1822
  | 17 => 1834
  | 18 => 1846
  | 19 => 1858
  | _ => 1980

def leftReturnIndex : Nat → Nat
  | 0 => 1281
  | 1 => 1281
  | 2 => 1281
  | 3 => 1281
  | 4 => 1293
  | 5 => 1305
  | 6 => 1317
  | 7 => 1443
  | 8 => 1659
  | 9 => 1659
  | 10 => 1659
  | 11 => 1659
  | 12 => 1671
  | 13 => 1683
  | 14 => 1695
  | 15 => 1821
  | 16 => 1833
  | 17 => 1845
  | 18 => 1857
  | 19 => 1979
  | _ => 1980

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
  | 3 => 1705
  | _ => 1867

def leftHelperJumpIndex : Nat → Nat
  | 0 => 403
  | 1 => 1442
  | 2 => 1279
  | 3 => 1820
  | _ => 1978

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
  | 0 => 1991
  | 1 => 2003
  | 2 => 2015
  | 3 => 2027
  | 4 => 2149
  | 5 => 2161
  | 6 => 2173
  | 7 => 2185
  | 8 => 2311
  | 9 => 2323
  | 10 => 2335
  | 11 => 2347
  | 12 => 2469
  | 13 => 2481
  | 14 => 2493
  | 15 => 2505
  | 16 => 2631
  | 17 => 2631
  | 18 => 2631
  | 19 => 2631
  | _ => 2728

def rightReturnIndex : Nat → Nat
  | 0 => 2002
  | 1 => 2014
  | 2 => 2026
  | 3 => 2148
  | 4 => 2160
  | 5 => 2172
  | 6 => 2184
  | 7 => 2310
  | 8 => 2322
  | 9 => 2334
  | 10 => 2346
  | 11 => 2468
  | 12 => 2480
  | 13 => 2492
  | 14 => 2504
  | 15 => 2630
  | 16 => 2727
  | 17 => 2727
  | 18 => 2727
  | 19 => 2727
  | _ => 2728

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 10))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2036
  | 1 => 2194
  | 2 => 2356
  | 3 => 2514
  | _ => 466

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2147
  | 1 => 2309
  | 2 => 2467
  | 3 => 2629
  | _ => 841

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

def routeIndex : Nat := 1980
theorem route_pc : A.instructionPC routeIndex = 0xb15 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1981
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2728
theorem tail_pc : A.instructionPC tailIndex = 0x10e6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2781
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4389 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2782
theorem schedule_pc : A.instructionPC scheduleIndex = 4390 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2833
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4588 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2834
theorem output_pc : A.instructionPC outputIndex = 4589 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2883
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4774 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
