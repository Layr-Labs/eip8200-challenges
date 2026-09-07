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
  | 8 => 1469
  | 9 => 1469
  | 10 => 1469
  | 11 => 1469
  | 12 => 1685
  | 13 => 1697
  | 14 => 1709
  | 15 => 1721
  | 16 => 1856
  | 17 => 1868
  | 18 => 1880
  | 19 => 1892
  | _ => 2023

def leftReturnIndex : Nat → Nat
  | 0 => 1297
  | 1 => 1297
  | 2 => 1297
  | 3 => 1297
  | 4 => 1309
  | 5 => 1321
  | 6 => 1333
  | 7 => 1468
  | 8 => 1684
  | 9 => 1684
  | 10 => 1684
  | 11 => 1684
  | 12 => 1696
  | 13 => 1708
  | 14 => 1720
  | 15 => 1855
  | 16 => 1867
  | 17 => 1879
  | 18 => 1891
  | 19 => 2022
  | _ => 2023

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
  | 3 => 1730
  | _ => 1901

def leftHelperJumpIndex : Nat → Nat
  | 0 => 411
  | 1 => 1462
  | 2 => 1295
  | 3 => 1849
  | _ => 2016

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
  | 0 => 2034
  | 1 => 2046
  | 2 => 2058
  | 3 => 2070
  | 4 => 2201
  | 5 => 2213
  | 6 => 2225
  | 7 => 2237
  | 8 => 2372
  | 9 => 2384
  | 10 => 2396
  | 11 => 2408
  | 12 => 2539
  | 13 => 2551
  | 14 => 2563
  | 15 => 2575
  | 16 => 2710
  | 17 => 2710
  | 18 => 2710
  | 19 => 2710
  | _ => 2816

def rightReturnIndex : Nat → Nat
  | 0 => 2045
  | 1 => 2057
  | 2 => 2069
  | 3 => 2200
  | 4 => 2212
  | 5 => 2224
  | 6 => 2236
  | 7 => 2371
  | 8 => 2383
  | 9 => 2395
  | 10 => 2407
  | 11 => 2538
  | 12 => 2550
  | 13 => 2562
  | 14 => 2574
  | 15 => 2709
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
  | 0 => 2079
  | 1 => 2246
  | 2 => 2417
  | 3 => 2584
  | _ => 473

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2194
  | 1 => 2365
  | 2 => 2532
  | 3 => 2703
  | _ => 855

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

def routeIndex : Nat := 2023
theorem route_pc : A.instructionPC routeIndex = 0xaa2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2024
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
