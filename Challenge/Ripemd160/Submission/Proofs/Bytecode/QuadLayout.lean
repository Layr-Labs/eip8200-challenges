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
  | 5 => 1295
  | 6 => 1308
  | 7 => 1321
  | 8 => 1446
  | 9 => 1446
  | 10 => 1446
  | 11 => 1446
  | 12 => 1662
  | 13 => 1675
  | 14 => 1688
  | 15 => 1701
  | 16 => 1826
  | 17 => 1839
  | 18 => 1852
  | 19 => 1865
  | _ => 1986

def leftReturnIndex : Nat → Nat
  | 0 => 1281
  | 1 => 1281
  | 2 => 1281
  | 3 => 1281
  | 4 => 1294
  | 5 => 1307
  | 6 => 1320
  | 7 => 1445
  | 8 => 1661
  | 9 => 1661
  | 10 => 1661
  | 11 => 1661
  | 12 => 1674
  | 13 => 1687
  | 14 => 1700
  | 15 => 1825
  | 16 => 1838
  | 17 => 1851
  | 18 => 1864
  | 19 => 1985
  | _ => 1986

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
  | 1 => 1331
  | 2 => 1099
  | 3 => 1711
  | _ => 1875

def leftHelperJumpIndex : Nat → Nat
  | 0 => 403
  | 1 => 1444
  | 2 => 1279
  | 3 => 1824
  | _ => 1984

def leftHelperPCNat : Nat → Nat
  | 0 => 4
  | 1 => 1776
  | 2 => 1352
  | 3 => 2383
  | _ => 2708

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1997
  | 1 => 2010
  | 2 => 2023
  | 3 => 2036
  | 4 => 2157
  | 5 => 2170
  | 6 => 2183
  | 7 => 2196
  | 8 => 2321
  | 9 => 2334
  | 10 => 2347
  | 11 => 2360
  | 12 => 2481
  | 13 => 2494
  | 14 => 2507
  | 15 => 2520
  | 16 => 2645
  | 17 => 2645
  | 18 => 2645
  | 19 => 2645
  | _ => 2742

def rightReturnIndex : Nat → Nat
  | 0 => 2009
  | 1 => 2022
  | 2 => 2035
  | 3 => 2156
  | 4 => 2169
  | 5 => 2182
  | 6 => 2195
  | 7 => 2320
  | 8 => 2333
  | 9 => 2346
  | 10 => 2359
  | 11 => 2480
  | 12 => 2493
  | 13 => 2506
  | 14 => 2519
  | 15 => 2644
  | 16 => 2741
  | 17 => 2741
  | 18 => 2741
  | 19 => 2741
  | _ => 2742

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 11))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2046
  | 1 => 2206
  | 2 => 2370
  | 3 => 2530
  | _ => 466

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2155
  | 1 => 2319
  | 2 => 2479
  | 3 => 2643
  | _ => 841

def rightHelperPCNat : Nat → Nat
  | 0 => 3046
  | 1 => 3383
  | 2 => 3723
  | 3 => 4061
  | _ => 561

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1986
theorem route_pc : A.instructionPC routeIndex = 0xb1b := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1987
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb1c := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 2742
theorem tail_pc : A.instructionPC tailIndex = 0x10f4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 2795
theorem tailJump_pc : A.instructionPC tailJumpIndex = 4403 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 2796
theorem schedule_pc : A.instructionPC scheduleIndex = 4404 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleJumpIndex : Nat := 2847
theorem scheduleJump_pc : A.instructionPC scheduleJumpIndex = 4602 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 2848
theorem output_pc : A.instructionPC outputIndex = 4603 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 2897
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 4788 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
