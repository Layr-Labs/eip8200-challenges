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
  | 0 => 363
  | 1 => 363
  | 2 => 363
  | 3 => 363
  | 4 => 763
  | 5 => 780
  | 6 => 797
  | 7 => 814
  | 8 => 936
  | 9 => 936
  | 10 => 936
  | 11 => 936
  | 12 => 1386
  | 13 => 1403
  | 14 => 1420
  | 15 => 1437
  | 16 => 1559
  | 17 => 1559
  | 18 => 1559
  | 19 => 1559
  | _ => 2009

def leftReturnIndex : Nat → Nat
  | 0 => 763
  | 1 => 763
  | 2 => 763
  | 3 => 763
  | 4 => 779
  | 5 => 796
  | 6 => 813
  | 7 => 935
  | 8 => 1386
  | 9 => 1386
  | 10 => 1386
  | 11 => 1386
  | 12 => 1402
  | 13 => 1419
  | 14 => 1436
  | 15 => 1558
  | 16 => 2009
  | 17 => 2009
  | 18 => 2009
  | 19 => 2009
  | _ => 2009

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 363
  | 1 => 828
  | 2 => 936
  | 3 => 1451
  | _ => 1559

def leftHelperJumpIndex : Nat → Nat
  | 0 => 762
  | 1 => 934
  | 2 => 1385
  | 3 => 1557
  | _ => 2008

def leftHelperPCNat : Nat → Nat
  | 0 => 636
  | 1 => 1270
  | 2 => 1402
  | 3 => 2091
  | _ => 2223

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2020
  | 1 => 2020
  | 2 => 2020
  | 3 => 2020
  | 4 => 2470
  | 5 => 2470
  | 6 => 2470
  | 7 => 2470
  | 8 => 2936
  | 9 => 2936
  | 10 => 2936
  | 11 => 2936
  | 12 => 3386
  | 13 => 3403
  | 14 => 3420
  | 15 => 3437
  | 16 => 3559
  | 17 => 3559
  | 18 => 3559
  | 19 => 3559
  | _ => 3959

def rightReturnIndex : Nat → Nat
  | 0 => 2470
  | 1 => 2470
  | 2 => 2470
  | 3 => 2470
  | 4 => 2936
  | 5 => 2936
  | 6 => 2936
  | 7 => 2936
  | 8 => 3386
  | 9 => 3386
  | 10 => 3386
  | 11 => 3386
  | 12 => 3402
  | 13 => 3419
  | 14 => 3436
  | 15 => 3558
  | 16 => 3959
  | 17 => 3959
  | 18 => 3959
  | 19 => 3959
  | _ => 3959

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2020
  | 1 => 2470
  | 2 => 2936
  | 3 => 3451
  | _ => 3559

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2469
  | 1 => 2935
  | 2 => 3385
  | 3 => 3557
  | _ => 3958

def rightHelperPCNat : Nat → Nat
  | 0 => 2741
  | 1 => 3243
  | 2 => 3761
  | 3 => 4450
  | _ => 4598

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 2009
theorem route_pc : A.instructionPC routeIndex = 2725 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 2010
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2726 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3959
theorem tail_pc : A.instructionPC tailIndex = 5046 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 4006
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5103 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 288
theorem schedule_pc : A.instructionPC scheduleIndex = 520 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 4007
theorem output_pc : A.instructionPC outputIndex = 5104 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4060
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
