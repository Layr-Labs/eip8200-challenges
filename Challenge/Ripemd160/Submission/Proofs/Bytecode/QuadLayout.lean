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
  | 0 => 346
  | 1 => 346
  | 2 => 346
  | 3 => 346
  | 4 => 746
  | 5 => 763
  | 6 => 780
  | 7 => 797
  | 8 => 919
  | 9 => 919
  | 10 => 919
  | 11 => 919
  | 12 => 1369
  | 13 => 1386
  | 14 => 1403
  | 15 => 1420
  | 16 => 1542
  | 17 => 1542
  | 18 => 1542
  | 19 => 1542
  | _ => 1992

def leftReturnIndex : Nat → Nat
  | 0 => 746
  | 1 => 746
  | 2 => 746
  | 3 => 746
  | 4 => 762
  | 5 => 779
  | 6 => 796
  | 7 => 918
  | 8 => 1369
  | 9 => 1369
  | 10 => 1369
  | 11 => 1369
  | 12 => 1385
  | 13 => 1402
  | 14 => 1419
  | 15 => 1541
  | 16 => 1992
  | 17 => 1992
  | 18 => 1992
  | 19 => 1992
  | _ => 1992

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 346
  | 1 => 811
  | 2 => 919
  | 3 => 1434
  | _ => 1542

def leftHelperJumpIndex : Nat → Nat
  | 0 => 745
  | 1 => 917
  | 2 => 1368
  | 3 => 1540
  | _ => 1991

def leftHelperPCNat : Nat → Nat
  | 0 => 730
  | 1 => 1364
  | 2 => 1496
  | 3 => 2185
  | _ => 2317

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 2003
  | 1 => 2003
  | 2 => 2003
  | 3 => 2003
  | 4 => 2453
  | 5 => 2453
  | 6 => 2453
  | 7 => 2453
  | 8 => 2919
  | 9 => 2919
  | 10 => 2919
  | 11 => 2919
  | 12 => 3369
  | 13 => 3386
  | 14 => 3403
  | 15 => 3420
  | 16 => 3542
  | 17 => 3542
  | 18 => 3542
  | 19 => 3542
  | _ => 3942

def rightReturnIndex : Nat → Nat
  | 0 => 2453
  | 1 => 2453
  | 2 => 2453
  | 3 => 2453
  | 4 => 2919
  | 5 => 2919
  | 6 => 2919
  | 7 => 2919
  | 8 => 3369
  | 9 => 3369
  | 10 => 3369
  | 11 => 3369
  | 12 => 3385
  | 13 => 3402
  | 14 => 3419
  | 15 => 3541
  | 16 => 3942
  | 17 => 3942
  | 18 => 3942
  | 19 => 3942
  | _ => 3942

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2003
  | 1 => 2453
  | 2 => 2919
  | 3 => 3434
  | _ => 3542

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2452
  | 1 => 2918
  | 2 => 3368
  | 3 => 3540
  | _ => 3941

def rightHelperPCNat : Nat → Nat
  | 0 => 2835
  | 1 => 3337
  | 2 => 3855
  | 3 => 4544
  | _ => 4692

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1992
theorem route_pc : A.instructionPC routeIndex = 2819 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1993
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2820 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3942
theorem tail_pc : A.instructionPC tailIndex = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3989
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 283
theorem schedule_pc : A.instructionPC scheduleIndex = 514 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3990
theorem output_pc : A.instructionPC outputIndex = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4043
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
