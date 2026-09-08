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
  | 0 => 307
  | 1 => 307
  | 2 => 307
  | 3 => 307
  | 4 => 707
  | 5 => 724
  | 6 => 741
  | 7 => 758
  | 8 => 880
  | 9 => 880
  | 10 => 880
  | 11 => 880
  | 12 => 1330
  | 13 => 1347
  | 14 => 1364
  | 15 => 1381
  | 16 => 1503
  | 17 => 1503
  | 18 => 1503
  | 19 => 1503
  | _ => 1953

def leftReturnIndex : Nat → Nat
  | 0 => 707
  | 1 => 707
  | 2 => 707
  | 3 => 707
  | 4 => 723
  | 5 => 740
  | 6 => 757
  | 7 => 879
  | 8 => 1330
  | 9 => 1330
  | 10 => 1330
  | 11 => 1330
  | 12 => 1346
  | 13 => 1363
  | 14 => 1380
  | 15 => 1502
  | 16 => 1953
  | 17 => 1953
  | 18 => 1953
  | 19 => 1953
  | _ => 1953

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 307
  | 1 => 772
  | 2 => 880
  | 3 => 1395
  | _ => 1503

def leftHelperJumpIndex : Nat → Nat
  | 0 => 706
  | 1 => 878
  | 2 => 1329
  | 3 => 1501
  | _ => 1952

def leftHelperPCNat : Nat → Nat
  | 0 => 656
  | 1 => 1290
  | 2 => 1422
  | 3 => 2111
  | _ => 2243

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1964
  | 1 => 1964
  | 2 => 1964
  | 3 => 1964
  | 4 => 2414
  | 5 => 2414
  | 6 => 2414
  | 7 => 2414
  | 8 => 2880
  | 9 => 2880
  | 10 => 2880
  | 11 => 2880
  | 12 => 3330
  | 13 => 3347
  | 14 => 3364
  | 15 => 3381
  | 16 => 3503
  | 17 => 3503
  | 18 => 3503
  | 19 => 3503
  | _ => 3903

def rightReturnIndex : Nat → Nat
  | 0 => 2414
  | 1 => 2414
  | 2 => 2414
  | 3 => 2414
  | 4 => 2880
  | 5 => 2880
  | 6 => 2880
  | 7 => 2880
  | 8 => 3330
  | 9 => 3330
  | 10 => 3330
  | 11 => 3330
  | 12 => 3346
  | 13 => 3363
  | 14 => 3380
  | 15 => 3502
  | 16 => 3903
  | 17 => 3903
  | 18 => 3903
  | 19 => 3903
  | _ => 3903

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 1964
  | 1 => 2414
  | 2 => 2880
  | 3 => 3395
  | _ => 3503

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2413
  | 1 => 2879
  | 2 => 3329
  | 3 => 3501
  | _ => 3902

def rightHelperPCNat : Nat → Nat
  | 0 => 2761
  | 1 => 3263
  | 2 => 3781
  | 3 => 4470
  | _ => 4618

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1953
theorem route_pc : A.instructionPC routeIndex = 2745 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1954
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 2746 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3903
theorem tail_pc : A.instructionPC tailIndex = 5066 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3950
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5123 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 244
theorem schedule_pc : A.instructionPC scheduleIndex = 440 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3983
theorem output_pc : A.instructionPC outputIndex = 5190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 4036
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5265 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
