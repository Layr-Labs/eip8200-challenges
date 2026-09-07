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
  | 0 => 327
  | 1 => 327
  | 2 => 327
  | 3 => 327
  | 4 => 727
  | 5 => 744
  | 6 => 761
  | 7 => 778
  | 8 => 900
  | 9 => 900
  | 10 => 900
  | 11 => 900
  | 12 => 1348
  | 13 => 1365
  | 14 => 1382
  | 15 => 1399
  | 16 => 1521
  | 17 => 1521
  | 18 => 1521
  | 19 => 1521
  | _ => 1969

def leftReturnIndex : Nat → Nat
  | 0 => 727
  | 1 => 727
  | 2 => 727
  | 3 => 727
  | 4 => 743
  | 5 => 760
  | 6 => 777
  | 7 => 899
  | 8 => 1348
  | 9 => 1348
  | 10 => 1348
  | 11 => 1348
  | 12 => 1364
  | 13 => 1381
  | 14 => 1398
  | 15 => 1520
  | 16 => 1969
  | 17 => 1969
  | 18 => 1969
  | 19 => 1969
  | _ => 1969

def leftPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (leftWrapperIndex k))
def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftWrapperIndex k + 15))
def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (leftReturnIndex k))

theorem leftWrapper_pc (k : Fin 21) :
    A.instructionPC (leftWrapperIndex k.val) = (leftPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def leftHelperStartIndex : Nat → Nat
  | 0 => 327
  | 1 => 792
  | 2 => 900
  | 3 => 1413
  | _ => 1521

def leftHelperJumpIndex : Nat → Nat
  | 0 => 726
  | 1 => 898
  | 2 => 1347
  | 3 => 1519
  | _ => 1968

def leftHelperPCNat : Nat → Nat
  | 0 => 704
  | 1 => 1338
  | 2 => 1470
  | 3 => 2217
  | _ => 2349

def leftHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (leftHelperPCNat (k / 4))

theorem leftHelper_pc (group : Fin 5) :
    A.instructionPC (leftHelperStartIndex group.val) =
      leftHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightWrapperIndex : Nat → Nat
  | 0 => 1980
  | 1 => 2092
  | 2 => 2204
  | 3 => 2221
  | 4 => 2339
  | 5 => 2356
  | 6 => 2373
  | 7 => 2390
  | 8 => 2512
  | 9 => 2512
  | 10 => 2512
  | 11 => 2512
  | 12 => 2960
  | 13 => 2977
  | 14 => 2994
  | 15 => 3011
  | 16 => 3133
  | 17 => 3133
  | 18 => 3133
  | 19 => 3133
  | _ => 3533

def rightReturnIndex : Nat → Nat
  | 0 => 2092
  | 1 => 2204
  | 2 => 2220
  | 3 => 2338
  | 4 => 2355
  | 5 => 2372
  | 6 => 2389
  | 7 => 2511
  | 8 => 2960
  | 9 => 2960
  | 10 => 2960
  | 11 => 2960
  | 12 => 2976
  | 13 => 2993
  | 14 => 3010
  | 15 => 3132
  | 16 => 3533
  | 17 => 3533
  | 18 => 3533
  | 19 => 3533
  | _ => 3533

def rightPC (k : Nat) : UInt256 := UInt256.ofNat (A.instructionPC (rightWrapperIndex k))
def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightWrapperIndex k + 15))
def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (A.instructionPC (rightReturnIndex k))

theorem rightWrapper_pc (k : Fin 21) :
    A.instructionPC (rightWrapperIndex k.val) = (rightPC k.val).toNat := by
  fin_cases k <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def rightHelperStartIndex : Nat → Nat
  | 0 => 2235
  | 1 => 2404
  | 2 => 2512
  | 3 => 3025
  | _ => 3133

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2337
  | 1 => 2510
  | 2 => 2959
  | 3 => 3131
  | _ => 3532

def rightHelperPCNat : Nat → Nat
  | 0 => 3295
  | 1 => 3625
  | 2 => 3773
  | 3 => 4520
  | _ => 4668

def rightHelperPC (k : Nat) : UInt256 :=
  UInt256.ofNat (rightHelperPCNat (k / 4))

theorem rightHelper_pc (group : Fin 5) :
    A.instructionPC (rightHelperStartIndex group.val) =
      rightHelperPCNat group.val := by
  fin_cases group <;> rw [ArtifactByteLength.instructionPC_eq_byteLength] <;> decide

def routeIndex : Nat := 1969
theorem route_pc : A.instructionPC routeIndex = 0xb5d := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def rightLoadIndex : Nat := 1970
theorem rightLoad_pc : A.instructionPC rightLoadIndex = 0xb5e := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailIndex : Nat := 3533
theorem tail_pc : A.instructionPC tailIndex = 0x13fc := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailJumpIndex : Nat := 3580
theorem tailJump_pc : A.instructionPC tailJumpIndex = 5173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleIndex : Nat := 264
theorem schedule_pc : A.instructionPC scheduleIndex = 488 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputIndex : Nat := 3581
theorem output_pc : A.instructionPC outputIndex = 5174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def outputReturnIndex : Nat := 3630
theorem outputReturn_pc : A.instructionPC outputReturnIndex = 5359 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
