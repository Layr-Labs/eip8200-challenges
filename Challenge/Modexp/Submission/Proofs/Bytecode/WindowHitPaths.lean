import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitStates

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Fixed-width window hit paths

Short located blocks for the modulus branch, table setup/updates, loop exit,
and both return tails.  The repeated four-byte loop body is kept in separate
modules so no one elaboration expands the complete appended program.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths

open EvmSemantics
open EvmSemantics.EVM

def modulusCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1879 .JUMPDEST,
   Main.pushAt 1880 1 160,
   Main.opAt 1881 .CALLDATALOAD,
   Main.opAt 1882 (.Dup ⟨0, by decide⟩),
   Main.opAt 1883 .ISZERO,
   Main.pushAt 1884 2 3607,
   Main.opAt 1885 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1886 1 96,
   Main.opAt 1887 .CALLDATALOAD,
   Main.pushAt 1888 1 1,
   Main.pushAt 1889 0 0,
   Main.opAt 1890 .MSTORE,
   Main.opAt 1891 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1892 1 32,
   Main.opAt 1893 .MSTORE,
   Main.opAt 1894 (.Dup ⟨1, by decide⟩),
   Main.opAt 1895 (.Dup ⟨1, by decide⟩),
   Main.opAt 1896 (.Dup ⟨0, by decide⟩),
   Main.opAt 1897 .MULMOD,
   Main.opAt 1898 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1899 1 64,
   Main.opAt 1900 .MSTORE]

def updateAt (index offset : Nat)
    (h0 : Artifact.submissionInstructions[index]? =
      some (.op (.Dup ⟨2, by decide⟩)) := by rfl)
    (h1 : Artifact.submissionInstructions[index + 1]? =
      some (.op (.Dup ⟨2, by decide⟩)) := by rfl)
    (h2 : Artifact.submissionInstructions[index + 2]? =
      some (.op (.Dup ⟨2, by decide⟩)) := by rfl)
    (h3 : Artifact.submissionInstructions[index + 3]? =
      some (.op .MULMOD) := by rfl)
    (h4 : Artifact.submissionInstructions[index + 4]? =
      some (.op (.Swap ⟨0, by decide⟩)) := by rfl)
    (h5 : Artifact.submissionInstructions[index + 5]? =
      some (.op .POP) := by rfl)
    (h6 : Artifact.submissionInstructions[index + 6]? =
      some (.op (.Dup ⟨0, by decide⟩)) := by rfl)
    (h7 : Artifact.submissionInstructions[index + 7]? =
      some (.push (if offset < 256 then 1 else 2) (UInt256.ofNat offset)) := by
        rfl)
    (h8 : Artifact.submissionInstructions[index + 8]? =
      some (.op .MSTORE) := by rfl) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt index (.Dup ⟨2, by decide⟩) h0,
   Main.opAt (index + 1) (.Dup ⟨2, by decide⟩) h1,
   Main.opAt (index + 2) (.Dup ⟨2, by decide⟩) h2,
   Main.opAt (index + 3) .MULMOD h3,
   Main.opAt (index + 4) (.Swap ⟨0, by decide⟩) h4,
   Main.opAt (index + 5) .POP h5,
   Main.opAt (index + 6) (.Dup ⟨0, by decide⟩) h6,
   Main.pushAt (index + 7) (if offset < 256 then 1 else 2)
     (UInt256.ofNat offset) h7
     (Artifact.allWellFormed.valid (List.mem_of_getElem? h7)),
   Main.opAt (index + 8) .MSTORE h8]

def table3Path := updateAt 1901 96
def table4Path := updateAt 1910 128
def table5Path := updateAt 1919 160
def table6Path := updateAt 1928 192
def table7Path := updateAt 1937 224
def table8Path := updateAt 1946 256
def table9Path := updateAt 1955 288
def table10Path := updateAt 1964 320
def table11Path := updateAt 1973 352
def table12Path := updateAt 1982 384
def table13Path := updateAt 1991 416
def table14Path := updateAt 2000 448
def table15Path := updateAt 2009 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2018 .POP,
   Main.opAt 2019 .POP,
   Main.pushAt 2020 1 1,
   Main.pushAt 2021 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2022 .JUMPDEST,
   Main.opAt 2023 (.Dup ⟨0, by decide⟩),
   Main.pushAt 2024 1 160,
   Main.opAt 2025 .EQ,
   Main.pushAt 2026 2 3599,
   Main.opAt 2027 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2028 (.Dup ⟨0, by decide⟩),
   Main.opAt 2029 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2350 .POP,
   Main.pushAt 2351 1 4,
   Main.opAt 2352 .ADD,
   Main.pushAt 2353 2 3241,
   Main.opAt 2354 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2355 .JUMPDEST,
   Main.opAt 2356 .POP,
   Main.pushAt 2357 0 0,
   Main.opAt 2358 .MSTORE,
   Main.pushAt 2359 1 32,
   Main.pushAt 2360 0 0,
   Main.opAt 2361 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2362 .JUMPDEST,
   Main.pushAt 2363 0 0,
   Main.pushAt 2364 0 0,
   Main.opAt 2365 .MSTORE,
   Main.pushAt 2366 1 32,
   Main.pushAt 2367 0 0,
   Main.opAt 2368 .RETURN]

@[simp] theorem jump3592 :
    Decode.isValidJumpDest submissionBytecode 3607 = true :=
  Artifact.isValidJumpDest_index 2362 (by rfl)

@[simp] theorem jump3584 :
    Decode.isValidJumpDest submissionBytecode 3599 = true :=
  Artifact.isValidJumpDest_index 2355 (by rfl)

@[simp] theorem jump3226 :
    Decode.isValidJumpDest submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2022 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
