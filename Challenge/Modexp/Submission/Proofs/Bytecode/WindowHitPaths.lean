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
  [Main.opAt 1873 .JUMPDEST,
   Main.pushAt 1874 1 160,
   Main.opAt 1875 .CALLDATALOAD,
   Main.opAt 1876 (.Dup ⟨0, by decide⟩),
   Main.opAt 1877 .ISZERO,
   Main.pushAt 1878 2 3592,
   Main.opAt 1879 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1880 1 96,
   Main.opAt 1881 .CALLDATALOAD,
   Main.pushAt 1882 1 1,
   Main.pushAt 1883 0 0,
   Main.opAt 1884 .MSTORE,
   Main.opAt 1885 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1886 1 32,
   Main.opAt 1887 .MSTORE,
   Main.opAt 1888 (.Dup ⟨1, by decide⟩),
   Main.opAt 1889 (.Dup ⟨1, by decide⟩),
   Main.opAt 1890 (.Dup ⟨0, by decide⟩),
   Main.opAt 1891 .MULMOD,
   Main.opAt 1892 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1893 1 64,
   Main.opAt 1894 .MSTORE]

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

def table3Path := updateAt 1895 96
def table4Path := updateAt 1904 128
def table5Path := updateAt 1913 160
def table6Path := updateAt 1922 192
def table7Path := updateAt 1931 224
def table8Path := updateAt 1940 256
def table9Path := updateAt 1949 288
def table10Path := updateAt 1958 320
def table11Path := updateAt 1967 352
def table12Path := updateAt 1976 384
def table13Path := updateAt 1985 416
def table14Path := updateAt 1994 448
def table15Path := updateAt 2003 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2012 .POP,
   Main.opAt 2013 .POP,
   Main.pushAt 2014 1 1,
   Main.pushAt 2015 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2016 .JUMPDEST,
   Main.opAt 2017 (.Dup ⟨0, by decide⟩),
   Main.pushAt 2018 1 160,
   Main.opAt 2019 .EQ,
   Main.pushAt 2020 2 3584,
   Main.opAt 2021 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2022 (.Dup ⟨0, by decide⟩),
   Main.opAt 2023 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2344 .POP,
   Main.pushAt 2345 1 4,
   Main.opAt 2346 .ADD,
   Main.pushAt 2347 2 3226,
   Main.opAt 2348 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2349 .JUMPDEST,
   Main.opAt 2350 .POP,
   Main.pushAt 2351 0 0,
   Main.opAt 2352 .MSTORE,
   Main.pushAt 2353 1 32,
   Main.pushAt 2354 0 0,
   Main.opAt 2355 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2356 .JUMPDEST,
   Main.pushAt 2357 0 0,
   Main.pushAt 2358 0 0,
   Main.opAt 2359 .MSTORE,
   Main.pushAt 2360 1 32,
   Main.pushAt 2361 0 0,
   Main.opAt 2362 .RETURN]

@[simp] theorem jump3592 :
    Decode.isValidJumpDest submissionBytecode 3592 = true :=
  Artifact.isValidJumpDest_index 2356 (by rfl)

@[simp] theorem jump3584 :
    Decode.isValidJumpDest submissionBytecode 3584 = true :=
  Artifact.isValidJumpDest_index 2349 (by rfl)

@[simp] theorem jump3226 :
    Decode.isValidJumpDest submissionBytecode 3226 = true :=
  Artifact.isValidJumpDest_index 2016 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
