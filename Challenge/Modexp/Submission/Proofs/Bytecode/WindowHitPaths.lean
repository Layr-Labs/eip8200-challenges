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
  [Main.opAt 1848 .JUMPDEST,
   Main.pushAt 1849 1 160,
   Main.opAt 1850 .CALLDATALOAD,
   Main.opAt 1851 (.Dup ⟨0, by decide⟩),
   Main.opAt 1852 .ISZERO,
   Main.pushAt 1853 2 3563,
   Main.opAt 1854 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1855 1 96,
   Main.opAt 1856 .CALLDATALOAD,
   Main.pushAt 1857 1 1,
   Main.pushAt 1858 0 0,
   Main.opAt 1859 .MSTORE,
   Main.opAt 1860 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1861 1 32,
   Main.opAt 1862 .MSTORE,
   Main.opAt 1863 (.Dup ⟨1, by decide⟩),
   Main.opAt 1864 (.Dup ⟨1, by decide⟩),
   Main.opAt 1865 (.Dup ⟨0, by decide⟩),
   Main.opAt 1866 .MULMOD,
   Main.opAt 1867 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1868 1 64,
   Main.opAt 1869 .MSTORE]

def updateAt (index offset : Nat)
    (h0 : Artifact.submissionInstructions[index]? =
      some (.op (.Dup ⟨1, by decide⟩)) := by rfl)
    (h1 : Artifact.submissionInstructions[index + 1]? =
      some (.op (.Dup ⟨3, by decide⟩)) := by rfl)
    (h2 : Artifact.submissionInstructions[index + 2]? =
      some (.op (.Swap ⟨1, by decide⟩)) := by rfl)
    (h3 : Artifact.submissionInstructions[index + 3]? =
      some (.op .MULMOD) := by rfl)
    (h4 : Artifact.submissionInstructions[index + 4]? =
      some (.op .JUMPDEST) := by rfl)
    (h5 : Artifact.submissionInstructions[index + 5]? =
      some (.op .JUMPDEST) := by rfl)
    (h6 : Artifact.submissionInstructions[index + 6]? =
      some (.op (.Dup ⟨0, by decide⟩)) := by rfl)
    (h7 : Artifact.submissionInstructions[index + 7]? =
      some (.push (if offset < 256 then 1 else 2) (UInt256.ofNat offset)) := by
        rfl)
    (h8 : Artifact.submissionInstructions[index + 8]? =
      some (.op .MSTORE) := by rfl) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt index (.Dup ⟨1, by decide⟩) h0,
   Main.opAt (index + 1) (.Dup ⟨3, by decide⟩) h1,
   Main.opAt (index + 2) (.Swap ⟨1, by decide⟩) h2,
   Main.opAt (index + 3) .MULMOD h3,
   Main.opAt (index + 4) .JUMPDEST h4,
   Main.opAt (index + 5) .JUMPDEST h5,
   Main.opAt (index + 6) (.Dup ⟨0, by decide⟩) h6,
   Main.pushAt (index + 7) (if offset < 256 then 1 else 2)
     (UInt256.ofNat offset) h7
     (Artifact.allWellFormed.valid (List.mem_of_getElem? h7)),
   Main.opAt (index + 8) .MSTORE h8]

def table3Path := updateAt 1870 96
def table4Path := updateAt 1879 128
def table5Path := updateAt 1888 160
def table6Path := updateAt 1897 192
def table7Path := updateAt 1906 224
def table8Path := updateAt 1915 256
def table9Path := updateAt 1924 288
def table10Path := updateAt 1933 320
def table11Path := updateAt 1942 352
def table12Path := updateAt 1951 384
def table13Path := updateAt 1960 416
def table14Path := updateAt 1969 448
def table15Path := updateAt 1978 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1987 .POP,
   Main.opAt 1988 .POP,
   Main.pushAt 1989 1 1,
   Main.pushAt 1990 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1991 .JUMPDEST,
   Main.opAt 1992 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1993 1 160,
   Main.opAt 1994 .EQ,
   Main.pushAt 1995 2 3555,
   Main.opAt 1996 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1997 (.Dup ⟨0, by decide⟩),
   Main.opAt 1998 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2319 .POP,
   Main.pushAt 2320 1 4,
   Main.opAt 2321 .ADD,
   Main.pushAt 2322 2 3197,
   Main.opAt 2323 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2324 .JUMPDEST,
   Main.opAt 2325 .POP,
   Main.pushAt 2326 0 0,
   Main.opAt 2327 .MSTORE,
   Main.pushAt 2328 1 32,
   Main.pushAt 2329 0 0,
   Main.opAt 2330 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2331 .JUMPDEST,
   Main.pushAt 2332 0 0,
   Main.pushAt 2333 0 0,
   Main.opAt 2334 .MSTORE,
   Main.pushAt 2335 1 32,
   Main.pushAt 2336 0 0,
   Main.opAt 2337 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3563 = true :=
  Artifact.isValidJumpDest_index 2331 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3555 = true :=
  Artifact.isValidJumpDest_index 2324 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 3197 = true :=
  Artifact.isValidJumpDest_index 1991 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
