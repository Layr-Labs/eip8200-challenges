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
  [Main.opAt 1843 .JUMPDEST,
   Main.pushAt 1844 1 160,
   Main.opAt 1845 .CALLDATALOAD,
   Main.opAt 1846 (.Dup ⟨0, by decide⟩),
   Main.opAt 1847 .ISZERO,
   Main.pushAt 1848 2 3556,
   Main.opAt 1849 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1850 1 96,
   Main.opAt 1851 .CALLDATALOAD,
   Main.pushAt 1852 1 1,
   Main.pushAt 1853 0 0,
   Main.opAt 1854 .MSTORE,
   Main.opAt 1855 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1856 1 32,
   Main.opAt 1857 .MSTORE,
   Main.opAt 1858 (.Dup ⟨1, by decide⟩),
   Main.opAt 1859 (.Dup ⟨1, by decide⟩),
   Main.opAt 1860 (.Dup ⟨0, by decide⟩),
   Main.opAt 1861 .MULMOD,
   Main.opAt 1862 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1863 1 64,
   Main.opAt 1864 .MSTORE]

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
  [Main.opAt 1982 .POP,
   Main.opAt 1983 .POP,
   Main.pushAt 1984 1 1,
   Main.pushAt 1985 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1986 .JUMPDEST,
   Main.opAt 1987 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1988 1 160,
   Main.opAt 1989 .EQ,
   Main.pushAt 1990 2 3548,
   Main.opAt 1991 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1992 (.Dup ⟨0, by decide⟩),
   Main.opAt 1993 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2314 .POP,
   Main.pushAt 2315 1 4,
   Main.opAt 2316 .ADD,
   Main.pushAt 2317 2 3190,
   Main.opAt 2318 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2319 .JUMPDEST,
   Main.opAt 2320 .POP,
   Main.pushAt 2321 0 0,
   Main.opAt 2322 .MSTORE,
   Main.pushAt 2323 1 32,
   Main.pushAt 2324 0 0,
   Main.opAt 2325 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2326 .JUMPDEST,
   Main.pushAt 2327 0 0,
   Main.pushAt 2328 0 0,
   Main.opAt 2329 .MSTORE,
   Main.pushAt 2330 1 32,
   Main.pushAt 2331 0 0,
   Main.opAt 2332 .RETURN]

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
