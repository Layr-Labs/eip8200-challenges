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
   Main.pushAt 1853 2 3481,
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
    (h6 : Artifact.submissionInstructions[index + 4]? =
      some (.op (.Dup ⟨0, by decide⟩)) := by rfl)
    (h7 : Artifact.submissionInstructions[index + 5]? =
      some (.push (if offset < 256 then 1 else 2) (UInt256.ofNat offset)) := by
        rfl)
    (h8 : Artifact.submissionInstructions[index + 6]? =
      some (.op .MSTORE) := by rfl) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt index (.Dup ⟨1, by decide⟩) h0,
   Main.opAt (index + 1) (.Dup ⟨3, by decide⟩) h1,
   Main.opAt (index + 2) (.Swap ⟨1, by decide⟩) h2,
   Main.opAt (index + 3) .MULMOD h3,
   Main.opAt (index + 4) (.Dup ⟨0, by decide⟩) h6,
   Main.pushAt (index + 5) (if offset < 256 then 1 else 2)
     (UInt256.ofNat offset) h7
     (Artifact.allWellFormed.valid (List.mem_of_getElem? h7)),
   Main.opAt (index + 6) .MSTORE h8]

def table3Path := updateAt 1870 96
def table4Path := updateAt 1877 128
def table5Path := updateAt 1884 160
def table6Path := updateAt 1891 192
def table7Path := updateAt 1898 224
def table8Path := updateAt 1905 256
def table9Path := updateAt 1912 288
def table10Path := updateAt 1919 320
def table11Path := updateAt 1926 352
def table12Path := updateAt 1933 384
def table13Path := updateAt 1940 416
def table14Path := updateAt 1947 448
def table15Path := updateAt 1954 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1961 .POP,
   Main.opAt 1962 .POP,
   Main.pushAt 1963 1 1,
   Main.pushAt 1964 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1965 .JUMPDEST,
   Main.opAt 1966 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1967 1 160,
   Main.opAt 1968 .EQ,
   Main.pushAt 1969 2 3473,
   Main.opAt 1970 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1971 (.Dup ⟨0, by decide⟩),
   Main.opAt 1972 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2221 .POP,
   Main.pushAt 2222 1 4,
   Main.opAt 2223 .ADD,
   Main.pushAt 2224 2 3171,
   Main.opAt 2225 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2226 .JUMPDEST,
   Main.opAt 2227 .POP,
   Main.pushAt 2228 0 0,
   Main.opAt 2229 .MSTORE,
   Main.pushAt 2230 1 32,
   Main.pushAt 2231 0 0,
   Main.opAt 2232 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2233 .JUMPDEST,
   Main.pushAt 2234 0 0,
   Main.pushAt 2235 0 0,
   Main.opAt 2236 .MSTORE,
   Main.pushAt 2237 1 32,
   Main.pushAt 2238 0 0,
   Main.opAt 2239 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3481 = true :=
  Artifact.isValidJumpDest_index 2233 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2226 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 3171 = true :=
  Artifact.isValidJumpDest_index 1965 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
