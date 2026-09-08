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
  [Main.opAt 1845 .JUMPDEST,
   Main.pushAt 1846 1 160,
   Main.opAt 1847 .CALLDATALOAD,
   Main.opAt 1848 (.Dup ⟨0, by decide⟩),
   Main.opAt 1849 .ISZERO,
   Main.pushAt 1850 2 3348,
   Main.opAt 1851 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1852 1 96,
   Main.opAt 1853 .CALLDATALOAD,
   Main.pushAt 1854 1 1,
   Main.pushAt 1855 0 0,
   Main.opAt 1856 .MSTORE,
   Main.opAt 1857 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1858 1 32,
   Main.opAt 1859 .MSTORE,
   Main.opAt 1860 (.Dup ⟨1, by decide⟩),
   Main.opAt 1861 (.Dup ⟨1, by decide⟩),
   Main.opAt 1862 (.Dup ⟨0, by decide⟩),
   Main.opAt 1863 .MULMOD,
   Main.opAt 1864 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1865 1 64,
   Main.opAt 1866 .MSTORE]

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
      some (.op (.Dup ⟨0, by decide⟩)) := by rfl)
    (h5 : Artifact.submissionInstructions[index + 5]? =
      some (.push (if offset < 256 then 3 else 4) (UInt256.ofNat offset)) := by rfl)
    (h6 : Artifact.submissionInstructions[index + 6]? =
      some (.op .MSTORE) := by rfl) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt index (.Dup ⟨1, by decide⟩) h0,
   Main.opAt (index + 1) (.Dup ⟨3, by decide⟩) h1,
   Main.opAt (index + 2) (.Swap ⟨1, by decide⟩) h2,
   Main.opAt (index + 3) .MULMOD h3,
   Main.opAt (index + 4) (.Dup ⟨0, by decide⟩) h4,
   Main.pushAt (index + 5) (if offset < 256 then 3 else 4)
     (UInt256.ofNat offset) h5
     (Artifact.allWellFormed.valid (List.mem_of_getElem? h5)),
   Main.opAt (index + 6) .MSTORE h6]

def table3Path := updateAt 1860 96
def table4Path := updateAt 1867 128
def table5Path := updateAt 1874 160
def table6Path := updateAt 1881 192
def table7Path := updateAt 1888 224
def table8Path := updateAt 1895 256
def table9Path := updateAt 1902 288
def table10Path := updateAt 1909 320
def table11Path := updateAt 1916 352
def table12Path := updateAt 1923 384
def table13Path := updateAt 1930 416
def table14Path := updateAt 1937 448
def table15Path := updateAt 1944 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1958 .POP,
   Main.opAt 1959 .POP,
   Main.pushAt 1960 1 1,
   Main.pushAt 1961 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1962 .JUMPDEST,
   Main.opAt 1963 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1964 1 160,
   Main.opAt 1965 .EQ,
   Main.pushAt 1966 2 3340,
   Main.opAt 1967 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1968 (.Dup ⟨0, by decide⟩),
   Main.opAt 1969 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2161 1 4,
   Main.opAt 2162 .ADD,
   Main.pushAt 2163 2 2982,
   Main.opAt 2164 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2165 .JUMPDEST,
   Main.opAt 2166 .POP,
   Main.pushAt 2167 0 0,
   Main.opAt 2168 .MSTORE,
   Main.pushAt 2169 1 32,
   Main.pushAt 2170 0 0,
   Main.opAt 2171 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2172 .JUMPDEST,
   Main.pushAt 2173 0 0,
   Main.pushAt 2174 0 0,
   Main.opAt 2175 .MSTORE,
   Main.pushAt 2176 1 32,
   Main.pushAt 2177 0 0,
   Main.opAt 2178 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3348 = true :=
  Artifact.isValidJumpDest_index 2172 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3340 = true :=
  Artifact.isValidJumpDest_index 2165 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 2982 = true :=
  Artifact.isValidJumpDest_index 1962 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
