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
  [Main.opAt 1849 .JUMPDEST,
   Main.pushAt 1850 33 0,
   Main.opAt 1851 .CALLDATALOAD,
   Main.opAt 1852 (.Dup ⟨0, by decide⟩),
   Main.opAt 1853 .ISZERO,
   Main.pushAt 1854 38 0,
   Main.opAt 1855 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1856 33 0,
   Main.opAt 1857 .CALLDATALOAD,
   Main.pushAt 1858 2 3289,
   Main.pushAt 1859 -8 0,
   Main.opAt 1860 .MSTORE,
   Main.opAt 1861 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1862 35 0,
   Main.opAt 1863 .MSTORE,
   Main.opAt 1864 (.Dup ⟨1, by decide⟩),
   Main.opAt 1865 (.Dup ⟨1, by decide⟩),
   Main.opAt 1866 (.Dup ⟨0, by decide⟩),
   Main.opAt 1867 .MULMOD,
   Main.opAt 1868 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1869 0 0,
   Main.opAt 1870 .MSTORE]

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

def table3Path := updateAt 1872 96
def table4Path := updateAt 1879 128
def table5Path := updateAt 1886 160
def table6Path := updateAt 1893 192
def table7Path := updateAt 1900 224
def table8Path := updateAt 1907 256
def table9Path := updateAt 1914 288
def table10Path := updateAt 1921 320
def table11Path := updateAt 1928 352
def table12Path := updateAt 1935 384
def table13Path := updateAt 1942 416
def table14Path := updateAt 1949 448
def table15Path := updateAt 1956 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1962 .POP,
   Main.opAt 1963 .POP,
   Main.pushAt 1964 34 0,
   Main.pushAt 1965 1 247]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1966 .JUMPDEST,
   Main.opAt 1967 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1968 -73 0,
   Main.opAt 1969 .EQ,
   Main.pushAt 1970 50 0,
   Main.opAt 1971 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1972 (.Dup ⟨0, by decide⟩),
   Main.opAt 1973 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2165 33 0,
   Main.opAt 2166 .ADD,
   Main.pushAt 2167 33 0,
   Main.opAt 2168 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2169 .JUMPDEST,
   Main.opAt 2170 .POP,
   Main.pushAt 2171 33 0,
   Main.opAt 2172 .MSTORE,
   Main.pushAt 2173 33 0,
   Main.pushAt 2174 33 0,
   Main.opAt 2175 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2176 .JUMPDEST,
   Main.pushAt 2177 63 0,
   Main.pushAt 2178 33 0,
   Main.opAt 2179 .MSTORE,
   Main.pushAt 2180 33 0,
   Main.pushAt 2181 -86 0,
   Main.opAt 2182 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3065 = true :=
  Artifact.isValidJumpDest_index 2176 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3057 = true :=
  Artifact.isValidJumpDest_index 2169 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 2829 = true :=
  Artifact.isValidJumpDest_index 1966 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
