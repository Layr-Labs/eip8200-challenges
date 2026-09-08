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
  [Main.opAt 1838 .JUMPDEST,
   Main.pushAt 1839 1 160,
   Main.opAt 1840 .CALLDATALOAD,
   Main.opAt 1841 (.Dup ⟨0, by decide⟩),
   Main.opAt 1842 .ISZERO,
   Main.pushAt 1843 2 3558,
   Main.opAt 1844 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1845 1 96,
   Main.opAt 1846 .CALLDATALOAD,
   Main.pushAt 1847 1 1,
   Main.pushAt 1848 0 0,
   Main.opAt 1849 .MSTORE,
   Main.opAt 1850 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1851 1 32,
   Main.opAt 1852 .MSTORE,
   Main.opAt 1853 (.Dup ⟨1, by decide⟩),
   Main.opAt 1854 (.Dup ⟨1, by decide⟩),
   Main.opAt 1855 (.Dup ⟨0, by decide⟩),
   Main.opAt 1856 .MULMOD,
   Main.opAt 1857 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1858 1 64,
   Main.opAt 1859 .MSTORE]

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
  [Main.opAt 1951 .POP,
   Main.opAt 1952 .POP,
   Main.pushAt 1953 1 1,
   Main.pushAt 1954 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1955 .JUMPDEST,
   Main.opAt 1956 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1957 1 160,
   Main.opAt 1958 .EQ,
   Main.pushAt 1959 2 3550,
   Main.opAt 1960 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1961 (.Dup ⟨0, by decide⟩),
   Main.opAt 1962 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2162 1 4,
   Main.opAt 2163 .ADD,
   Main.pushAt 2164 2 3192,
   Main.opAt 2165 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2166 .JUMPDEST,
   Main.opAt 2167 .POP,
   Main.pushAt 2168 0 0,
   Main.opAt 2169 .MSTORE,
   Main.pushAt 2170 1 32,
   Main.pushAt 2171 0 0,
   Main.opAt 2172 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2173 .JUMPDEST,
   Main.pushAt 2174 0 0,
   Main.pushAt 2175 0 0,
   Main.opAt 2176 .MSTORE,
   Main.pushAt 2177 1 32,
   Main.pushAt 2178 0 0,
   Main.opAt 2179 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3558 = true :=
  Artifact.isValidJumpDest_index 2173 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3550 = true :=
  Artifact.isValidJumpDest_index 2166 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 3192 = true :=
  Artifact.isValidJumpDest_index 1955 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
