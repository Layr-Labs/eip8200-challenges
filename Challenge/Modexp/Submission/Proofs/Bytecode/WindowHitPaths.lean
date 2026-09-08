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
  [Main.opAt 1837 .JUMPDEST,
   Main.pushAt 1838 1 160,
   Main.opAt 1839 .CALLDATALOAD,
   Main.opAt 1840 (.Dup ⟨0, by decide⟩),
   Main.opAt 1841 .ISZERO,
   Main.pushAt 1842 2 3558,
   Main.opAt 1843 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1844 1 96,
   Main.opAt 1845 .CALLDATALOAD,
   Main.pushAt 1846 1 1,
   Main.pushAt 1847 0 0,
   Main.opAt 1848 .MSTORE,
   Main.opAt 1849 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1850 1 32,
   Main.opAt 1851 .MSTORE,
   Main.opAt 1852 (.Dup ⟨1, by decide⟩),
   Main.opAt 1853 (.Dup ⟨1, by decide⟩),
   Main.opAt 1854 (.Dup ⟨0, by decide⟩),
   Main.opAt 1855 .MULMOD,
   Main.opAt 1856 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1857 1 64,
   Main.opAt 1858 .MSTORE]

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

def table3Path := updateAt 1859 96
def table4Path := updateAt 1866 128
def table5Path := updateAt 1873 160
def table6Path := updateAt 1880 192
def table7Path := updateAt 1887 224
def table8Path := updateAt 1894 256
def table9Path := updateAt 1901 288
def table10Path := updateAt 1908 320
def table11Path := updateAt 1915 352
def table12Path := updateAt 1922 384
def table13Path := updateAt 1929 416
def table14Path := updateAt 1936 448
def table15Path := updateAt 1943 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1950 .POP,
   Main.opAt 1951 .POP,
   Main.pushAt 1952 1 1,
   Main.pushAt 1953 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1954 .JUMPDEST,
   Main.opAt 1955 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1956 1 160,
   Main.opAt 1957 .EQ,
   Main.pushAt 1958 2 3550,
   Main.opAt 1959 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1960 (.Dup ⟨0, by decide⟩),
   Main.opAt 1961 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2153 1 4,
   Main.opAt 2154 .ADD,
   Main.pushAt 2155 2 3192,
   Main.opAt 2156 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2157 .JUMPDEST,
   Main.opAt 2158 .POP,
   Main.pushAt 2159 0 0,
   Main.opAt 2160 .MSTORE,
   Main.pushAt 2161 1 32,
   Main.pushAt 2162 0 0,
   Main.opAt 2163 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2164 .JUMPDEST,
   Main.pushAt 2165 0 0,
   Main.pushAt 2166 0 0,
   Main.opAt 2167 .MSTORE,
   Main.pushAt 2168 1 32,
   Main.pushAt 2169 0 0,
   Main.opAt 2170 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3558 = true :=
  Artifact.isValidJumpDest_index 2164 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3550 = true :=
  Artifact.isValidJumpDest_index 2157 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 3192 = true :=
  Artifact.isValidJumpDest_index 1954 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
