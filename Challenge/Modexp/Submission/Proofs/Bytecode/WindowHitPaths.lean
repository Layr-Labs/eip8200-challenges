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
  [Main.opAt 1841 .JUMPDEST,
   Main.pushAt 1842 1 160,
   Main.opAt 1843 .CALLDATALOAD,
   Main.opAt 1844 (.Dup ⟨0, by decide⟩),
   Main.opAt 1845 .ISZERO,
   Main.pushAt 1846 2 3066,
   Main.opAt 1847 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1848 1 96,
   Main.opAt 1849 .CALLDATALOAD,
   Main.pushAt 1850 2 3268,
   Main.pushAt 1851 0 0,
   Main.opAt 1852 .MSTORE,
   Main.opAt 1853 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1854 1 32,
   Main.opAt 1855 .MSTORE,
   Main.opAt 1856 (.Dup ⟨1, by decide⟩),
   Main.opAt 1857 (.Dup ⟨1, by decide⟩),
   Main.opAt 1858 (.Dup ⟨0, by decide⟩),
   Main.opAt 1859 .MULMOD,
   Main.opAt 1860 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1861 0 0,
   Main.opAt 1862 .MSTORE]

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
  [Main.opAt 1952 .POP,
   Main.opAt 1953 .POP,
   Main.pushAt 1954 1 1,
   Main.pushAt 1955 1 247]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1956 .JUMPDEST,
   Main.opAt 1957 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1958 1 160,
   Main.opAt 1959 .EQ,
   Main.pushAt 1960 2 3058,
   Main.opAt 1961 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1962 (.Dup ⟨0, by decide⟩),
   Main.opAt 1963 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2155 1 4,
   Main.opAt 2156 .ADD,
   Main.pushAt 2157 2 2830,
   Main.opAt 2158 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2159 .JUMPDEST,
   Main.opAt 2160 .POP,
   Main.pushAt 2161 0 0,
   Main.opAt 2162 .MSTORE,
   Main.pushAt 2163 1 32,
   Main.pushAt 2164 0 0,
   Main.opAt 2165 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2166 .JUMPDEST,
   Main.pushAt 2167 0 0,
   Main.pushAt 2168 0 0,
   Main.opAt 2169 .MSTORE,
   Main.pushAt 2170 1 32,
   Main.pushAt 2171 0 0,
   Main.opAt 2172 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3044 = true :=
  Artifact.isValidJumpDest_index 2166 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3036 = true :=
  Artifact.isValidJumpDest_index 2159 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 2808 = true :=
  Artifact.isValidJumpDest_index 1956 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
