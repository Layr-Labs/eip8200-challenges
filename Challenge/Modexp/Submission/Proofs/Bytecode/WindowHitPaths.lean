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
  [Main.opAt 1834 .JUMPDEST,
   Main.pushAt 1835 1 160,
   Main.opAt 1836 .CALLDATALOAD,
   Main.opAt 1837 (.Dup ⟨0, by decide⟩),
   Main.opAt 1838 .ISZERO,
   Main.pushAt 1839 2 3066,
   Main.opAt 1840 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1841 1 96,
   Main.opAt 1842 .CALLDATALOAD,
   Main.pushAt 1843 1 1,
   Main.pushAt 1844 0 0,
   Main.opAt 1845 .MSTORE,
   Main.opAt 1846 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1847 1 32,
   Main.opAt 1848 .MSTORE,
   Main.opAt 1849 (.Dup ⟨1, by decide⟩),
   Main.opAt 1850 (.Dup ⟨1, by decide⟩),
   Main.opAt 1851 (.Dup ⟨0, by decide⟩),
   Main.opAt 1852 .MULMOD,
   Main.opAt 1853 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1854 1 64,
   Main.opAt 1855 .MSTORE]

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

def table3Path := updateAt 1856 96
def table4Path := updateAt 1863 128
def table5Path := updateAt 1870 160
def table6Path := updateAt 1877 192
def table7Path := updateAt 1884 224
def table8Path := updateAt 1891 256
def table9Path := updateAt 1898 288
def table10Path := updateAt 1905 320
def table11Path := updateAt 1912 352
def table12Path := updateAt 1919 384
def table13Path := updateAt 1926 416
def table14Path := updateAt 1933 448
def table15Path := updateAt 1940 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1947 .POP,
   Main.opAt 1948 .POP,
   Main.pushAt 1949 1 1,
   Main.pushAt 1950 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1951 .JUMPDEST,
   Main.opAt 1952 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1953 1 160,
   Main.opAt 1954 .EQ,
   Main.pushAt 1955 2 3058,
   Main.opAt 1956 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1957 (.Dup ⟨0, by decide⟩),
   Main.opAt 1958 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2150 1 4,
   Main.opAt 2151 .ADD,
   Main.pushAt 2152 2 2830,
   Main.opAt 2153 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2154 .JUMPDEST,
   Main.opAt 2155 .POP,
   Main.pushAt 2156 0 0,
   Main.opAt 2157 .MSTORE,
   Main.pushAt 2158 1 32,
   Main.pushAt 2159 0 0,
   Main.opAt 2160 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2161 .JUMPDEST,
   Main.pushAt 2162 0 0,
   Main.pushAt 2163 0 0,
   Main.opAt 2164 .MSTORE,
   Main.pushAt 2165 1 32,
   Main.pushAt 2166 0 0,
   Main.opAt 2167 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3066 = true :=
  Artifact.isValidJumpDest_index 2161 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3058 = true :=
  Artifact.isValidJumpDest_index 2154 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 2830 = true :=
  Artifact.isValidJumpDest_index 1951 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
