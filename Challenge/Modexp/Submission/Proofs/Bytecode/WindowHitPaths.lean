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
   Main.pushAt 1848 2 3066,
   Main.opAt 1849 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1850 1 96,
   Main.opAt 1851 .CALLDATALOAD,
   Main.pushAt 1852 2 3268,
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
   Main.pushAt 1863 0 0,
   Main.opAt 1864 .MSTORE]

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
  [Main.opAt 1954 .POP,
   Main.opAt 1955 .POP,
   Main.pushAt 1956 1 1,
   Main.pushAt 1957 1 247]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1958 .JUMPDEST,
   Main.opAt 1959 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1960 1 160,
   Main.opAt 1961 .EQ,
   Main.pushAt 1962 2 3058,
   Main.opAt 1963 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1964 (.Dup ⟨0, by decide⟩),
   Main.opAt 1965 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2157 1 4,
   Main.opAt 2158 .ADD,
   Main.pushAt 2159 2 2830,
   Main.opAt 2160 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2161 .JUMPDEST,
   Main.opAt 2162 .POP,
   Main.pushAt 2163 0 0,
   Main.opAt 2164 .MSTORE,
   Main.pushAt 2165 1 32,
   Main.pushAt 2166 0 0,
   Main.opAt 2167 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2168 .JUMPDEST,
   Main.pushAt 2169 0 0,
   Main.pushAt 2170 0 0,
   Main.opAt 2171 .MSTORE,
   Main.pushAt 2172 1 32,
   Main.pushAt 2173 0 0,
   Main.opAt 2174 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3044 = true :=
  Artifact.isValidJumpDest_index 2168 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3036 = true :=
  Artifact.isValidJumpDest_index 2161 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 2808 = true :=
  Artifact.isValidJumpDest_index 1958 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
