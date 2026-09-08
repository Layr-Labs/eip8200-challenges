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
  [Main.opAt 1811 .JUMPDEST,
   Main.pushAt 1812 1 160,
   Main.opAt 1813 .CALLDATALOAD,
   Main.opAt 1814 (.Dup ⟨0, by decide⟩),
   Main.opAt 1815 .ISZERO,
   Main.pushAt 1816 2 3412,
   Main.opAt 1817 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1818 1 96,
   Main.opAt 1819 .CALLDATALOAD,
   Main.pushAt 1820 1 1,
   Main.pushAt 1821 0 0,
   Main.opAt 1822 .MSTORE,
   Main.opAt 1823 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1824 1 32,
   Main.opAt 1825 .MSTORE,
   Main.opAt 1826 (.Dup ⟨1, by decide⟩),
   Main.opAt 1827 (.Dup ⟨1, by decide⟩),
   Main.opAt 1828 (.Dup ⟨0, by decide⟩),
   Main.opAt 1829 .MULMOD,
   Main.opAt 1830 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1831 1 64,
   Main.opAt 1832 .MSTORE]

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
  [Main.opAt 1924 .POP,
   Main.opAt 1925 .POP,
   Main.pushAt 1926 1 1,
   Main.pushAt 1927 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1928 .JUMPDEST,
   Main.opAt 1929 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1930 1 160,
   Main.opAt 1931 .EQ,
   Main.pushAt 1932 2 3404,
   Main.opAt 1933 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1934 (.Dup ⟨0, by decide⟩),
   Main.opAt 1935 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2184 .POP,
   Main.pushAt 2185 1 4,
   Main.opAt 2186 .ADD,
   Main.pushAt 2187 2 3046,
   Main.opAt 2188 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2189 .JUMPDEST,
   Main.opAt 2190 .POP,
   Main.pushAt 2191 0 0,
   Main.opAt 2192 .MSTORE,
   Main.pushAt 2193 1 32,
   Main.pushAt 2194 0 0,
   Main.opAt 2195 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2196 .JUMPDEST,
   Main.pushAt 2197 0 0,
   Main.pushAt 2198 0 0,
   Main.opAt 2199 .MSTORE,
   Main.pushAt 2200 1 32,
   Main.pushAt 2201 0 0,
   Main.opAt 2202 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3412 = true :=
  Artifact.isValidJumpDest_index 2196 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3404 = true :=
  Artifact.isValidJumpDest_index 2189 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 3046 = true :=
  Artifact.isValidJumpDest_index 1928 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
