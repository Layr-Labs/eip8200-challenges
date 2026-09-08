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
  [Main.opAt 1822 .JUMPDEST,
   Main.pushAt 1823 1 160,
   Main.opAt 1824 .CALLDATALOAD,
   Main.opAt 1825 (.Dup ⟨0, by decide⟩),
   Main.opAt 1826 .ISZERO,
   Main.pushAt 1827 2 3525,
   Main.opAt 1828 .JUMPI]

def tablePreludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1829 1 96,
   Main.opAt 1830 .CALLDATALOAD,
   Main.pushAt 1831 1 1,
   Main.pushAt 1832 0 0,
   Main.opAt 1833 .MSTORE,
   Main.opAt 1834 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1835 1 32,
   Main.opAt 1836 .MSTORE,
   Main.opAt 1837 (.Dup ⟨1, by decide⟩),
   Main.opAt 1838 (.Dup ⟨1, by decide⟩),
   Main.opAt 1839 (.Dup ⟨0, by decide⟩),
   Main.opAt 1840 .MULMOD,
   Main.opAt 1841 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1842 1 64,
   Main.opAt 1843 .MSTORE]

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

def table3Path := updateAt 1844 96
def table4Path := updateAt 1851 128
def table5Path := updateAt 1858 160
def table6Path := updateAt 1865 192
def table7Path := updateAt 1872 224
def table8Path := updateAt 1879 256
def table9Path := updateAt 1886 288
def table10Path := updateAt 1893 320
def table11Path := updateAt 1900 352
def table12Path := updateAt 1907 384
def table13Path := updateAt 1914 416
def table14Path := updateAt 1921 448
def table15Path := updateAt 1928 480

def tableFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1935 .POP,
   Main.opAt 1936 .POP,
   Main.pushAt 1937 1 1,
   Main.pushAt 1938 1 128]

def loopGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1939 .JUMPDEST,
   Main.opAt 1940 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1941 1 160,
   Main.opAt 1942 .EQ,
   Main.pushAt 1943 2 3517,
   Main.opAt 1944 .JUMPI]

def wordLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1945 (.Dup ⟨0, by decide⟩),
   Main.opAt 1946 .CALLDATALOAD]

def loopAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 2138 1 4,
   Main.opAt 2139 .ADD,
   Main.pushAt 2140 2 3159,
   Main.opAt 2141 .JUMP]

def normalReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2142 .JUMPDEST,
   Main.opAt 2143 .POP,
   Main.pushAt 2144 0 0,
   Main.opAt 2145 .MSTORE,
   Main.pushAt 2146 1 32,
   Main.pushAt 2147 0 0,
   Main.opAt 2148 .RETURN]

def zeroReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 2149 .JUMPDEST,
   Main.pushAt 2150 0 0,
   Main.pushAt 2151 0 0,
   Main.opAt 2152 .MSTORE,
   Main.pushAt 2153 1 32,
   Main.pushAt 2154 0 0,
   Main.opAt 2155 .RETURN]

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3525 = true :=
  Artifact.isValidJumpDest_index 2149 (by rfl)

@[simp] theorem jump3555 :
    Decode.isValidJumpDest submissionBytecode 3517 = true :=
  Artifact.isValidJumpDest_index 2142 (by rfl)

@[simp] theorem jump3197 :
    Decode.isValidJumpDest submissionBytecode 3159 = true :=
  Artifact.isValidJumpDest_index 1939 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
