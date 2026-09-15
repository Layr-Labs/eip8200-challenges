import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1920 .JUMPDEST,
   pushAt 1921 2 2583,
   opAt 1922 (.Dup ⟨3, by decide⟩),
   opAt 1923 (.Dup ⟨0, by decide⟩),
   opAt 1924 (.Dup ⟨0, by decide⟩),
   pushAt 1925 2 1358,
   opAt 1926 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1911 .JUMPDEST,
   pushAt 1912 2 2688,
   opAt 1913 .MLOAD,
   pushAt 1914 1 128,
   opAt 1915 .LT,
   opAt 1916 (.Dup ⟨0, by decide⟩),
   pushAt 1917 1 8,
   opAt 1918 (.Swap ⟨0, by decide⟩),
   opAt 1919 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1934 .POP,
   pushAt 1935 1 5,
   opAt 1936 .SUB,
   pushAt 1937 2 1516,
   opAt 1938 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1927 .JUMPDEST,
   pushAt 1928 0 0,
   opAt 1929 .NOT,
   opAt 1930 .ADD,
   opAt 1931 (.Dup ⟨0, by decide⟩),
   pushAt 1932 2 2572,
   opAt 1933 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 1911 = 2559 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 1911 ≤ i) (hii : i ≤ 1938) :
    Artifact.submissionArtifact.instructionPC i =
      ([2559,2560,2563,2564,2566,2567,2568,2570,2571,2572,2573,2576,2577,2578,2579,2582,2583,2584,2585,2586,2587,2588,2591,2592,2593,2595,2596,2599] : List Nat)[i - 1911]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2559 = true :=
  Artifact.isValidJumpDest_index 1911 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2572 = true :=
  Artifact.isValidJumpDest_index 1920 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2583 = true :=
  Artifact.isValidJumpDest_index 1927 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
