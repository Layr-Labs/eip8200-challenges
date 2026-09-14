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
  [opAt 1923 .JUMPDEST,
   pushAt 1924 2 2583,
   opAt 1925 (.Dup ⟨3, by decide⟩),
   opAt 1926 (.Dup ⟨0, by decide⟩),
   opAt 1927 (.Dup ⟨0, by decide⟩),
   pushAt 1928 2 1358,
   opAt 1929 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1914 .JUMPDEST,
   pushAt 1915 2 2688,
   opAt 1916 .MLOAD,
   pushAt 1917 1 128,
   opAt 1918 .LT,
   opAt 1919 (.Dup ⟨0, by decide⟩),
   pushAt 1920 1 8,
   opAt 1921 (.Swap ⟨0, by decide⟩),
   opAt 1922 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1937 .POP,
   pushAt 1938 1 5,
   opAt 1939 .SUB,
   pushAt 1940 2 1516,
   opAt 1941 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1930 .JUMPDEST,
   pushAt 1931 0 0,
   opAt 1932 .NOT,
   opAt 1933 .ADD,
   opAt 1934 (.Dup ⟨0, by decide⟩),
   pushAt 1935 2 2572,
   opAt 1936 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 1914 = 2559 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 1914 ≤ i) (hii : i ≤ 1941) :
    Artifact.submissionArtifact.instructionPC i =
      ([2559,2560,2563,2564,2566,2567,2568,2570,2571,2572,2573,2576,2577,2578,2579,2582,2583,2584,2585,2586,2587,2588,2591,2592,2593,2595,2596,2599] : List Nat)[i - 1914]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2559 = true :=
  Artifact.isValidJumpDest_index 1914 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2572 = true :=
  Artifact.isValidJumpDest_index 1923 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2583 = true :=
  Artifact.isValidJumpDest_index 1930 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
