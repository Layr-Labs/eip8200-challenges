import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2197 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 2198 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.pushAt 2199 1 160,
   Main.opAt 2200 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.pushAt 2201 0 0,
   Main.opAt 2202 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2203 0 0,
   Main.opAt 2204 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2205 0 0,
   Main.opAt 2206 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2207 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2208 1 32,
   Main.opAt 2209 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2210 1 32,
   Main.opAt 2211 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2212 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2213 1 64,
   Main.opAt 2214 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2215 1 32,
   Main.opAt 2216 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2217 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2218 1 96,
   Main.opAt 2219 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2220 5 4294968273,
   Main.opAt 2221 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.NOT)),
   Main.opAt 2222 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2223 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2224 1 128,
   Main.opAt 2225 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2226 5 4294968272,
   Main.opAt 2227 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.NOT)),
   Main.opAt 2228 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2229 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2230 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))

def branchPushLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.pushAt 2231 2 4978

def branchJumpLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2232 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def branchIsZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [branchIsZeroLocated]

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2233 2 1314,
   Main.opAt 2234 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2235 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2236 0 0,
   Main.pushAt 2237 0 0,
   Main.opAt 2238 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2239 1 32,
   Main.pushAt 2240 0 0,
   Main.opAt 2241 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem gEip2PC0 (i : Nat) (hlo : 2197 ≤ i) (hhi : i ≤ 2217) :
    Artifact.submissionArtifact.instructionPC i =
      [4919, 4920, 4921, 4923, 4924, 4925, 4926, 4927, 4928, 4929, 4930, 4931, 4933, 4934, 4936, 4937, 4938, 4940, 4941, 4943, 4944][i - 2197]! := by
  interval_cases i <;> decide

@[simp] theorem gEip2PC1 (i : Nat) (hlo : 2218 ≤ i) (hhi : i ≤ 2238) :
    Artifact.submissionArtifact.instructionPC i =
      [4945, 4947, 4948, 4954, 4955, 4956, 4957, 4959, 4960, 4966, 4967, 4968, 4969, 4970, 4973, 4974, 4977, 4978, 4979, 4980, 4981][i - 2218]! := by
  interval_cases i <;> decide

@[simp] theorem gEip2PC2 (i : Nat) (hlo : 2239 ≤ i) (hhi : i ≤ 2241) :
    Artifact.submissionArtifact.instructionPC i =
      [4982, 4984, 4985][i - 2239]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths
