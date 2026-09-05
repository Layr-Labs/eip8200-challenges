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
   Main.opAt 2190 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 2191 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.pushAt 2192 1 160,
   Main.opAt 2193 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.pushAt 2194 0 0,
   Main.opAt 2195 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2196 0 0,
   Main.opAt 2197 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2198 0 0,
   Main.opAt 2199 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2200 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2201 1 32,
   Main.opAt 2202 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2203 1 32,
   Main.opAt 2204 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2205 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2206 1 64,
   Main.opAt 2207 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2208 1 32,
   Main.opAt 2209 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2210 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2211 1 96,
   Main.opAt 2212 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2213 32 115792089237316195423570985008687907853269984665640564039457584007908834671662,
   Main.opAt 2214 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2215 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2216 1 128,
   Main.opAt 2217 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2218 32 115792089237316195423570985008687907853269984665640564039457584007908834671663,
   Main.opAt 2219 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2220 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2221 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))

def branchPushLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.pushAt 2222 2 5143

def branchJumpLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2223 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def branchIsZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [branchIsZeroLocated]

def branchJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [branchPushLocated, branchJumpLocated]

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2224 2 1314,
   Main.opAt 2225 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2226 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2227 0 0,
   Main.pushAt 2228 0 0,
   Main.opAt 2229 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2230 1 32,
   Main.pushAt 2231 0 0,
   Main.opAt 2232 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guardEip2PC0 (i : Nat) (hlo : 2190 ≤ i) (hhi : i ≤ 2210) :
    Artifact.submissionArtifact.instructionPC i =
      [5032, 5033, 5034, 5036, 5037, 5038, 5039, 5040, 5041, 5042, 5043, 5044, 5046, 5047, 5049, 5050, 5051, 5053, 5054, 5056, 5057][i - 2190]! := by
  interval_cases i <;> decide

@[simp] theorem guardEip2PC1 (i : Nat) (hlo : 2211 ≤ i) (hhi : i ≤ 2231) :
    Artifact.submissionArtifact.instructionPC i =
      [5058, 5060, 5061, 5094, 5095, 5096, 5098, 5099, 5132, 5133, 5134, 5135, 5138, 5139, 5142, 5143, 5144, 5145, 5146, 5147, 5149][i - 2211]! := by
  interval_cases i <;> decide

@[simp] theorem guardEip2PC2 (i : Nat) (hlo : 2232 ≤ i) (hhi : i ≤ 2232) :
    Artifact.submissionArtifact.instructionPC i =
      [5150][i - 2232]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths
