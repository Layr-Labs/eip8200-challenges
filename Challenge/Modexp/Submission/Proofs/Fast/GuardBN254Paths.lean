import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Paths

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2190 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 2191 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.pushAt 2192 1 192,
   Main.opAt 2193 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.pushAt 2194 0 0,
   Main.opAt 2195 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2196 1 0,
   Main.opAt 2197 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2198 1 32,
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
   Main.pushAt 2213 32 5964364953636342908918930162962566239787286640968493902593843747347131818633,
   Main.opAt 2214 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2215 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2216 1 128,
   Main.opAt 2217 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2218 32 21888242871839275222246405745257275088696311157297823662689037894645226208581,
   Main.opAt 2219 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2220 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2221 1 160,
   Main.opAt 2222 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2223 32 21888242871839275222246405745257275088696311157297823662689037894645226208583,
   Main.opAt 2224 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2225 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2226 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))

def branchPushLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.pushAt 2227 2 5183

def branchJumpLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2228 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   branchIsZeroLocated,
   branchPushLocated,
   branchJumpLocated
  ]

def branchIsZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [branchIsZeroLocated]

def branchJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   branchPushLocated,
   branchJumpLocated
  ]

theorem branchPath_eq : branchPath = branchIsZeroPath ++ branchJumpPath := by rfl

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2229 2 1314,
   Main.opAt 2230 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2231 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2232 32 6720979588572738974916628410083100159223021409556719026881700545747062357561,
   Main.pushAt 2233 1 0,
   Main.opAt 2234 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2235 1 32,
   Main.pushAt 2236 0 0,
   Main.opAt 2237 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guardBN254PC0 (i : Nat) (hlo : 2190 ≤ i) (hhi : i ≤ 2210) :
    Artifact.submissionArtifact.instructionPC i =
      [5032, 5033, 5034, 5036, 5037, 5038, 5039, 5041, 5042, 5044, 5045, 5046, 5048, 5049, 5051, 5052, 5053, 5055, 5056, 5058, 5059][i - 2190]! := by
  interval_cases i <;> decide

@[simp] theorem guardBN254PC1 (i : Nat) (hlo : 2211 ≤ i) (hhi : i ≤ 2237) :
    Artifact.submissionArtifact.instructionPC i =
      [5060, 5062, 5063, 5096, 5097, 5098, 5100, 5101, 5134, 5135, 5136, 5138, 5139, 5172, 5173, 5174, 5175, 5178, 5179, 5182, 5183, 5184, 5217, 5219, 5220, 5222, 5223][i - 2211]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Paths
