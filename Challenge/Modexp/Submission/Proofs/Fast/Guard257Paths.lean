import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2139 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 2140 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.pushAt 2141 1 163,
   Main.opAt 2142 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.pushAt 2143 0 0,
   Main.opAt 2144 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2145 0 0,
   Main.opAt 2146 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2147 1 33,
   Main.opAt 2148 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2149 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2150 1 32,
   Main.opAt 2151 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2152 1 1,
   Main.opAt 2153 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2154 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2155 1 64,
   Main.opAt 2156 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2157 1 33,
   Main.opAt 2158 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2159 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2160 1 96,
   Main.opAt 2161 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2162 32 452312848583266388373324160190187140051835877600158453279131187530910662656,
   Main.opAt 2163 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2164 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2165 1 128,
   Main.opAt 2166 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2167 32 2266871685857013885419158128209026732832114290800391293656575918782654971904,
   Main.opAt 2168 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2169 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2170 1 160,
   Main.opAt 2171 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2172 32 48312224427533946512043291035939178167157762805192705886137669566595072,
   Main.opAt 2173 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2174 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2175 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))

def branchPushLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.pushAt 2176 2 4988

def branchJumpLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2177 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

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
   Main.pushAt 2178 2 1314,
   Main.opAt 2179 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2180 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2181 0 0,
   Main.pushAt 2182 0 0,
   Main.opAt 2183 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2184 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   Main.pushAt 2185 1 1,
   Main.opAt 2186 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2187 1 33,
   Main.pushAt 2188 0 0,
   Main.opAt 2189 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guard257PC0 (i : Nat) (hlo : 2139 ≤ i) (hhi : i ≤ 2159) :
    Artifact.submissionArtifact.instructionPC i =
      [4838, 4839, 4840, 4842, 4843, 4844, 4845, 4846, 4847, 4849, 4850, 4851, 4853, 4854, 4856, 4857, 4858, 4860, 4861, 4863, 4864][i - 2139]! := by
  interval_cases i <;> decide

@[simp] theorem guard257PC1 (i : Nat) (hlo : 2160 ≤ i) (hhi : i ≤ 2189) :
    Artifact.submissionArtifact.instructionPC i =
      [4865, 4867, 4868, 4901, 4902, 4903, 4905, 4906, 4939, 4940, 4941, 4943, 4944, 4977, 4978, 4979, 4980, 4983, 4984, 4987, 4988, 4989, 4990, 4991, 4992, 5025, 5027, 5028, 5030, 5031][i - 2160]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths
