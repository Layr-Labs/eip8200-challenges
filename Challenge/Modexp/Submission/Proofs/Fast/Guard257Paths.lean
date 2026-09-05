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
   Main.pushAt 2162 1 1,
   Main.pushAt 2163 1 248,
   Main.opAt 2164 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.SHL)),
   Main.opAt 2165 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2166 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2167 1 128,
   Main.opAt 2168 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2169 3 328449,
   Main.pushAt 2170 1 232,
   Main.opAt 2171 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.SHL)),
   Main.opAt 2172 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2173 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2174 1 160,
   Main.opAt 2175 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 2176 1 7,
   Main.pushAt 2177 1 232,
   Main.opAt 2178 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.SHL)),
   Main.opAt 2179 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2180 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2181 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))

def branchPushLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.pushAt 2182 2 4906

def branchJumpLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2183 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def branchIsZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [branchIsZeroLocated]

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.pushAt 2184 2 4919,
   Main.opAt 2185 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) := [
   Main.opAt 2186 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2187 0 0,
   Main.pushAt 2188 0 0,
   Main.opAt 2189 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2190 0 0,
   Main.opAt 2191 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.NOT)),
   Main.pushAt 2192 1 1,
   Main.opAt 2193 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2194 1 33,
   Main.pushAt 2195 0 0,
   Main.opAt 2196 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem g257PC0 (i : Nat) (hlo : 2139 ≤ i) (hhi : i ≤ 2159) :
    Artifact.submissionArtifact.instructionPC i =
      [4838, 4839, 4840, 4842, 4843, 4844, 4845, 4846, 4847, 4849, 4850, 4851, 4853, 4854, 4856, 4857, 4858, 4860, 4861, 4863, 4864][i - 2139]! := by
  interval_cases i <;> decide

@[simp] theorem g257PC1 (i : Nat) (hlo : 2160 ≤ i) (hhi : i ≤ 2180) :
    Artifact.submissionArtifact.instructionPC i =
      [4865, 4867, 4868, 4870, 4872, 4873, 4874, 4875, 4877, 4878, 4882, 4884, 4885, 4886, 4887, 4889, 4890, 4892, 4894, 4895, 4896][i - 2160]! := by
  interval_cases i <;> decide

@[simp] theorem g257PC2 (i : Nat) (hlo : 2181 ≤ i) (hhi : i ≤ 2196) :
    Artifact.submissionArtifact.instructionPC i =
      [4897, 4898, 4901, 4902, 4905, 4906, 4907, 4908, 4909, 4910, 4911, 4912, 4914, 4915, 4917, 4918][i - 2181]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths
