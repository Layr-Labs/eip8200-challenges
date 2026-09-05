import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2190 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2191 0 0,
   Main.pushAt 2192 1 160,
   Main.opAt 2193 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 2194 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2195 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2196 32 0,
   Main.pushAt 2197 0 0,
   Main.opAt 2198 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2199 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2200 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2201 32 32,
   Main.pushAt 2202 1 32,
   Main.opAt 2203 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2204 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2205 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2206 32 32,
   Main.pushAt 2207 1 64,
   Main.opAt 2208 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2209 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2210 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2211 32 115792089237316195423570985008687907853269984665640564039457584007908834671662,
   Main.pushAt 2212 1 96,
   Main.opAt 2213 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2214 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2215 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2216 32 115792089237316195423570985008687907853269984665640564039457584007908834671663,
   Main.pushAt 2217 1 128,
   Main.opAt 2218 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2219 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2220 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated := Main.opAt 2221 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))
def branchPushLocated := Main.pushAt 2222 2 5362
def branchJumpLocated := Main.opAt 2223 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
def branchIsZeroPath := [branchIsZeroLocated]
def branchJumpPath := [branchPushLocated, branchJumpLocated]

def fallbackPushLocated := Main.pushAt 2224 2 1314
def fallbackJumpLocated := Main.opAt 2225 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fallbackPushLocated, fallbackJumpLocated]

@[simp] theorem fallbackPush_index : fallbackPushLocated.index = 2224 := rfl
@[simp] theorem fallbackPush_instruction :
    fallbackPushLocated.instruction = .push 2 (UInt256.ofNat 1314) := rfl
@[simp] theorem fallbackJump_index : fallbackJumpLocated.index = 2225 := rfl
@[simp] theorem fallbackJump_instruction : fallbackJumpLocated.instruction = .op .JUMP := rfl

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2226 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2227 32 0,
   Main.pushAt 2228 0 0,
   Main.opAt 2229 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2230 1 32,
   Main.pushAt 2231 0 0,
   Main.opAt 2232 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guardPC0 (i : Nat) (hlo : 2190 ≤ i) (hhi : i ≤ 2224) :
    Artifact.submissionArtifact.instructionPC i =
      [5157,5158,5159,5161,5162,5163,5164,5197,5198,5199,5200,5201,5234,5236,5237,5238,5239,5272,5274,5275,5276,5277,5310,5312,5313,5314,5315,5348,5350,5351,5352,5353,5354,5357,5358][i - 2190]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC1 (i : Nat) (hlo : 2225 ≤ i) (hhi : i ≤ 2232) :
    Artifact.submissionArtifact.instructionPC i =
      [5361,5362,5363,5396,5397,5398,5400,5401][i - 2225]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths
