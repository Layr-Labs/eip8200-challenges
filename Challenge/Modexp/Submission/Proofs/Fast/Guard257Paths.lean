import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2139 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2140 0 0,
   Main.pushAt 2141 1 163,
   Main.opAt 2142 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 2143 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2144 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2145 32 33,
   Main.pushAt 2146 0 0,
   Main.opAt 2147 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2148 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2149 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2150 32 1,
   Main.pushAt 2151 1 32,
   Main.opAt 2152 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2153 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2154 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2155 32 33,
   Main.pushAt 2156 1 64,
   Main.opAt 2157 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2158 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2159 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2160 32 452312848583266388373324160190187140051835877600158453279131187530910662656,
   Main.pushAt 2161 1 96,
   Main.opAt 2162 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2163 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2164 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2165 32 2266871685857013885419158128209026732832114290800391293656575918782654971904,
   Main.pushAt 2166 1 128,
   Main.opAt 2167 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2168 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2169 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2170 32 48312224427533946512043291035939178167157762805192705886137669566595072,
   Main.pushAt 2171 1 160,
   Main.opAt 2172 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2173 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2174 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated := Main.opAt 2175 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))
def branchPushLocated := Main.pushAt 2176 2 5081
def branchJumpLocated := Main.opAt 2177 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
def branchIsZeroPath := [branchIsZeroLocated]
def branchJumpPath := [branchPushLocated, branchJumpLocated]

def fallbackPushLocated := Main.pushAt 2178 2 5157
def fallbackJumpLocated := Main.opAt 2179 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fallbackPushLocated, fallbackJumpLocated]

@[simp] theorem fallbackPush_index : fallbackPushLocated.index = 2178 := rfl
@[simp] theorem fallbackPush_instruction :
    fallbackPushLocated.instruction = .push 2 (UInt256.ofNat 5157) := rfl
@[simp] theorem fallbackJump_index : fallbackJumpLocated.index = 2179 := rfl
@[simp] theorem fallbackJump_instruction : fallbackJumpLocated.instruction = .op .JUMP := rfl

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2180 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2181 32 452312848583266388373324160190187140051835877600158453279131187530910662655,
   Main.pushAt 2182 0 0,
   Main.opAt 2183 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2184 32 115339776388732929035197660848497720713218148788040405586178452820382218977280,
   Main.pushAt 2185 1 32,
   Main.opAt 2186 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2187 1 33,
   Main.pushAt 2188 0 0,
   Main.opAt 2189 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guardPC0 (i : Nat) (hlo : 2139 ≤ i) (hhi : i ≤ 2173) :
    Artifact.submissionArtifact.instructionPC i =
      [4838,4839,4840,4842,4843,4844,4845,4878,4879,4880,4881,4882,4915,4917,4918,4919,4920,4953,4955,4956,4957,4958,4991,4993,4994,4995,4996,5029,5031,5032,5033,5034,5067,5069,5070][i - 2139]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC1 (i : Nat) (hlo : 2174 ≤ i) (hhi : i ≤ 2189) :
    Artifact.submissionArtifact.instructionPC i =
      [5071,5072,5073,5076,5077,5080,5081,5082,5115,5116,5117,5150,5152,5153,5155,5156][i - 2174]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths
