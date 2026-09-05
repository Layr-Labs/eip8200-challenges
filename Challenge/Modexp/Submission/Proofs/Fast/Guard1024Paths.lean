import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Paths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2052 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2053 0 0,
   Main.pushAt 2054 2 353,
   Main.opAt 2055 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 2056 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2057 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2058 32 128,
   Main.pushAt 2059 0 0,
   Main.opAt 2060 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2061 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2062 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2063 32 1,
   Main.pushAt 2064 1 32,
   Main.opAt 2065 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2066 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2067 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2068 32 128,
   Main.pushAt 2069 1 64,
   Main.opAt 2070 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2071 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2072 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2073 32 8793306660163990040561289890486148164325486782586370684446629828706317024479,
   Main.pushAt 2074 1 96,
   Main.opAt 2075 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2076 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2077 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2078 32 44513626964103848159171604930358580559684327884685485523541937090475774086062,
   Main.pushAt 2079 1 128,
   Main.opAt 2080 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2081 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2082 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2083 32 13735552034596734314392003083933777828981134616265434527816408455772068535085,
   Main.pushAt 2084 1 160,
   Main.opAt 2085 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2086 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2087 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2088 32 20741756277002281002578156983727958327059860011036567020672535493562176622834,
   Main.pushAt 2089 1 192,
   Main.opAt 2090 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2091 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2092 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2093 32 1669349634595236858291517537149291117455193199261270936918514663252800326893,
   Main.pushAt 2094 1 224,
   Main.opAt 2095 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2096 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2097 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2098 32 99117046946972186913022966043064609353311784182601608842001214174495081049617,
   Main.pushAt 2099 2 256,
   Main.opAt 2100 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2101 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2102 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2103 32 33420266142682261421808456191225212768240439756117012645431084487760459509359,
   Main.pushAt 2104 2 288,
   Main.opAt 2105 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2106 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2107 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2108 32 63069685324986315081589603195175474010237415761785462502555456014205811395170,
   Main.pushAt 2109 2 320,
   Main.opAt 2110 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2111 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2112 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2113 32 28495709460745782467519422091981789823265660288809982556585264814447371747328,
   Main.pushAt 2114 2 352,
   Main.opAt 2115 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2116 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2117 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated := Main.opAt 2118 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))
def branchPushLocated := Main.pushAt 2119 2 4690
def branchJumpLocated := Main.opAt 2120 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
def branchIsZeroPath := [branchIsZeroLocated]
def branchJumpPath := [branchPushLocated, branchJumpLocated]

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 2121 2 1314,
   Main.opAt 2122 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2123 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2124 32 15311000363910303241540621865409679537502595890653539278795210471371740305479,
   Main.pushAt 2125 0 0,
   Main.opAt 2126 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2127 32 108131171086235498843144070769070390205391711722934919355131028315980221287783,
   Main.pushAt 2128 1 32,
   Main.opAt 2129 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2130 32 30211351789909815513928503188859640991933128769084385520359151767836288201668,
   Main.pushAt 2131 1 64,
   Main.opAt 2132 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2133 32 19240783075872300903671752229116273808210541663683986574655295206487138977467,
   Main.pushAt 2134 1 96,
   Main.opAt 2135 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2136 1 128,
   Main.pushAt 2137 0 0,
   Main.opAt 2138 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guardPC0 (i : Nat) (hlo : 2052 ≤ i) (hhi : i ≤ 2086) :
    Artifact.submissionArtifact.instructionPC i =
      [4214,4215,4216,4219,4220,4221,4222,4255,4256,4257,4258,4259,4292,4294,4295,4296,4297,4330,4332,4333,4334,4335,4368,4370,4371,4372,4373,4406,4408,4409,4410,4411,4444,4446,4447][i - 2052]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC1 (i : Nat) (hlo : 2087 ≤ i) (hhi : i ≤ 2121) :
    Artifact.submissionArtifact.instructionPC i =
      [4448,4449,4482,4484,4485,4486,4487,4520,4522,4523,4524,4525,4558,4561,4562,4563,4564,4597,4600,4601,4602,4603,4636,4639,4640,4641,4642,4675,4678,4679,4680,4681,4682,4685,4686][i - 2087]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC2 (i : Nat) (hlo : 2122 ≤ i) (hhi : i ≤ 2138) :
    Artifact.submissionArtifact.instructionPC i =
      [4689,4690,4691,4724,4725,4726,4759,4761,4762,4795,4797,4798,4831,4833,4834,4836,4837][i - 2122]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Paths
