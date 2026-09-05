import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardState

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

/-!
# Located paths for the compact exact guard

Instruction indices 2925--2973 are the 49-instruction, 116-byte suffix.  One
17-instruction loop checks the 31 identical full words; the padded last word
is checked once after loop exit.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardPaths

open EvmSemantics
open EvmSemantics.EVM
open ExactGuardData ExactGuardSpec

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def preludePath : List Located :=
  [⟨2925, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2926, .push ⟨1, by decide⟩ (UInt256.ofNat 255), by rfl, by decide⟩,
   ⟨2927, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨2928, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2929, .op .DIV, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2930, .push ⟨1, by decide⟩ (UInt256.ofNat 97), by rfl, by decide⟩,
   ⟨2931, .op .MUL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2932, .push ⟨2, by decide⟩ (UInt256.ofNat 1000), by rfl, by decide⟩,
   ⟨2933, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2934, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2935, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨2936, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩]

def loopPath : List Located :=
  [⟨2937, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2938, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2939, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2940, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2941, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2942, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2943, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2944, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2945, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2946, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2947, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2948, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2949, .push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨2950, .op .GT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2951, .push ⟨2, by decide⟩ (UInt256.ofNat 5309), by rfl, by decide⟩,
   ⟨2952, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def exitPath : List Located :=
  [⟨2953, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2954, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def tailPath : List Located :=
  [⟨2955, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2956, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨2957, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2958, .push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨2959, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2960, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2961, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩]

def cleanupPath : List Located :=
  [⟨2962, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2963, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def branchIsZeroPath : List Located :=
  []

def branchPushPath : List Located :=
  [⟨2964, .push ⟨2, by decide⟩ (UInt256.ofNat 1006), by rfl, by decide⟩]

def branchJumpPath : List Located :=
  [⟨2965, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fallbackPath : List Located :=
  []

def returnPath : List Located :=
  [⟨2966, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2967, .push ⟨20, by decide⟩ (UInt256.ofNat 972889429405991776604892044862621566948497025487), by rfl, by decide⟩,
   ⟨2968, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨2969, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2970, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2971, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨2972, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem guardPC (i : Nat) (hlo : 2925 ≤ i) (hhi : i ≤ 2973) :
    Artifact.submissionArtifact.instructionPC i =
      [5293, 5294, 5296, 5297, 5298, 5299, 5301, 5302, 5305, 5306, 5307, 5308, 5309, 5310, 5311, 5312, 5313, 5314, 5315, 5316, 5317, 5319, 5320, 5321, 5322, 5325, 5326, 5329, 5330, 5331, 5332, 5333, 5335, 5336, 5339, 5340, 5341, 5342, 5343, 5344, 5347, 5348, 5349, 5370, 5371, 5372, 5374, 5375, 5376][i - 2925]! := by
  interval_cases i <;> rw [StackPC.instructionPC_eq_byteLength] <;> decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardPaths
