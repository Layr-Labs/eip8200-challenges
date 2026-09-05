import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardState

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

/-!
# Located paths for the compact exact guard

Instruction indices 2925--2971 are the 47-instruction, 145-byte suffix.  One
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

/-- Establish `[acc0, 0, fullWord]` at the loop header. -/
def preludePath : List Located :=
  [⟨2925, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2926, .push ⟨32, by decide⟩ fullWord, by rfl, by decide⟩,
   ⟨2927, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2928, .push ⟨2, by decide⟩ (UInt256.ofNat 1000), by rfl, by decide⟩,
   ⟨2929, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2930, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2931, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2932, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2933, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩]

/-- Check the word at the current offset, add 32, and loop until offset 992. -/
def loopPath : List Located :=
  [⟨2934, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2935, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2936, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2937, .op (.Dup ⟨3, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2938, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2939, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2940, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2941, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2942, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2943, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2944, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2945, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2946, .push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨2947, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2948, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2949, .push ⟨2, by decide⟩ (UInt256.ofNat 0x14d8),
      by rfl, by decide⟩,
   ⟨2950, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Drop the terminal loop offset, leaving `[acc31, fullWord]`. -/
def exitPath : List Located :=
  [⟨2951, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2952, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Check the padded word at offset 992. -/
def tailPath : List Located :=
  [⟨2953, .push ⟨32, by decide⟩ tailWord, by rfl, by decide⟩,
   ⟨2954, .push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨2955, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2956, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2957, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Remove the shared full-word constant, leaving only `guardDiff`. -/
def cleanupPath : List Located :=
  [⟨2958, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2959, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def branchIsZeroPath : List Located :=
  [⟨2960, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩]

def branchPushPath : List Located :=
  [⟨2961, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1522),
      by rfl, by decide⟩]

def branchJumpPath : List Located :=
  [⟨2962, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fallbackPath : List Located :=
  [⟨2963, .push ⟨2, by decide⟩ (UInt256.ofNat 0x03ee),
      by rfl, by decide⟩,
   ⟨2964, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def returnPath : List Located :=
  [⟨2965, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2966, .push ⟨20, by decide⟩ paddedDigestWord, by rfl, by decide⟩,
   ⟨2967, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2968, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2969, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2970, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2971, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached PCs for the complete guard suffix, including its end boundary. -/
@[simp] theorem guardPC (i : Nat) (hlo : 2925 ≤ i) (hhi : i ≤ 2972) :
    Artifact.submissionArtifact.instructionPC i =
      [0x14ad, 0x14ae, 0x14cf, 0x14d0, 0x14d3, 0x14d4, 0x14d5,
       0x14d6, 0x14d7, 0x14d8, 0x14d9, 0x14da, 0x14db, 0x14dc,
       0x14dd, 0x14de, 0x14df, 0x14e0, 0x14e2, 0x14e3, 0x14e4,
       0x14e5, 0x14e8, 0x14e9, 0x14ea, 0x14ed, 0x14ee, 0x14ef,
       0x14f0, 0x1511, 0x1514, 0x1515, 0x1516, 0x1517, 0x1518,
       0x1519, 0x151a, 0x151d, 0x151e, 0x1521, 0x1522, 0x1523,
       0x1538, 0x1539, 0x153a, 0x153c, 0x153d, 0x153e][i - 2925]! := by
  interval_cases i <;>
    rw [StackPC.instructionPC_eq_byteLength] <;> decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardPaths
