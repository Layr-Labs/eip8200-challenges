import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardState

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

/-!
# Located paths for the compact exact guard

Instruction indices 2161--2207 are the 47-instruction, 145-byte suffix.  One
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
  [⟨2161, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2162, .push ⟨32, by decide⟩ fullWord, by rfl, by decide⟩,
   ⟨2163, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2164, .push ⟨2, by decide⟩ (UInt256.ofNat 1000), by rfl, by decide⟩,
   ⟨2165, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2166, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2167, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2168, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2169, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩]

/-- Check the word at the current offset, add 32, and loop until offset 992. -/
def loopPath : List Located :=
  [⟨2170, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2171, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2172, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2173, .op (.Dup ⟨3, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2174, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2175, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2176, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2177, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2178, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2179, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2180, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2181, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2182, .push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨2183, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2184, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2185, .push ⟨2, by decide⟩ (UInt256.ofNat 0x14bd),
      by rfl, by decide⟩,
   ⟨2186, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Drop the terminal loop offset, leaving `[acc31, fullWord]`. -/
def exitPath : List Located :=
  [⟨2187, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2188, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Check the padded word at offset 992. -/
def tailPath : List Located :=
  [⟨2189, .push ⟨32, by decide⟩ tailWord, by rfl, by decide⟩,
   ⟨2190, .push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨2191, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2192, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2193, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Remove the shared full-word constant, leaving only `guardDiff`. -/
def cleanupPath : List Located :=
  [⟨2194, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨2195, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def branchIsZeroPath : List Located :=
  [⟨2196, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩]

def branchPushPath : List Located :=
  [⟨2197, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1507),
      by rfl, by decide⟩]

def branchJumpPath : List Located :=
  [⟨2198, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fallbackPath : List Located :=
  [⟨2199, .push ⟨2, by decide⟩ (UInt256.ofNat 0x03ee),
      by rfl, by decide⟩,
   ⟨2200, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def returnPath : List Located :=
  [⟨2201, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2202, .push ⟨20, by decide⟩ paddedDigestWord, by rfl, by decide⟩,
   ⟨2203, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2204, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2205, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2206, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨2207, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached PCs for the complete guard suffix, including its end boundary. -/
@[simp] theorem guardPC (i : Nat) (hlo : 2161 ≤ i) (hhi : i ≤ 2208) :
    Artifact.submissionArtifact.instructionPC i =
      [0x1492, 0x1493, 0x14b4, 0x14b5, 0x14b8, 0x14b9, 0x14ba,
       0x14bb, 0x14bc, 0x14bd, 0x14be, 0x14bf, 0x14c0, 0x14c1,
       0x14c2, 0x14c3, 0x14c4, 0x14c5, 0x14c7, 0x14c8, 0x14c9,
       0x14ca, 0x14cd, 0x14ce, 0x14cf, 0x14d2, 0x14d3, 0x14d4,
       0x14d5, 0x14f6, 0x14f9, 0x14fa, 0x14fb, 0x14fc, 0x14fd,
       0x14fe, 0x14ff, 0x1502, 0x1503, 0x1506, 0x1507, 0x1508,
       0x151d, 0x151e, 0x151f, 0x1521, 0x1522, 0x1523][i - 2161]! := by
  interval_cases i <;> decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardPaths
