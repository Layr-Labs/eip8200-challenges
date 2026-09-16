import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def cacheProgram : List Instr :=
  -- E5, new indices 1872..1880 (pcs 2531..2545): `DUP1 PUSH1 4 EQ PUSH1 0x91 MUL PUSH2 2682 ADD
  -- PUSH2 0x6a2 MSTORE`.  The leading `DUP2` of the E5 region is instruction 1871 and belongs to
  -- `blk2982`, exactly as the old `DUP2` at old index 2079 did.
  [.op (.Dup { idx := 0 }),
   .push 1 4,
   .op .EQ,
   .push 1 145,
   .op .MUL,
   .push 2 2682,
   .op .ADD,
   .push 2 1698,
   .op .MSTORE]

def cache : Block Artifact.submissionArtifact .Osaka 2531 cacheProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 1870 9 2531 cacheProgram
    (by decide) (by rfl) (by rfl) (by decide)

#print axioms cache
end Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
