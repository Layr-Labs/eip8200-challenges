import Challenge.Modexp.Submission.Proofs.Bytecode.WordExpRuns
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

/-- The unrolled block leaves the terminal counter at eight; the byte-loop tail
pops that dead slot before the next byte pushes its own fresh zero. -/
def bitFinishDispatchState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with pc := UInt256.ofNat 212 }

/-- The tail of the block drops `base - 1` and rejoins the byte loop. -/
def gasSteps_bitExit (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 8 byte offset acc base)
      (bitFinishDispatchState input outer byte offset acc base) :=
  WordEnds.gasSteps_bitExit_sym (bitLoopState input outer 0 byte offset acc base)
    (bitTail input) (base - UInt256.ofNat 1) (UInt256.ofNat 8) byte offset
    (UInt256.ofNat outer) acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])
    (by exact Artifact.isValidJumpDest_index 143 (by rfl))

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
