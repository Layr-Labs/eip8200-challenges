import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordExpRuns
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace CycleSubmission.Global.WordLoops
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open Word

/-- The unrolled block leaves the terminal counter at eight; the byte-loop tail
pops that dead slot before the next byte pushes its own fresh zero. -/
def bitFinishDispatchState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with pc := UInt256.ofNat 3966 }

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
    (by exact CycleSubmission.Global.Binding.jumpDest 3065 (by rfl))

end CycleSubmission.Global.WordLoops
