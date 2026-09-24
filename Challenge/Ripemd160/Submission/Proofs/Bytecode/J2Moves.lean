import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 250 rho)
    (atState s 339 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 339 (frame f rho))
    (atState s (if 219 < f.full.toNat then 375 else 347) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 347 (frame f rho))
    (atState s 367 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 367 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 347 else 375) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 375 (frame f rho))
    (atState s 388 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 388 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 4823 else 395) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 395 (frame f rho))
    (atState s 432 (frame (transitionResult f) rho))
  toGuard (f : J2Raw.Frame) : GasSteps (atState s 432 (frame f rho)) (atState s 367 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4823 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4828 else 436) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
