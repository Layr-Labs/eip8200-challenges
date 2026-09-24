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
    (atState s 313 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 313 (frame f rho))
    (atState s (if 219 < f.full.toNat then 348 else 321) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 321 (frame f rho))
    (atState s 341 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 341 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 321 else 348) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 348 (frame f rho))
    (atState s 361 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 361 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 540 else 368) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 368 (frame f rho))
    (atState s 403 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 403 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 321 else 410) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 410 (frame f rho)) (atState s 348 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 540 (frame f rho))
    (atState s (if f.acc.toNat=0 then 545 else 568) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
