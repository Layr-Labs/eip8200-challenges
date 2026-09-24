import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 119 rho)
    (atState s 208 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 208 (frame f rho))
    (atState s (if 219 < f.full.toNat then 241 else 215) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 215 (frame f rho))
    (atState s 235 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 235 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 215 else 241) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 241 (frame f rho))
    (atState s 254 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 254 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 538 else 261) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 261 (frame f rho))
    (atState s 297 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 297 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 215 else 303) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 303 (frame f rho)) (atState s 241 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 538 (frame f rho))
    (atState s (if f.acc.toNat=0 then 543 else 565) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
