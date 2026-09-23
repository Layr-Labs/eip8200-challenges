import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 123 rho)
    (atState s 188 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 188 (frame f rho))
    (atState s (if f.full.toNat=0 then 220 else 193) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 193 (frame f rho))
    (atState s 214 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 214 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 193 else 220) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 220 (frame f rho))
    (atState s 237 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 237 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 4699 else 244) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 244 (frame f rho))
    (atState s 287 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 287 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 193 else 293) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 293 (frame f rho)) (atState s 220 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4699 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4704 else 310) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
