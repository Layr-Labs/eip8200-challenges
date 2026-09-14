import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 113 rho)
    (atState s 184 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 184 (frame f rho))
    (atState s (if f.full.toNat=0 then 219 else 190) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 190 (frame f rho))
    (atState s 213 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 213 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 190 else 219) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 219 (frame f rho))
    (atState s 237 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) : GasSteps (atState s 237 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 298 else 244) (frame f rho))
  transition (f : J2Raw.Frame) : GasSteps (atState s 244 (frame f rho))
    (atState s 288 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 288 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 190 else 294) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 294 (frame f rho)) (atState s 219 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 298 (frame f rho))
    (atState s (if f.acc.toNat=0 then 303 else 341) (finishRest f rho))
  cleanup (f : J2Raw.Frame) : GasSteps (atState s 341 (finishRest f rho)) (atState s 352 rho)
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
