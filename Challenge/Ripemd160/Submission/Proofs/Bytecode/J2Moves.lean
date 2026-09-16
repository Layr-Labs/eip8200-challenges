import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 112 rho)
    (atState s 183 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 183 (frame f rho))
    (atState s (if f.full.toNat=0 then 217 else 188) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 188 (frame f rho))
    (atState s 211 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 211 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 188 else 217) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 217 (frame f rho))
    (atState s 235 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 235 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 292 else 242) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 242 (frame f rho))
    (atState s 283 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 283 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 188 else 289) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 289 (frame f rho)) (atState s 217 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 292 (frame f rho))
    (atState s (if f.acc.toNat=0 then 297 else 336) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
