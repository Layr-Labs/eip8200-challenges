import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 111 rho)
    (atState s 182 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 182 (frame f rho))
    (atState s (if f.full.toNat=0 then 216 else 187) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 187 (frame f rho))
    (atState s 210 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 210 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 187 else 216) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 216 (frame f rho))
    (atState s 234 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 234 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 294 else 241) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 241 (frame f rho))
    (atState s 285 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 285 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 187 else 291) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 291 (frame f rho)) (atState s 216 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 294 (frame f rho))
    (atState s (if f.acc.toNat=0 then 299 else 337) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
