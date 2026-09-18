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
    (atState s 190 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 190 (frame f rho))
    (atState s (if f.full.toNat=0 then 224 else 195) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 195 (frame f rho))
    (atState s 217 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 217 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 195 else 224) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 224 (frame f rho))
    (atState s 241 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 241 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 300 else 248) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 248 (frame f rho))
    (atState s 291 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 291 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 195 else 297) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 297 (frame f rho)) (atState s 224 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 300 (frame f rho))
    (atState s (if f.acc.toNat=0 then 305 else 342) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
