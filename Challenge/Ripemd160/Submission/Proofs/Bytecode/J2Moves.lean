import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 4797 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
    (atState s 4871 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps (atState s 4871 (frame f rho))
    (atState s (if f.len.toNat < 33 then 4905 else 4879) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 4879 (frame f rho))
    (atState s 4898 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 4898 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4879 else 4905) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 4905 (frame f rho))
    (atState s 4918 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4918 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 4925 else 4553) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4553 (frame f rho))
    (atState s 4591 (f.off :: frame (transitionResult f) rho))
  transitionGuard (x : UInt256) (f : J2Raw.Frame) : GasSteps (atState s 4591 (x :: frame f rho))
    (atState s (if x.toNat<f.full.toNat then 4879 else 4597) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 4597 (frame f rho)) (atState s 4905 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4925 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4928 else 245) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
