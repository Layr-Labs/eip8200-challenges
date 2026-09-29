import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 4799 rho)
    (atState s 4888 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 4888 (frame f rho))
    (atState s (if 219 < f.full.toNat then 4923 else 4896) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 4896 (frame f rho))
    (atState s 4916 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 4916 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4896 else 4923) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 4923 (frame f rho))
    (atState s 4936 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4936 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 4943 else 4638) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4638 (frame f rho))
    (atState s 4675 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 4675 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4896 else 4682) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 4682 (frame f rho)) (atState s 4923 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4943 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4946 else 246) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
