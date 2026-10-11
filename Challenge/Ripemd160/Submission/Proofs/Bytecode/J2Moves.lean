import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
    (atState s 4878 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps (atState s 4878 (frame f rho))
    (atState s (if f.len.toNat < 33 then 4913 else 4886) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 4886 (frame f rho))
    (atState s 4906 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 4906 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4886 else 4913) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 4913 (frame f rho))
    (atState s 4926 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4926 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 4934 else 4638) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4638 (frame f rho))
    (atState s 4679 (f.off :: frame (transitionResult f) rho))
  transitionGuard (x : UInt256) (f : J2Raw.Frame) : GasSteps (atState s 4679 (x :: frame f rho))
    (atState s (if x.toNat<f.full.toNat then 4886 else 4685) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 4685 (frame f rho)) (atState s 4913 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4934 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4937 else 246) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
