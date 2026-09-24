import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 4796 rho)
    (atState s 4885 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) : GasSteps (atState s 4885 (frame f rho))
    (atState s (if 219 < f.full.toNat then 4920 else 4893) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 4893 (frame f rho))
    (atState s 4913 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 4913 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4893 else 4920) (frame f rho))
  tail (f : J2Raw.Frame) : GasSteps (atState s 4920 (frame f rho))
    (atState s 4933 (frame (tailResult s f) rho))
  finish (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4933 (frame f rho))
    (atState s (if f.stop.toNat=f.len.toNat then 4940 else 4633) (frame f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4633 (frame f rho))
    (atState s 4670 (frame (transitionResult f) rho))
  transitionGuard (f : J2Raw.Frame) : GasSteps (atState s 4670 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4893 else 4677) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 4677 (frame f rho)) (atState s 4920 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4940 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4943 else 246) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
