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
    (atState s 4877 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps (atState s 4877 (frame f rho))
    (atState s (if f.len.toNat < 33 then 4910 else 4885) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 4885 (frame f rho))
    (atState s 4903 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 4903 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4885 else 4910) (frame f rho))
  tailFinal (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat = f.len.toNat) :
    GasSteps (atState s 4910 (frame f rho)) (atState s 4930 (frame (tailResult s f) rho))
  tailBoundary (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat ≠ f.len.toNat)
      (hshift : UInt256.shiftLeft (UInt256.sub f.off f.full) (UInt256.ofNat 3) = UInt256.ofNat 40) :
    GasSteps (atState s 4910 (frame f rho)) (atState s 4552 (frame (tailResult s f) rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4552 (frame f rho))
    (atState s 4588 (f.off :: frame (transitionResult f) rho))
  transitionGuard (x : UInt256) (f : J2Raw.Frame) : GasSteps (atState s 4588 (x :: frame f rho))
    (atState s (if x.toNat<f.full.toNat then 4885 else 4594) (frame f rho))
  toTail (f : J2Raw.Frame) : GasSteps (atState s 4594 (frame f rho)) (atState s 4910 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4930 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4934 else 4955) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
