import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedAccumulator
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

/-- New PCs are the unreordered, locally expanded fusion block.  Relocate these
separately from the original-baseline numeric PCs in the rest of this module. -/
def fusedPC : Nat := 4759
def fusedReturnPC : Nat := 4771
def non256PC : Nat := 4774

def fusedAcc (s : State) (f : J2Raw.Frame) : UInt256 :=
  UInt256.lor (UInt256.xor (tailDiff s f) J2FusedAccumulator.correction) f.acc

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 4618 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
    (atState s 4691 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps (atState s 4691 (frame f rho))
    (atState s (if f.len.toNat < 33 then 4724 else 4699) (frame f rho))
  normal (f : J2Raw.Frame) : GasSteps (atState s 4699 (frame f rho))
    (atState s 4717 (frame (normalResult s f) rho))
  normalGuard (f : J2Raw.Frame) : GasSteps (atState s 4717 (frame f rho))
    (atState s (if f.off.toNat<f.full.toNat then 4699 else 4724) (frame f rho))
  tailFinal (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat = f.len.toNat) :
    GasSteps (atState s 4724 (frame f rho)) (atState s 4744 (frame (tailResult s f) rho))
  tailBoundary (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat ≠ f.len.toNat)
        (hn256 : s.executionEnv.calldata.size ≠ 256)
        (hmask : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 ≠ 0)
      (hshift : UInt256.shiftLeft (UInt256.sub f.off f.full) (UInt256.ofNat 3) = UInt256.ofNat 40) :
    GasSteps (atState s 4724 (frame f rho)) (atState s 4779 (frame (tailResult s f) rho))
  fusedBoundary (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat ≠ f.len.toNat) (h256 : s.executionEnv.calldata.size = 256) :
    GasSteps (atState s 4724 (frame f rho))
      (atState s (if (fusedAcc s f).toNat = 0 then fusedReturnPC else 4838) (finishRest f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 4779 (frame f rho))
    (atState s 4815 (f.off :: frame (transitionResult f) rho))
  transitionGuard (x : UInt256) (f : J2Raw.Frame) : GasSteps (atState s 4815 (x :: frame f rho))
    (atState s 4699 (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 4744 (frame f rho))
    (atState s (if f.acc.toNat=0 then 4748 else 4838) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
