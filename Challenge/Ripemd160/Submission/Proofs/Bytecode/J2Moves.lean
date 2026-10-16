import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedAccumulator
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Raw

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

/-- The scanner's located moves. The word chain is the seven blocks `blockPC j` (`j < 7`), each falling into
the next; `blockPC 7 = 5017` is the tail. Both segment entries are computed jumps into the chain. -/
def fusedPC : Nat := 5052
def fusedReturnPC : Nat := 5064
def non256PC : Nat := 5067

def fusedAcc (s : State) (f : J2Raw.Frame) : UInt256 :=
  UInt256.lor (UInt256.xor (tailDiff s f) J2FusedAccumulator.correction) f.acc

structure Moves (s : State) (rho : List UInt256) where
  init : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
    (atState s 4877 (frame (initResult s.executionEnv.calldata.size) rho))
  first (f : J2Raw.Frame) (j : Nat) (hj : j ≤ 7)
      (ht : dispatchTarget (UInt256.ofNat 0) f.full = UInt256.ofNat (blockPC j)) :
    GasSteps (atState s 4877 (frame f rho)) (atState s (blockPC j) (frame f rho))
  normal (j : Nat) (hj : j < 7) (f : J2Raw.Frame) : GasSteps (atState s (blockPC j) (frame f rho))
    (atState s (blockPC (j+1)) (frame (normalResult s f) rho))
  tailFinal (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat = f.len.toNat) :
    GasSteps (atState s 5017 (frame f rho)) (atState s 5037 (frame (tailResult s f) rho))
  tailBoundary (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat ≠ f.len.toNat)
      (hn256 : s.executionEnv.calldata.size ≠ 256)
      (hmask : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 ≠ 0)
      (hshift : UInt256.shiftLeft (UInt256.sub f.off f.full) (UInt256.ofNat 3) = UInt256.ofNat 40) :
    GasSteps (atState s 5017 (frame f rho)) (atState s 5072 (frame (tailResult s f) rho))
  fusedBoundary (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
      (hfinal : f.stop.toNat ≠ f.len.toNat) (h256 : s.executionEnv.calldata.size = 256) :
    GasSteps (atState s 5017 (frame f rho))
      (atState s (if (fusedAcc s f).toNat = 0 then fusedReturnPC else 4565) (finishRest f rho))
  transition (f : J2Raw.Frame) (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) : GasSteps (atState s 5072 (frame f rho))
    (atState s 5108 (f.off :: frame (transitionResult f) rho))
  dispatch (x : UInt256) (f : J2Raw.Frame) (j : Nat) (hj : j ≤ 7)
      (ht : dispatchTarget f.off f.full = UInt256.ofNat (blockPC j)) :
    GasSteps (atState s 5108 (x :: frame f rho)) (atState s (blockPC j) (frame f rho))
  result (f : J2Raw.Frame) : GasSteps (atState s 5037 (frame f rho))
    (atState s (if f.acc.toNat=0 then 5041 else 4565) (finishRest f rho))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
