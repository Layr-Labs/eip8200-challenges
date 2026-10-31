import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSteps
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory

set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def zeroTn : UInt256 := UInt256.ofNat 0

def l1Target (_n : Nat) : UInt256 := UInt256.ofNat 3347

def setupState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 3182
    memory := mem
    stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, dst, ret] ++ rest}

def outState (s : State) (mem : ByteArray) (pb n i : Nat)
    (hd ent w5 inv m0 : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := hd
    memory := mem
    stack := [UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32),
      ent, w5, allOnes, UInt256.ofNat 0, inv, m0] ++ rest}
end Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup
