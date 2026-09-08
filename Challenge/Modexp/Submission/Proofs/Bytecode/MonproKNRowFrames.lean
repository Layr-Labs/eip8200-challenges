import Challenge.Modexp.Submission.Proofs.Fast.MonproRowModel
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowFrames

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open MonproKNCache

def entry (s : State) (mem : ByteArray) (pa pb : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, dst, ret] ++ rest
           memory := mem }

def outer (s : State) (mem : ByteArray) (pa pb n i : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1982
           stack := [UInt256.ofNat (ptrAt (pb + 32*n - 32) i),
             UInt256.ofNat (pa-32), UInt256.ofNat (pb-32), negative32, allOnes, dst, ret] ++ rest
           memory := mem }

def l1 (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j pc : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (pa+32*n-32) j),
             UInt256.ofNat (ptrAt (8224+32*n) j), (l1Step mem bi pa n j).carry, bi,
             UInt256.ofNat (ptrAt (pb+32*n-32) i), UInt256.ofNat (pa-32),
             UInt256.ofNat (pb-32), negative32, allOnes, dst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

def middle (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2008
           stack := [paj, ptj, c, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
             UInt256.ofNat (pa-32), UInt256.ofNat (pb-32), negative32, allOnes, dst, ret] ++ rest
           memory := mem }

def l2 (s : State) (mem : ByteArray) (bi mu c0 : UInt256) (pa pb n i k pc : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (32*n-64) k),
             UInt256.ofNat (ptrAt (8192+32*n) k), (l2Step mem mu c0 n k).carry, mu, bi,
             UInt256.ofNat (ptrAt (pb+32*n-32) i), UInt256.ofNat (pa-32),
             UInt256.ofNat (pb-32), negative32, allOnes, dst, ret] ++ rest
           memory := (l2Step mem mu c0 n k).memory }

def tail (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2435
           stack := [pmj, ptj, c, mu, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
             UInt256.ofNat (pa-32), UInt256.ofNat (pb-32), negative32, allOnes, dst, ret] ++ rest
           memory := mem }

def exit (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2471
           stack := [pbi, UInt256.ofNat (pa-32), UInt256.ofNat (pb-32),
             negative32, allOnes, dst, ret] ++ rest
           memory := mem }

def csub (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2655
           stack := [dst, ret] ++ rest
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowFrames
