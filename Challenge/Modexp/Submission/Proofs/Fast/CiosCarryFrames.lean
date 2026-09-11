import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached
variable {carrySlot : UInt256}

def l1Target (n : Nat) : UInt256 :=
  UInt256.ofNat 4280 + UInt256.ofNat 153 * isFour n

def l2Target (n : Nat) : UInt256 :=
  UInt256.ofNat 4567 + UInt256.ofNat 153 * isFour n

@[simp] theorem l1Target_four : l1Target 4 = UInt256.ofNat 4433 := by decide
@[simp] theorem l1Target_eight : l1Target 8 = UInt256.ofNat 4280 := by decide
@[simp] theorem l2Target_four : l2Target 4 = UInt256.ofNat 4720 := by decide
@[simp] theorem l2Target_eight : l2Target 8 = UInt256.ofNat 4567 := by decide

/-- Before first-loop step `j`: carry and `b_i` above the honest cached base. -/
def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [(l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, carrySlot, allOnes, l2Target n, pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

/-- Row head before the first product; no dummy carry occupies the stack. -/
def firstAt (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
             UInt256.ofNat pa, UInt256.ofNat (pb-32), l1Target n,
             carrySlot, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

/-- Before second-loop step `k` of row `i`: only the carry and `mu` above
`b_i` and the row frame. -/
def l2At (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [(l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, carrySlot, allOnes, l2Target n, pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

def entryState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4163
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

def outState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4252
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, carrySlot, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

/-- After the first loop: the carry and `b_i` above the row frame. -/
def midState (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4537
           stack := [c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, carrySlot, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

/-- After the second loop: the carry, `mu` and `b_i` above the row frame. -/
def tailState (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4828
           stack := [c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, carrySlot, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }


end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
