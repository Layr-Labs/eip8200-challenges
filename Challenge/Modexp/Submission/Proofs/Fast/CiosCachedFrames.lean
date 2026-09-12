import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

def negative32 : UInt256 := UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904
def allOnes : UInt256 := UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935
def isFour (n : Nat) : UInt256 :=
  UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat (32*n))

@[simp] theorem isFour_four : isFour 4 = UInt256.ofNat 1 := by decide
@[simp] theorem isFour_eight : isFour 8 = UInt256.ofNat 0 := by decide


/-- First-loop entry of the multiply rows (frame slot `ent`): the setup computes
`0x0fe4 + 0x98 * [n = 4]` (k1 JUMPDEST for eight limbs, k5 JUMPDEST for four). -/
def l1Target (n : Nat) : UInt256 :=
  UInt256.ofNat 4019 + UInt256.ofNat 152 * isFour n

/-- Second-loop entry (`ent + 0x12b`), fixed for the whole kernel call. -/
def l2Target (n : Nat) : UInt256 :=
  UInt256.ofNat 4318 + UInt256.ofNat 152 * isFour n

@[simp] theorem l1Target_four : l1Target 4 = UInt256.ofNat 4171 := by decide
@[simp] theorem l1Target_eight : l1Target 8 = UInt256.ofNat 4019 := by decide
@[simp] theorem l2Target_four : l2Target 4 = UInt256.ofNat 4470 := by decide
@[simp] theorem l2Target_eight : l2Target 8 = UInt256.ofNat 4318 := by decide

/-! ## Row frames

The kernel keeps, below the per-step words, the row frame
`[pbi, hd, pb - 32, ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest`
(`pdst, ret, rest` are generic; the multiply instantiates them with
`inv, m0, tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest`).
`hd` is the row head the tail returns to (`JUMPI` via `DUP3`; 3996 for the multiply,
the `sq_row` pc 4710 for the square) and `ent` is the first-loop entry
(`l1Target n` for the multiply; the square rows advance it by 38 per row). -/

/-- The first-loop frame on an arbitrary MAC state `q` (memory and running carry). -/
def l1Q (pc : Nat) (s : State) (q : MacState) (bi : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [q.carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := q.memory }

/-- Before first-loop step `j` of a multiply row: `q = l1Step mem bi pa n j`. -/
def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  l1Q pc s (l1Step mem bi pa n j) bi pb n i hd ent pdst ret rest

/-- Row head before the first product; no dummy carry occupies the stack. -/
def firstAt (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
             hd, UInt256.ofNat (pb-32), ent,
             negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

/-- Before second-loop step `k` of row `i`: only the carry and `mu` above
`b_i` and the row frame. -/
def l2At (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [(l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
