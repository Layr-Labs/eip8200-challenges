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


/-- Prologue value of the first-loop register (frame slot `ent`): the setup computes
`0x0db6 + 14 * (s32 &&& 128)`: for eight limbs `s32 = 256`, the mask is zero and the
register holds the shared k1 JUMPDEST 3510; for four limbs `s32 = 128`, adding
`14*128 = 1792` gives 5302.  Since the reassembly the four-limb value is NOT the
entry of the private ladder copy (that is `l1Base 4 = 5296`): the staging block
recomputes the base from the register (`ent - (6 + 290 * [ent < 4096])`, E8) before
any first-loop dispatch, and the four-limb square rows never use the shared ladder.

Base transcribed from the artifact, not adjusted: the computation is literally
`PUSH1 0xe; MUL; PUSH2 0xdb6; ADD` at indices 2696..2699 (pc 3364..3370). -/
def l1Target (n : Nat) : UInt256 :=
  UInt256.ofNat 3510 + UInt256.ofNat 1792 * isFour n

/-- The first-loop ladder entry the multiply rows dispatch to (`DUP6 JUMP`): the shared
ladder k1 block 3510 for eight limbs, the private copy's k5 block 5296 for four limbs.
The staging block (E8) installs it into the `ent` register; `l1Target` is what the
prologue installed there before. -/
def l1BaseNat (n : Nat) : Nat := 3510 + 1786 * ((8 - n) / 4)

def l1Base (n : Nat) : UInt256 := UInt256.ofNat (l1BaseNat n)

/-- Prologue value of the frame cell at absolute stack position 15 (`ent + 0x120`).
Before the reassembly this was the second-loop entry constant; the reassembled kernel
evicts it and uses the cell as the row-carry channel (see `CarryRowModel.rowsS`), so
the value is only ever the cell's content between the prologue and the first install
(the staging reload E15, a row-0 park E11/E12) and is never read. -/
def l2Target (n : Nat) : UInt256 :=
  UInt256.ofNat 3798 + UInt256.ofNat 1792 * isFour n

@[simp] theorem l1Target_four : l1Target 4 = UInt256.ofNat 5302 := by decide
@[simp] theorem l1Target_eight : l1Target 8 = UInt256.ofNat 3510 := by decide
@[simp] theorem l1BaseNat_four : l1BaseNat 4 = 5296 := by decide
@[simp] theorem l1BaseNat_eight : l1BaseNat 8 = 3510 := by decide
@[simp] theorem l1Base_four : l1Base 4 = UInt256.ofNat 5296 := by decide
@[simp] theorem l1Base_eight : l1Base 8 = UInt256.ofNat 3510 := by decide
@[simp] theorem l2Target_four : l2Target 4 = UInt256.ofNat 5590 := by decide
@[simp] theorem l2Target_eight : l2Target 8 = UInt256.ofNat 3798 := by decide

/-! ## Row frames

The kernel keeps, below the per-step words, the row frame
`[pbi, hd, pb - 32, ent, negative32, allOnes, cy, pdst, ret] ++ rest`
(`pdst, ret, rest` are generic; the multiply instantiates them with
`inv, m0, tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest`).
`hd` is the row head the tail returns to (`JUMPI` via `DUP3`; 3481 for the multiply,
the `sq_row` pc 4190 for the square), `ent` is the first-loop entry
(`l1Base n` for the multiply; the square rows advance it by 37 per row), and `cy` is
the row-carry channel: the cell at absolute stack position 15 that the reassembled row
head reads (`DUP10`) and installs (`SWAP9`) instead of the scratch word `mem[2080]`. -/

/-- The first-loop frame on an arbitrary MAC state `q` (memory and running carry). -/
def l1Q (pc : Nat) (s : State) (q : MacState) (bi : UInt256)
    (pb n i : Nat) (hd ent cy pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [q.carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, cy, pdst, ret] ++ rest
           memory := q.memory }

/-- Before first-loop step `j` of a multiply row: `q = l1Step mem bi pa n j`. -/
def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent cy pdst ret : UInt256) (rest : List UInt256) : State :=
  l1Q pc s (l1Step mem bi pa n j) bi pb n i hd ent cy pdst ret rest

/-- Row head before the first product; no dummy carry occupies the stack. -/
def firstAt (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pb n i : Nat) (hd ent cy pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
             hd, UInt256.ofNat (pb-32), ent,
             negative32, allOnes, cy, pdst, ret] ++ rest
           memory := mem }

/-- Before second-loop step `k` of row `i`: only the carry and `mu` above
`b_i` and the row frame. -/
def l2At (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent cy pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [(l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, cy, pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
