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


def l1Target (n : Nat) : UInt256 :=
  UInt256.ofNat 4239 + UInt256.ofNat 150 * isFour n

def l2Target (n : Nat) : UInt256 :=
  UInt256.ofNat 4574 + UInt256.ofNat 150 * isFour n

@[simp] theorem l1Target_four : l1Target 4 = UInt256.ofNat 4389 := by decide
@[simp] theorem l1Target_eight : l1Target 8 = UInt256.ofNat 4239 := by decide
@[simp] theorem l2Target_four : l2Target 4 = UInt256.ofNat 4724 := by decide
@[simp] theorem l2Target_eight : l2Target 8 = UInt256.ofNat 4574 := by decide

def modulusAddress (n : Nat) : UInt256 := UInt256.ofNat (32*n-32)


def modulusValue (mem : ByteArray) (n : Nat) : UInt256 :=
  MachineState.readWord mem (32*n-32)

theorem modulusValue_zero (s : State) (mem : ByteArray) (n : Nat) (hn : n ≤ 32) :
    modulusValue (mpZeroed s mem n) n = modulusValue mem n :=
  readWord_mpZeroed s mem n (32*n-32) hn (Or.inl (by omega))

theorem modulusValue_l1 (mem : ByteArray) (bi : UInt256) (pa n j : Nat) (hn : n ≤ 32) :
    modulusValue (l1Step mem bi pa n j).memory n = modulusValue mem n :=
  readWord_l1Step mem bi pa n (32*n-32) j hn (Or.inl (by omega))

theorem modulusValue_l2 (mem : ByteArray) (mu c0 : UInt256) (n k : Nat) (hn : n ≤ 32) :
    modulusValue (l2Step mem mu c0 n k).memory n = modulusValue mem n :=
  readWord_l2Step mem mu c0 n (32*n-32) k hn (Or.inl (by omega))

theorem modulusValue_mid (mem : ByteArray) (c : UInt256) (n : Nat) (hn : n ≤ 32) :
    modulusValue (midMem mem c) n = modulusValue mem n :=
  readWord_midMem mem c (32*n-32) (Or.inl (by omega))

theorem modulusValue_tail (mem : ByteArray) (c : UInt256) (n : Nat) (hn : n ≤ 32) :
    modulusValue (tailMem mem c) n = modulusValue mem n :=
  readWord_tailMem mem c (32*n-32) (Or.inl (by omega))

def inverseValue (mem : ByteArray) : UInt256 := MachineState.readWord mem 9376

theorem inverseValue_zero (s : State) (mem : ByteArray) (n : Nat) (hn : n ≤ 32) :
    inverseValue (mpZeroed s mem n) = inverseValue mem :=
  readWord_mpZeroed s mem n 9376 hn (Or.inr (by decide))

theorem inverseValue_l1 (mem : ByteArray) (bi : UInt256) (pa n j : Nat) (hn : n ≤ 32) :
    inverseValue (l1Step mem bi pa n j).memory = inverseValue mem :=
  readWord_l1Step mem bi pa n 9376 j hn (Or.inr (by decide))

theorem inverseValue_l2 (mem : ByteArray) (mu c0 : UInt256) (n k : Nat) (hn : n ≤ 32) :
    inverseValue (l2Step mem mu c0 n k).memory = inverseValue mem :=
  readWord_l2Step mem mu c0 n 9376 k hn (Or.inr (by decide))

theorem inverseValue_mid (mem : ByteArray) (c : UInt256) :
    inverseValue (midMem mem c) = inverseValue mem :=
  readWord_midMem mem c 9376 (Or.inr (by decide))

theorem inverseValue_tail (mem : ByteArray) (c : UInt256) :
    inverseValue (tailMem mem c) = inverseValue mem :=
  readWord_tailMem mem c 9376 (Or.inr (by decide))

def tailPointerValue (mem : ByteArray) : UInt256 := MachineState.readWord mem 9440

theorem tailPointerValue_zero (s : State) (mem : ByteArray) (n : Nat) (hn : n ≤ 32) :
    tailPointerValue (mpZeroed s mem n) = tailPointerValue mem :=
  readWord_mpZeroed s mem n 9440 hn (Or.inr (by decide))

theorem tailPointerValue_l1 (mem : ByteArray) (bi : UInt256) (pa n j : Nat) (hn : n ≤ 32) :
    tailPointerValue (l1Step mem bi pa n j).memory = tailPointerValue mem :=
  readWord_l1Step mem bi pa n 9440 j hn (Or.inr (by decide))

theorem tailPointerValue_l2 (mem : ByteArray) (mu c0 : UInt256) (n k : Nat) (hn : n ≤ 32) :
    tailPointerValue (l2Step mem mu c0 n k).memory = tailPointerValue mem :=
  readWord_l2Step mem mu c0 n 9440 k hn (Or.inr (by decide))

theorem tailPointerValue_mid (mem : ByteArray) (c : UInt256) :
    tailPointerValue (midMem mem c) = tailPointerValue mem :=
  readWord_midMem mem c 9440 (Or.inr (by decide))

theorem tailPointerValue_tail (mem : ByteArray) (c : UInt256) :
    tailPointerValue (tailMem mem c) = tailPointerValue mem :=
  readWord_tailMem mem c 9440 (Or.inr (by decide))


/-- Before first-loop step `j`: carry and `b_i` above the honest cached base. -/
def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [(l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, negative32, allOnes, l2Target n, modulusValue mem n, inverseValue mem, tailPointerValue mem, pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

/-- Before second-loop step `k` of row `i`: only the carry and `mu` above
`b_i` and the row frame. -/
def l2At (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [(l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, negative32, allOnes, l2Target n, modulusValue mid n, inverseValue mid, tailPointerValue mid, pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
