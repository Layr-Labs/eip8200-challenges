import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareCaches
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The square rows of the sqCP1m kernel, row by row and as two bounded loops

Square row `i` (`0 ≤ i < n`, `n ∈ {4, 8}`, operand and accumulator addressed from
2368) is

    row head `hd = 2464` ─ prologue (`SquareRow.gasSteps_prologue`) ─▶ first-loop entry
    `4296 + 37(8 - n + i)` ─ chain (limb steps `i+1 .. n-1`) ─▶ middle `JUMPDEST` 4555
    ─ middle ─▶ second loop ─▶ tail ─ `DUP3 JUMPI` ─▶ row head `i + 1`   (or ─▶ exit ─▶ CSUB)

The memory after row `i` is WP-S1's machine-carry model
`SquareResult.sqRowsCarry M0 n (i + 1)`, the frame slot `ent` advances by 37 per row
and slot 14 carries the previous limb `x_{i-1}` (`sqPrev`), whose top bit is the next
row's `tb` (`sqTb_eq_prev`).

The kernel blocks shared with the multiply are WP-K's: `KernelChain.gasSteps_l1Suffix`
(chain suffix), `CarryRowGas.gasSteps_mid`, `gasSteps_l2Four/Eight`, `gasSteps_tailNext`,
`gasSteps_tailLast` (all generic in the row head `hd` and the first-loop entry `ent`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRows

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult SquareRow CiosCached
open CiosCachedMidMemory CarryRowModel StagedOperand CarryScratchAgreement

/-! ## Row bookkeeping -/

/-- First-loop entry of square row `i` of an `n`-limb square: the block `k = 9 - n + i`
(limb step `i + 1`); for the last row the middle `JUMPDEST`.

Row `i`'s entry is the frame's `ent` slot advanced by 37 per row, starting from the
ladder base `l1BaseNat n` (3510 on the shared ladder for eight limbs, 5296 in the private
ladder copy for four limbs) that the staging block / the row-zero program install. -/
def sqEnt (n i : Nat) : Nat := l1BaseNat n + 37 * i

/-- Frame slot 14 at row head `i`: the row-0 value `a0` (the setup's `aEnd`, or zero when
the in-kernel loop re-enters), and the limb `x_{i-1}` that row `i - 1` parked there. -/
def sqPrev (a0 : UInt256) (M0 : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => a0
  | i + 1 => sqX (sqRowsCarry M0 n i) n i

/-- Any row-0 slot 14 with a clear top bit gives the row-0 carry `tb = 0`: the setup's
`&a_{n-1} < 2 ^ 255` and the loop's zero both qualify. -/
theorem sgt_zero_setup (n : Nat) (hn : n ≤ 8) :
    UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat (512 + 32 * n - 32)) = UInt256.ofNat 0 := by
  apply sgt_zero_eq_zero_of_lt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sgt_zero_zero : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  decide

/-- Slot 14 when the rows are done: the limb the last row parked there. -/
def sqLast (M0 : ByteArray) (n : Nat) : UInt256 := sqX (sqRowsCarry M0 n (n - 1)) n (n - 1)

theorem sqTb_eq_prev (a0 : UInt256) (M0 : ByteArray) (n i : Nat) (hi : i < n) (hn : n ≤ 8)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0) :
    UInt256.sgt (UInt256.ofNat 0) (sqPrev a0 M0 n i) = sqTb (sqRowsCarry M0 n i) n i := by
  cases i with
  | zero =>
      show UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0
      exact ha0
  | succ j => exact (sqTb_succ_carry M0 n j (by omega) hn).symm

theorem jumpDest_sqEnt (n i : Nat) (hn4 : n = 4 ∨ n = 8) (hi : i < n) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (sqEnt n i) = true := by
  rcases hn4 with rfl | rfl
  · have h := KernelChain.jumpDest_l1EntryCopy (9 - 4 + i) (by omega) (by omega)
    rwa [show (5148 + 37 * (9 - 4 + i - 1)) = sqEnt 4 i by unfold sqEnt l1BaseNat; omega] at h
  · have h := KernelChain.jumpDest_l1Entry (9 - 8 + i) (by omega) (by omega)
    rwa [show (3510 + 37 * (9 - 8 + i - 1)) = sqEnt 8 i by unfold sqEnt l1BaseNat; omega] at h

theorem jumpDest4710' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4190).toNat = true :=
  jumpDest4710

theorem extraCache_midMem1 {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) (c : UInt256) :
    CiosReadonlyExtra.ExtraCache (midMem1 mem c) m96 m64 m32 :=
  hc.of_preserved
    (readWord_midMem1 mem c 96 (Or.inl (by decide)))
    (readWord_midMem1 mem c 64 (Or.inl (by decide)))
    (readWord_midMem1 mem c 32 (Or.inl (by decide)))

/-! ## One square row -/

/-- **Square row `i` up to the tail block** (`i < n`, `n ∈ {4, 8}`): prologue, chain,
middle and second loop.  The first-loop result is `SquareModel.sqL1 mem n i tb`; the cell
`cy` is merged at the head (`cy + carry`) and its overflow rides the `b_i` slot. -/
def gasSteps_rowToTail (s : State) (mem : ByteArray) (n i : Nat)
    (cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8) (hi : i < n)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 n) :
    Challenge.EvmProof.GasSteps
      (outState s mem 2368 n i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i)) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (tailState s
        (fromL2S (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) n).memory
        (fromL2S (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) n).carry
        (rowMu (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory n)
        (slotOverflow cy (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry)
        2368 n i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i + 37))
        (cy + (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)) := by
  have hn8 : n ≤ 8 := by omega
  have hn2 : 2 ≤ n := by omega
  have hn32 : n ≤ 8 := by omega
  -- the prologue
  have gP := gasSteps_prologue s mem n i (sqEnt n i) cy inv m0 tl m96 m64 m32 aprev
    (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hi hn8
    (jumpDest_sqEnt n i hn hi) (by unfold sqEnt l1BaseNat; rcases hn with rfl | rfl <;> omega)
  -- Four limbs walk the private ladder copy (5296, 5333, 5370, 5407) and leave through its
  -- own `PUSH2 0x0f63 JUMP`; eight limbs walk the shared ladder and fall through 3769 into
  -- the join at 3791.  Chain, middle block and exit all differ, so the row splits on the
  -- width here.
  by_cases h4 : n = 4
  · subst h4
    -- the chain: block `k = 9 - 4 + i`, limb steps `i + 1 .. 4 - 1`
    have hk : (5148 + 37 * (9 - 4 + i - 1)) = sqEnt 4 i := by unfold sqEnt l1BaseNat; omega
    have hsteps : 8 - (9 - 4 + i) = 4 - 1 - i := by omega
    have gC := KernelChain.gasSteps_l1SuffixCopy (9 - 4 + i) (by omega) (by omega) s
      (sqPro mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev))
      (sqB2 (sqX mem 4 i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 2368 4 i (i + 1)
      (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 4 i + 37)) cy inv m0
      (tl :: m96 :: m64 :: m32 :: sqX mem 4 i :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hn8 (by omega) (by omega)
      (hsnap.sqPro i _ hi hn8)
    rw [hk, hsteps] at gC
    -- the first-loop result is `sqL1`
    have hQ : l1Run (sqPro mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev))
        (sqB2 (sqX mem 4 i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 4 (i + 1) (4 - 1 - i) =
        sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev) := rfl
    rw [hQ] at gC
    -- caches on the first-loop result
    have hstep : i + 1 + (4 - 1 - i) ≤ 4 := by omega
    have hcQ : CiosReadonly.ReadonlyCache (sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
        4 tl inv m0 :=
      SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hc hn32 i hi _) hn32 _ 2368
        (i + 1) (4 - 1 - i) hstep
    have heQ : CiosReadonlyExtra.ExtraCache
        (sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory m96 m64 m32 :=
      SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro he 4 i hi _) _ 2368 4
        (i + 1) (4 - 1 - i) hstep
    have hminvQ : inverseInvariant (sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory 4 :=
      SquareCaches.inverse_l1Run _ _ 2368 4 (i + 1) (4 - 1 - i) hn32 hstep
        (SquareCaches.inverse_sqPro mem 4 i _ hn32 hi hminv)
    -- the middle
    have gM := CarryRowGas.gasSteps_midCopy s (sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
      (sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry
      (sqB2 (sqX mem 4 i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 4 i
      (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 4 i + 37)) cy tl inv m0 (sqX mem 4 i) m96 m64 m32
      pdst ret rest hcap hrun hcode hfork hnp hact hn2 hn32 hminvQ hcQ
    refine (gP.trans gC).trans (gM.trans ?_)
    -- the second loop
    exact CarryRowGas.gasSteps_l2Four s _ _ _ _ 2368 i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 4 i + 37))
      (cy + (sqL1 mem 4 i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry)
      tl inv m0 (sqX mem 4 i) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact heQ
  · obtain rfl : n = 8 := by omega
    -- the chain: block `k = 9 - 8 + i`, limb steps `i + 1 .. 8 - 1`
    have hk : (3510 + 37 * (9 - 8 + i - 1)) = sqEnt 8 i := by unfold sqEnt l1BaseNat; omega
    have hsteps : 8 - (9 - 8 + i) = 8 - 1 - i := by omega
    have gC := KernelChain.gasSteps_l1Suffix (9 - 8 + i) (by omega) (by omega) s
      (sqPro mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev))
      (sqB2 (sqX mem 8 i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 2368 8 i (i + 1)
      (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 8 i + 37)) cy inv m0
      (tl :: m96 :: m64 :: m32 :: sqX mem 8 i :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hn8 (by omega) (by omega)
      (hsnap.sqPro i _ hi hn8)
    rw [hk, hsteps] at gC
    -- the first-loop result is `sqL1`
    have hQ : l1Run (sqPro mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev))
        (sqB2 (sqX mem 8 i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 8 (i + 1) (8 - 1 - i) =
        sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev) := rfl
    rw [hQ] at gC
    -- caches on the first-loop result
    have hstep : i + 1 + (8 - 1 - i) ≤ 8 := by omega
    have hcQ : CiosReadonly.ReadonlyCache (sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
        8 tl inv m0 :=
      SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hc hn32 i hi _) hn32 _ 2368
        (i + 1) (8 - 1 - i) hstep
    have heQ : CiosReadonlyExtra.ExtraCache
        (sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory m96 m64 m32 :=
      SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro he 8 i hi _) _ 2368 8
        (i + 1) (8 - 1 - i) hstep
    have hminvQ : inverseInvariant (sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory 8 :=
      SquareCaches.inverse_l1Run _ _ 2368 8 (i + 1) (8 - 1 - i) hn32 hstep
        (SquareCaches.inverse_sqPro mem 8 i _ hn32 hi hminv)
    -- the middle
    have gM := CarryRowGas.gasSteps_mid s (sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
      (sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry
      (sqB2 (sqX mem 8 i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 8 i
      (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 8 i + 37)) cy tl inv m0 (sqX mem 8 i) m96 m64 m32
      pdst ret rest hcap hrun hcode hfork hnp hact hn2 hn32 hminvQ hcQ
    refine (gP.trans gC).trans (gM.trans ?_)
    -- the second loop
    exact CarryRowGas.gasSteps_l2Eight s _ _ _ _ 2368 i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 8 i + 37))
      (cy + (sqL1 mem 8 i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry)
      tl inv m0 (sqX mem 8 i) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact heQ

/-- **Square row `i` (`i + 1 < n`)**: row head `i` to row head `i + 1`. -/
def gasSteps_rowNext (s : State) (mem : ByteArray) (n i : Nat)
    (cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8) (hi : i + 1 < n)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 n) :
    Challenge.EvmProof.GasSteps
      (outState s mem 2368 n i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i)) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (outState s (fromMemS (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) cy n) 2368 n (i + 1)
        (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i + 37))
        (fromSlot (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) cy n) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)) :=
  (gasSteps_rowToTail s mem n i cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun hcode hfork
    hnp hact hn (by omega) hminv hc he hsnap).trans
  (CarryRowGas.gasSteps_tailNext s _ _ _ _ 2368 n i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i + 37))
    (cy + (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry)
    inv m0 (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hi (by decide)
    (by omega) jumpDest4710')

/-- **The last square row (`i + 1 = n`)**: row head to `sq_exit`, with the row frame
retained (the R0 kernel-exit dispatch flushes the cell and sends `hd = sq_row` there). -/
def gasSteps_rowLastToExit (s : State) (mem : ByteArray) (n i : Nat)
    (cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8) (hi : i + 1 = n)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 n) :
    Challenge.EvmProof.GasSteps
      (outState s mem 2368 n i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i)) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (CiosCachedTailDefs.sqExitState s
        (flushS (fromMemS (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) cy n)
          (fromSlot (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) cy n))
        (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) (i + 1))) 2368 n (UInt256.ofNat 4190)
        (UInt256.ofNat (sqEnt n i + 37))
        (fromSlot (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) cy n) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)) :=
  (gasSteps_rowToTail s mem n i cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun hcode hfork
    hnp hact hn (by omega) hminv hc he hsnap).trans
  (CarryRowGas.gasSteps_tailLastSq s _ _ _ _ 2368 n i (UInt256.ofNat (sqEnt n i + 37))
    (cy + (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry)
    tl inv m0 (sqX mem n i) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hi
    (by decide) (by omega) jumpDest4710')

/-! ## The two loops -/

/-- The loop invariant state at row head `i`: the real memory is the model memory
`sqRowsCarry M0 n i` with the entry scratch word of `R` re-installed (`unflush`), the cell
holds the model's scratch word, frame slot `ent = sqEnt n i`, slot 14 = `sqPrev a0 M0 n i`. -/
def rowState (s : State) (a0 : UInt256) (R M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256) (i : Nat) : State :=
  outState s (unflush R (sqRowsCarry M0 n i)) 2368 n i (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt n i))
    (MachineState.readWord (sqRowsCarry M0 n i) 2080) inv m0
    (tl :: m96 :: m64 :: m32 :: sqPrev a0 M0 n i :: pdst :: ret :: rest)

theorem sqEnt_succ (n i : Nat) : sqEnt n i + 37 = sqEnt n (i + 1) := by
  unfold sqEnt; omega

theorem readonlyCache_unflush {R M : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (hc : CiosReadonly.ReadonlyCache M n tl inv m0) (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    CiosReadonly.ReadonlyCache (unflush R M) n tl inv m0 :=
  hc.of_preserved (readWord_unflush R M 2720 (Or.inr (by decide)))
    (readWord_unflush R M (32*n-32) (Or.inl (by omega)))

theorem extraCache_unflush {R M : ByteArray} {m96 m64 m32 : UInt256}
    (he : CiosReadonlyExtra.ExtraCache M m96 m64 m32) :
    CiosReadonlyExtra.ExtraCache (unflush R M) m96 m64 m32 :=
  he.of_preserved (readWord_unflush R M 96 (Or.inl (by decide)))
    (readWord_unflush R M 64 (Or.inl (by decide)))
    (readWord_unflush R M 32 (Or.inl (by decide)))

theorem inverse_unflush (R M : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hminv : inverseInvariant M n) :
    inverseInvariant (unflush R M) n := by
  unfold inverseInvariant at *
  rw [readWord_unflush R M (32*n-32) (Or.inl (by omega)), readWord_unflush R M 2720 (Or.inr (by decide))]
  exact hminv

/-- One row of the loop invariant. -/
def gasSteps_rowStateNext (s : State) (a0 : UInt256) (R M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (_hsnap : StagedOperand.Snapshot M0 2368 n) (i : Nat) (hi : i + 1 < n) :
    Challenge.EvmProof.GasSteps (rowState s a0 R M0 n tl inv m0 m96 m64 m32 pdst ret rest i)
      (rowState s a0 R M0 n tl inv m0 m96 m64 m32 pdst ret rest (i + 1)) := by
  have hn8 : n ≤ 8 := by omega
  have g := gasSteps_rowNext s (unflush R (sqRowsCarry M0 n i)) n i
    (MachineState.readWord (sqRowsCarry M0 n i) 2080) tl inv m0 m96 m64 m32
    (sqPrev a0 M0 n i) pdst ret rest hcap hrun hcode hfork hnp hact hn hi
    (inverse_unflush R _ n (by omega) hn8
      (SquareCaches.inverse_sqRowsCarry M0 n hn8 hminv i (by omega)))
    (readonlyCache_unflush (SquareCaches.readonlyCache_sqRowsCarry hc hn8 i (by omega)) (by omega) hn8)
    (extraCache_unflush (SquareCaches.extraCache_sqRowsCarry he n hn8 i (by omega)))
    (fun _ _ => rfl)
  have hb := sqRow_unflush R (sqRowsCarry M0 n i) n i (sqTb (sqRowsCarry M0 n i) n i) (by omega)
    (by omega) hn8
  rw [sqTb_eq_prev a0 M0 n i (by omega) hn8 ha0, hb.1, hb.2, ← sqRowsCarry_succ, sqEnt_succ n i,
    sqX_unflush] at g
  exact g

/-- **All `n` square rows** (`n ∈ {4, 8}`): from row head 0 to `sq_exit`, with the
machine-carry square rows `sqRowsCarry M0 n n` in memory (exactly, thanks to the exit
flush) and the frame retained. -/
def gasSteps_rowsToExit (s : State) (a0 : UInt256) (R M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 n) :
    Challenge.EvmProof.GasSteps
      (rowState s a0 R M0 n tl inv m0 m96 m64 m32 pdst ret rest 0)
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry M0 n n)
        (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n)) 2368 n (UInt256.ofNat 4190)
        (UInt256.ofNat (sqEnt n n)) (MachineState.readWord (sqRowsCarry M0 n n) 2080) inv m0
        (tl :: m96 :: m64 :: m32 :: sqLast M0 n :: pdst :: ret :: rest)) := by
  have hn8 : n ≤ 8 := by omega
  have last := gasSteps_rowLastToExit s (unflush R (sqRowsCarry M0 n (n - 1))) n (n - 1)
    (MachineState.readWord (sqRowsCarry M0 n (n - 1)) 2080) tl inv m0 m96 m64 m32
    (sqPrev a0 M0 n (n - 1)) pdst ret rest hcap hrun hcode hfork hnp hact hn (by omega)
    (inverse_unflush R _ n (by omega) hn8
      (SquareCaches.inverse_sqRowsCarry M0 n hn8 hminv (n - 1) (by omega)))
    (readonlyCache_unflush (SquareCaches.readonlyCache_sqRowsCarry hc hn8 (n - 1) (by omega)) (by omega) hn8)
    (extraCache_unflush (SquareCaches.extraCache_sqRowsCarry he n hn8 (n - 1) (by omega)))
    (fun _ _ => rfl)
  have hb := sqRow_unflush R (sqRowsCarry M0 n (n - 1)) n (n - 1)
    (sqTb (sqRowsCarry M0 n (n - 1)) n (n - 1)) (by omega) (by omega) hn8
  rw [sqTb_eq_prev a0 M0 n (n - 1) (by omega) hn8 ha0, hb.1, hb.2, ← sqRowsCarry_succ,
    sqRowsCarry_unflush_flush, show n - 1 + 1 = n by omega, sqEnt_succ n (n - 1),
    show n - 1 + 1 = n by omega, sqX_unflush] at last
  exact (Challenge.EvmProof.GasSteps.iterateBounded
    (I := rowState s a0 R M0 n tl inv m0 m96 m64 m32 pdst ret rest) (n - 1)
    (fun i hi => gasSteps_rowStateNext s a0 R M0 n tl inv m0 m96 m64 m32 pdst ret rest hcap hrun
      hcode hfork hnp hact hn ha0 hminv hc he hsnap i (by omega))).trans last

end Challenge.Modexp.Submission.Proofs.Fast.SquareRows
