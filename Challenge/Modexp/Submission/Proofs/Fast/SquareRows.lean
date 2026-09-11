import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareCaches
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The square rows of the sqCP1m kernel, row by row and as two bounded loops

Square row `i` (`0 ≤ i < n`, `n ∈ {4, 8}`, operand and accumulator addressed from
2048) is

    row head `hd = 4710` ─ prologue (`SquareRow.gasSteps_prologue`) ─▶ first-loop entry
    `4068 + 38(8 - n + i)` ─ chain (limb steps `i+1 .. n-1`) ─▶ middle `JUMPDEST` 4334
    ─ middle ─▶ second loop ─▶ tail ─ `DUP3 JUMPI` ─▶ row head `i + 1`   (or ─▶ exit ─▶ CSUB)

The memory after row `i` is WP-S1's machine-carry model
`SquareResult.sqRowsCarry M0 n (i + 1)`, the frame slot `ent` advances by 38 per row
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
open CiosCachedMidMemory CarryRowModel StagedOperand

/-! ## Row bookkeeping -/

/-- First-loop entry of square row `i` of an `n`-limb square: the block `k = 9 - n + i`
(limb step `i + 1`); for the last row the middle `JUMPDEST` 4334. -/
def sqEnt (n i : Nat) : Nat := 4072 + 38 * (8 - n + i)

/-- Frame slot 14 at row head `i`: the operand pointer `&a_0` for row 0 (the setup's
`aEnd`), the limb `x_{i-1}` that row `i - 1` parked there afterwards. -/
def sqPrev (M0 : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => UInt256.ofNat (2048 + 32 * n - 32)
  | i + 1 => sqX (sqRowsCarry M0 n i) n i

theorem sqTb_eq_prev (M0 : ByteArray) (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    UInt256.sgt (UInt256.ofNat 0) (sqPrev M0 n i) = sqTb (sqRowsCarry M0 n i) n i := by
  cases i with
  | zero =>
      show UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat (2048 + 32 * n - 32)) = UInt256.ofNat 0
      apply sgt_zero_eq_zero_of_lt
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  | succ j => exact (sqTb_succ_carry M0 n j (by omega) hn).symm

theorem jumpDest_sqEnt (n i : Nat) (hn : n ≤ 8) (hi : i < n) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (sqEnt n i) = true := by
  have h := KernelChain.jumpDest_l1Entry (9 - n + i) (by omega) (by omega)
  rwa [show 9 - n + i - 1 = 8 - n + i by omega] at h

theorem jumpDest4710' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4714).toNat = true :=
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
middle and second loop.  The first-loop result is `SquareModel.sqL1 mem n i tb`. -/
def gasSteps_rowToTail (s : State) (mem : ByteArray) (n i : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8) (hi : i < n)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2048 n) :
    Challenge.EvmProof.GasSteps
      (outState s mem 2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (tailState s
        (rowFromL2Carry (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) n).memory
        (rowFromL2Carry (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) n).carry
        (rowMu (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory n)
        (overflow (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
          (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry)
        2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i + 38)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)) := by
  have hn8 : n ≤ 8 := by omega
  have hn2 : 2 ≤ n := by omega
  have hn32 : n ≤ 32 := by omega
  -- the prologue
  have gP := gasSteps_prologue s mem n i (sqEnt n i) inv m0 tl m96 m64 m32 aprev
    (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hi hn8
    (jumpDest_sqEnt n i hn8 hi) (by unfold sqEnt; omega)
  -- the chain: block `k = 9 - n + i`, limb steps `i + 1 .. n - 1`
  have hk : 9 - n + i - 1 = 8 - n + i := by omega
  have hsteps : 8 - (9 - n + i) = n - 1 - i := by omega
  have gC := KernelChain.gasSteps_l1Suffix (9 - n + i) (by omega) (by omega) s
    (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev))
    (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2048 2048 n i (i + 1)
    (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i + 38)) inv m0
    (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hn8 (by omega) (by omega)
    (hsnap.sqPro i _ hi hn8)
  rw [hk, hsteps] at gC
  -- the first-loop result is `sqL1`
  have hQ : l1Run (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev))
      (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2048 n (i + 1) (n - 1 - i) =
      sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev) := rfl
  rw [hQ] at gC
  -- caches on the first-loop result
  have hstep : i + 1 + (n - 1 - i) ≤ n := by omega
  have hcQ : CiosReadonly.ReadonlyCache (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
      n tl inv m0 :=
    SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hc hn32 i hi _) hn32 _ 2048
      (i + 1) (n - 1 - i) hstep
  have heQ : CiosReadonlyExtra.ExtraCache
      (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro he n i hi _) _ 2048 n
      (i + 1) (n - 1 - i) hstep
  have hminvQ : inverseInvariant (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory n :=
    SquareCaches.inverse_l1Run _ _ 2048 n (i + 1) (n - 1 - i) hn32 hstep
      (SquareCaches.inverse_sqPro mem n i _ hn32 hi hminv)
  -- the middle
  have gM := CarryRowGas.gasSteps_mid s (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).memory
    (sqL1 mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)).carry
    (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2048 n i
    (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i + 38)) tl inv m0 (sqX mem n i) m96 m64 m32
    pdst ret rest hcap hrun hcode hfork hnp hact hn2 hn32 hminvQ hcQ
  refine (gP.trans gC).trans (gM.trans ?_)
  -- the second loop
  by_cases h4 : n = 4
  · subst h4
    exact CarryRowGas.gasSteps_l2Four s _ _ _ _ 2048 i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt 4 i + 38))
      tl inv m0 (sqX mem 4 i) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      (extraCache_midMem1 heQ _)
  · obtain rfl : n = 8 := by omega
    exact CarryRowGas.gasSteps_l2Eight s _ _ _ _ 2048 i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt 8 i + 38))
      tl inv m0 (sqX mem 8 i) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      (extraCache_midMem1 heQ _)

/-- **Square row `i` (`i + 1 < n`)**: row head `i` to row head `i + 1`. -/
def gasSteps_rowNext (s : State) (mem : ByteArray) (n i : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8) (hi : i + 1 < n)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2048 n) :
    Challenge.EvmProof.GasSteps
      (outState s mem 2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (outState s (sqRowCarry mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) 2048 n (i + 1)
        (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i + 38)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)) :=
  (gasSteps_rowToTail s mem n i tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun hcode hfork
    hnp hact hn (by omega) hminv hc he hsnap).trans
  (CarryRowGas.gasSteps_tailNext s _ _ _ _ 2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i + 38))
    inv m0 (tl :: m96 :: m64 :: m32 :: sqX mem n i :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hi (by decide)
    (by omega) jumpDest4710')

/-- **The last square row (`i + 1 = n`)**: row head to the `CSUB` entry. -/
def gasSteps_rowLast (s : State) (mem : ByteArray) (n i : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8) (hi : i + 1 = n)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2048 n) :
    Challenge.EvmProof.GasSteps
      (outState s mem 2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (mpCsubState s (sqRowCarry mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) pdst ret rest) :=
  (gasSteps_rowToTail s mem n i tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun hcode hfork
    hnp hact hn (by omega) hminv hc he hsnap).trans
  (CarryRowGas.gasSteps_tailLast s _ _ _ _ 2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i + 38))
    tl inv m0 (sqX mem n i) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hi
    (by decide) (by omega) jumpDest4710')

/-! ## The two loops -/

/-- The loop invariant state at row head `i`: memory `sqRowsCarry M0 n i`, frame slot
`ent = sqEnt n i`, slot 14 = `sqPrev M0 n i`. -/
def rowState (s : State) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256) (i : Nat) : State :=
  outState s (sqRowsCarry M0 n i) 2048 n i (UInt256.ofNat 4714) (UInt256.ofNat (sqEnt n i)) inv m0
    (tl :: m96 :: m64 :: m32 :: sqPrev M0 n i :: pdst :: ret :: rest)

theorem sqEnt_succ (n i : Nat) : sqEnt n i + 38 = sqEnt n (i + 1) := by
  unfold sqEnt; omega

/-- **All `n` square rows** (`n ∈ {4, 8}`): from row head 0 to the `CSUB` entry with the
machine-carry square rows `sqRowsCarry M0 n n` in memory. -/
def gasSteps_rows (s : State) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2048 n) :
    Challenge.EvmProof.GasSteps
      (rowState s M0 n tl inv m0 m96 m64 m32 pdst ret rest 0)
      (mpCsubState s (sqRowsCarry M0 n n) pdst ret rest) := by
  have hn8 : n ≤ 8 := by omega
  have hn32 : n ≤ 32 := by omega
  have next : ∀ i, i < n - 1 →
      Challenge.EvmProof.GasSteps (rowState s M0 n tl inv m0 m96 m64 m32 pdst ret rest i)
        (rowState s M0 n tl inv m0 m96 m64 m32 pdst ret rest (i + 1)) := by
    intro i hi
    have g := gasSteps_rowNext s (sqRowsCarry M0 n i) n i tl inv m0 m96 m64 m32 (sqPrev M0 n i)
      pdst ret rest hcap hrun hcode hfork hnp hact hn (by omega)
      (SquareCaches.inverse_sqRowsCarry M0 n hn32 hminv i (by omega))
      (SquareCaches.readonlyCache_sqRowsCarry hc hn32 i (by omega))
      (SquareCaches.extraCache_sqRowsCarry he n hn32 i (by omega))
      (hsnap.sqRowsCarry i (by omega) hn8)
    rw [sqTb_eq_prev M0 n i (by omega) hn32, ← sqRowsCarry_succ, sqEnt_succ n i] at g
    exact g
  have last := gasSteps_rowLast s (sqRowsCarry M0 n (n - 1)) n (n - 1) tl inv m0 m96 m64 m32
    (sqPrev M0 n (n - 1)) pdst ret rest hcap hrun hcode hfork hnp hact hn (by omega)
    (SquareCaches.inverse_sqRowsCarry M0 n hn32 hminv (n - 1) (by omega))
    (SquareCaches.readonlyCache_sqRowsCarry hc hn32 (n - 1) (by omega))
    (SquareCaches.extraCache_sqRowsCarry he n hn32 (n - 1) (by omega))
    (hsnap.sqRowsCarry (n - 1) (by omega) hn8)
  rw [sqTb_eq_prev M0 n (n - 1) (by omega) hn32, ← sqRowsCarry_succ,
    show n - 1 + 1 = n by omega] at last
  exact (Challenge.EvmProof.GasSteps.iterateBounded
    (I := rowState s M0 n tl inv m0 m96 m64 m32 pdst ret rest) (n - 1) next).trans last

end Challenge.Modexp.Submission.Proofs.Fast.SquareRows
