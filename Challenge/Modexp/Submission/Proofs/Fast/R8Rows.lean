import Challenge.Modexp.Submission.Proofs.Fast.SquareRows
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZero

set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8Rows
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareModel SquareResult SquareRow SquareRows
open CiosCachedMidMemory CarryRowModel StagedOperand

def gasSteps_rowZeroToTail (s : State) (mem : ByteArray)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord mem 2336 = UInt256.ofNat 0)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 8) :
    Challenge.EvmProof.GasSteps
      { outState s mem 2368 8 0 (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 4453 }
      (tailState s
        (rowFromL2Carry (sqL1 mem 8 0 (UInt256.ofNat 0)) 8).memory
        (rowFromL2Carry (sqL1 mem 8 0 (UInt256.ofNat 0)) 8).carry
        (rowMu (sqL1 mem 8 0 (UInt256.ofNat 0)).memory 8)
        (overflow (sqL1 mem 8 0 (UInt256.ofNat 0)).memory
          (sqL1 mem 8 0 (UInt256.ofNat 0)).carry)
        2368 8 0 (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: pdst :: ret :: rest)) := by
  have hi : (0 : Nat) < 8 := by decide
  have hn8 : 8 ≤ 8 := by omega
  have hn2 : 2 ≤ 8 := by omega
  have hn32 : 8 ≤ 8 := by omega
  -- the prologue
  have gP := R8RowZero.gasSteps_prologue s mem (sqEnt 8 0) inv m0 tl m96 m64 m32 aprev
    (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hzero
    (jumpDest_sqEnt 8 0 hn8 hi) (by unfold sqEnt; omega) (by decide)
  -- the chain: block `k = 9 - 8 + 0`, limb steps `0 + 1 .. 8 - 1`
  have hk : 9 - 8 + 0 - 1 = 8 - 8 + 0 := by omega
  have hsteps : 8 - (9 - 8 + 0) = 8 - 1 - 0 := by omega
  have gC := KernelChain.gasSteps_l1Suffix (9 - 8 + 0) (by omega) (by omega) s
    (sqPro mem 8 0 (UInt256.ofNat 0))
    (sqB2 (sqX mem 8 0) (UInt256.ofNat 0)) 2368 2368 8 0 (0 + 1)
    (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
    (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hn8 (by omega) (by omega)
    (hsnap.sqPro 0 _ hi hn8)
  rw [hk, hsteps] at gC
  -- the first-loop result is `sqL1`
  have hQ : l1Run (sqPro mem 8 0 (UInt256.ofNat 0))
      (sqB2 (sqX mem 8 0) (UInt256.ofNat 0)) 2368 8 (0 + 1) (8 - 1 - 0) =
      sqL1 mem 8 0 (UInt256.ofNat 0) := rfl
  rw [hQ] at gC
  -- caches on the first-loop result
  have hstep : 0 + 1 + (8 - 1 - 0) ≤ 8 := by omega
  have hcQ : CiosReadonly.ReadonlyCache (sqL1 mem 8 0 (UInt256.ofNat 0)).memory
      8 tl inv m0 :=
    SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hc hn32 0 hi _) hn32 _ 2368
      (0 + 1) (8 - 1 - 0) hstep
  have heQ : CiosReadonlyExtra.ExtraCache
      (sqL1 mem 8 0 (UInt256.ofNat 0)).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro he 8 0 hi _) _ 2368 8
      (0 + 1) (8 - 1 - 0) hstep
  have hminvQ : inverseInvariant (sqL1 mem 8 0 (UInt256.ofNat 0)).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 (0 + 1) (8 - 1 - 0) hn32 hstep
      (SquareCaches.inverse_sqPro mem 8 0 _ hn32 hi hminv)
  -- the middle
  have gM := CarryRowGas.gasSteps_mid s (sqL1 mem 8 0 (UInt256.ofNat 0)).memory
    (sqL1 mem 8 0 (UInt256.ofNat 0)).carry
    (sqB2 (sqX mem 8 0) (UInt256.ofNat 0)) 2368 8 0
    (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0 + 37)) tl inv m0 (sqX mem 8 0) m96 m64 m32
    pdst ret rest hcap hrun hcode hfork hnp hact hn2 hn32 hminvQ hcQ
  refine (gP.trans gC).trans (gM.trans ?_)
  -- the second loop
  exact CarryRowGas.gasSteps_l2Eight s _ _ _ _ 2368 0 (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0 + 37))
    tl inv m0 (sqX mem 8 0) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
    (extraCache_midMem1 heQ _)

def gasSteps_rowZeroNext (s : State) (mem : ByteArray)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord mem 2336 = UInt256.ofNat 0)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 8) :
    Challenge.EvmProof.GasSteps
      { outState s mem 2368 8 0 (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 4453 }
      (outState s (sqRowCarry mem 8 0 (UInt256.ofNat 0)) 2368 8 (0 + 1)
        (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: pdst :: ret :: rest)) :=
  (gasSteps_rowZeroToTail s mem tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun hcode hfork
    hnp hact hzero hminv hc he hsnap).trans
  (CarryRowGas.gasSteps_tailNext s _ _ _ _ 2368 8 0 (UInt256.ofNat 4483) (UInt256.ofNat (sqEnt 8 0 + 37))
    inv m0 (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by decide)
    (by omega) jumpDest4710')

def gasSteps_rowsToExit (s : State) (a0 : UInt256) (M0 : ByteArray)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord M0 2336 = UInt256.ofNat 0)
    (hminv : inverseInvariant M0 8)
    (hc : CiosReadonly.ReadonlyCache M0 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 8) :
    Challenge.EvmProof.GasSteps
      { rowState s a0 M0 8 tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 4453 }
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry M0 8 8)
        (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 8)) 2368 8 (UInt256.ofNat 4483)
        (UInt256.ofNat (sqEnt 8 8)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqLast M0 8 :: pdst :: ret :: rest)) := by
  have ha0 : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
  have g0 := gasSteps_rowZeroNext s M0 tl inv m0 m96 m64 m32 a0 pdst ret rest
    hcap hrun hcode hfork hnp hact hzero hminv hc he hsnap
  have g0' : Challenge.EvmProof.GasSteps
      { rowState s a0 M0 8 tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 4453 }
      (rowState s (UInt256.ofNat 0) M0 8 tl inv m0 m96 m64 m32 pdst ret rest 1) := by
    simpa only [rowState, sqRowsCarry, sqTb, sqPrev, sqEnt_succ] using g0
  have next : ∀ i, i < 7 →
      Challenge.EvmProof.GasSteps (rowState s (UInt256.ofNat 0) M0 8 tl inv m0 m96 m64 m32 pdst ret rest i)
        (rowState s (UInt256.ofNat 0) M0 8 tl inv m0 m96 m64 m32 pdst ret rest (i + 1)) := by
    intro i hi
    have g := SquareRows.gasSteps_rowNext s (sqRowsCarry M0 8 i) 8 i tl inv m0 m96 m64 m32
      (sqPrev (UInt256.ofNat 0) M0 8 i) pdst ret rest hcap hrun hcode hfork hnp hact (Or.inr rfl) (by omega)
      (SquareCaches.inverse_sqRowsCarry M0 8 (by decide) hminv i (by omega))
      (SquareCaches.readonlyCache_sqRowsCarry hc (by decide) i (by omega))
      (SquareCaches.extraCache_sqRowsCarry he 8 (by decide) i (by omega))
      (hsnap.sqRowsCarry i (by omega) (by decide))
    rw [sqTb_eq_prev (UInt256.ofNat 0) M0 8 i (by omega) (by decide) ha0, ← sqRowsCarry_succ, sqEnt_succ 8 i] at g
    exact g
  have last := SquareRows.gasSteps_rowLastToExit s (sqRowsCarry M0 8 7) 8 7 tl inv m0 m96 m64 m32
    (sqPrev (UInt256.ofNat 0) M0 8 7) pdst ret rest hcap hrun hcode hfork hnp hact (Or.inr rfl) (by decide)
    (SquareCaches.inverse_sqRowsCarry M0 8 (by decide) hminv 7 (by decide))
    (SquareCaches.readonlyCache_sqRowsCarry hc (by decide) 7 (by decide))
    (SquareCaches.extraCache_sqRowsCarry he 8 (by decide) 7 (by decide))
    (hsnap.sqRowsCarry 7 (by decide) (by decide))
  rw [sqTb_eq_prev (UInt256.ofNat 0) M0 8 7 (by decide) (by decide) ha0, ← sqRowsCarry_succ,
    sqEnt_succ 8 7] at last
  exact (g0'.trans (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => rowState s (UInt256.ofNat 0) M0 8 tl inv m0 m96 m64 m32 pdst ret rest (i + 1))
    6 (fun i hi => next (i + 1) (by omega)))).trans last

def gasSteps_rowsZeroWidth (s : State) (a0 : UInt256) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 8)
    (hzero : MachineState.readWord M0 2336 = UInt256.ofNat 0)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 n) :
    Challenge.EvmProof.GasSteps
      { rowState s a0 M0 n tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 4453 }
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry M0 n n)
        (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n)) 2368 n (UInt256.ofNat 4483)
        (UInt256.ofNat (sqEnt n n)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqLast M0 n :: pdst :: ret :: rest)) := by
  subst n
  exact gasSteps_rowsToExit s a0 M0 tl inv m0 m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact hzero hminv hc he hsnap


end Challenge.Modexp.Submission.Proofs.Fast.R8Rows
