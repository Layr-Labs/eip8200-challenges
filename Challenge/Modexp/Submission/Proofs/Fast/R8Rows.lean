import Challenge.Modexp.Submission.Proofs.Fast.SquareRows
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact
import Challenge.Modexp.Submission.Proofs.Fast.R8FirstSuffix

set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The eight square rows from row head 0 to `sq_exit`

Row 0 is the dedicated eight-limb first-row program (`R8RowZero`, mx_major's
`R8ZeroFirstRow`), which needs no zeroed `t` and lands at the second-loop `JUMPDEST`
3833 with the memory `firstMemory mem`.  With a zero scratch word that memory *is* the
machine-carry row model of the zeroed memory (`R8RowZeroExact.firstMemory_eq`), so the
second loop (`R8FirstSuffix.gasSteps`, entered at 3833), the tail and rows 1..7 are the
unchanged `CarryRowGas` / `SquareRows` chain on the model `mpZeroed s mem 8`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R8Rows
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareModel SquareResult SquareRow SquareRows
open CiosCachedMidMemory CarryRowModel StagedOperand

private theorem mul_comm' (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

/-! ## The first-row result as the second-loop entry frame of the row model -/

theorem readWord_midMem1_2336 (mem : ByteArray) (c : UInt256) :
    MachineState.readWord (midMem1 mem c) 2336 = MachineState.readWord mem 2336 := by
  unfold midMem1
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega

/-- `mu = t[n] * inv` of the first-row program is the model's `rowMu`. -/
theorem mu_eq (Q : ByteArray) (c inv : UInt256) (hinv : inv = MachineState.readWord Q 2720) :
    MachineState.readWord (midMem1 Q c) 2336 * inv = rowMu Q 8 := by
  rw [readWord_midMem1_2336, hinv, mul_comm']
  rfl

/-- The carry `addMod t0 (mulMod m0 mu M) M` of the first-row program is the model's `rowC0`. -/
theorem c0_eq (Q : ByteArray) (c m0 : UInt256) (hm0 : m0 = MachineState.readWord Q 224)
    (hinvQ : ((MachineState.readWord Q 224).toNat * (MachineState.readWord Q 2720).toNat + 1) %
      2 ^ 256 = 0)
    (hguard : MachineState.readWord Q 2720 ≠ UInt256.ofNat 1) :
    UInt256.addMod (MachineState.readWord (midMem1 Q c) 2336)
      (UInt256.mulMod m0 (rowMu Q 8) maxWord) maxWord = rowC0 Q 8 := by
  rw [N0Carry.addMod_comm, readWord_midMem1_2336, hm0]
  exact N0Carry.addMod_row_carry _ _ _ hinvQ hguard

theorem result_eq_l2At (s : State) (mem : ByteArray) (tl inv m0 m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8) (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0) :
    R8ZeroFirstRow.result { s with memory := mem } (UInt256.ofNat 4065) (UInt256.ofNat 3417)
        negative32 (l2Target 8) inv m0 m96 m64 m32 (pdst :: ret :: rest) =
      l2At 3668 s
        (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry)
        (overflow (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry)
        (rowMu (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 8)
        (rowC0 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 8)
        2368 8 0 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest) := by
  have hF := R8RowZeroExact.firstMemory_eq s mem hscr
  have hQ224 : MachineState.readWord (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 224 =
      MachineState.readWord mem 224 := by
    rw [readWord_sqL1 _ 8 0 224 _ (by decide) (Or.inl (by decide)),
      StagedMonpro.readWord_mpZeroed s mem 8 224 (by decide) (Or.inl (by decide))]
  have hQ2720 : MachineState.readWord (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 2720 =
      MachineState.readWord mem 2720 := by
    rw [readWord_sqL1 _ 8 0 2720 _ (by decide) (Or.inr (by decide)),
      StagedMonpro.readWord_mpZeroed s mem 8 2720 (by decide) (Or.inr (by decide))]
  have hmu := mu_eq (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
    (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry inv (by rw [hQ2720]; exact hc.inverse)
  have hc0 := c0_eq (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
    (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry m0 (by rw [hQ224]; exact hc.modulusLow)
    (by rw [hQ224, hQ2720]; exact hminv) (by rw [hQ2720, ← hc.inverse]; exact hc.inverseGuard)
  have hx : sqX (mpZeroed s mem 8) 8 0 = MachineState.readWord mem 2592 := by
    unfold sqX
    rw [StagedMonpro.readWord_mpZeroed s mem 8 (aAddr 8 0) (by decide)
      (Or.inr (by unfold aAddr; omega))]
    rfl
  simp only [R8ZeroFirstRow.result, R8ZeroFirstRow.endFrame, l2At, l2Step, l2Target_eight,
    ptrAt_zero, List.cons_append, List.nil_append]
  rw [hF, hmu, hc0, R8ZeroFirstRow.zeroed_first_overflow s mem, hx, hc.lowAddress]
  rfl

/-! ## Row 0: the first-row program, the second loop and the tail -/

def gasSteps_rowZeroToTail (s : State) (mem : ByteArray)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 8) :
    Challenge.EvmProof.GasSteps
      { outState s mem 2368 8 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 4889 }
      (tailState s
        (rowFromL2Carry (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) 8).memory
        (rowFromL2Carry (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) 8).carry
        (rowMu (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 8)
        (overflow (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry)
        2368 8 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest)) := by
  have hcap2 : (pdst :: ret :: rest).length ≤ 1002 := by simp only [List.length_cons]; omega
  have gP := R8RowZero.gasSteps_prologue s mem (sqEnt 8 0) inv m0 m96 m64 m32 aprev
    (pdst :: ret :: rest) hcap2 hrun hcode hfork hnp hact
  rw [result_eq_l2At s mem tl inv m0 m96 m64 m32 pdst ret rest hscr hminv hc] at gP
  have heZ : CiosReadonlyExtra.ExtraCache (mpZeroed s mem 8) m96 m64 m32 :=
    he.of_preserved (StagedMonpro.readWord_mpZeroed s mem 8 96 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s mem 8 64 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s mem 8 32 (by decide) (Or.inl (by decide)))
  have heQ : CiosReadonlyExtra.ExtraCache
      (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heZ 8 0 (by decide) _) _ 2368 8
      (0 + 1) (8 - 1 - 0) (by omega)
  have htl := hc.lowAddress
  subst htl
  exact gP.trans (R8FirstSuffix.gasSteps s _ _ _ _ 2368 0 (UInt256.ofNat 4065)
    (UInt256.ofNat (sqEnt 8 0 + 37)) _ inv m0 (sqX (mpZeroed s mem 8) 8 0) m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact (extraCache_midMem1 heQ _))

def gasSteps_rowZeroNext (s : State) (mem : ByteArray)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hsnap : StagedOperand.Snapshot mem 2368 8) :
    Challenge.EvmProof.GasSteps
      { outState s mem 2368 8 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0)) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 4889 }
      (outState s (sqRowCarry (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) 2368 8 (0 + 1)
        (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest)) :=
  (gasSteps_rowZeroToTail s mem tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun hcode hfork
    hnp hact hscr hminv hc he hsnap).trans
  (CarryRowGas.gasSteps_tailNext s _ _ _ _ 2368 8 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0 + 37))
    inv m0 (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by decide)
    (by omega) jumpDest4710')

/-! ## Rows 0..7 -/

def gasSteps_rowsToExit (s : State) (a0 : UInt256) (M0 : ByteArray)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero M0)
    (hminv : inverseInvariant M0 8)
    (hc : CiosReadonly.ReadonlyCache M0 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 8) :
    Challenge.EvmProof.GasSteps
      { rowState s a0 M0 8 tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 4889 }
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry (mpZeroed s M0 8) 8 8)
        (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 8)) 2368 8 (UInt256.ofNat 4065)
        (UInt256.ofNat (sqEnt 8 8)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqLast (mpZeroed s M0 8) 8 :: pdst :: ret :: rest)) := by
  have ha0 : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
  have hcZ : CiosReadonly.ReadonlyCache (mpZeroed s M0 8) 8 tl inv m0 :=
    hc.of_preserved (StagedMonpro.readWord_mpZeroed s M0 8 2720 (by decide) (Or.inr (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 (32 * 8 - 32) (by decide) (Or.inl (by decide)))
  have heZ : CiosReadonlyExtra.ExtraCache (mpZeroed s M0 8) m96 m64 m32 :=
    he.of_preserved (StagedMonpro.readWord_mpZeroed s M0 8 96 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 64 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 32 (by decide) (Or.inl (by decide)))
  have hminvZ : inverseInvariant (mpZeroed s M0 8) 8 := by
    unfold inverseInvariant
    rw [StagedMonpro.readWord_mpZeroed s M0 8 (32 * 8 - 32) (by decide) (Or.inl (by decide)),
      StagedMonpro.readWord_mpZeroed s M0 8 2720 (by decide) (Or.inr (by decide))]
    exact hminv
  have hsnapZ : StagedOperand.Snapshot (mpZeroed s M0 8) 2368 8 := fun _ _ => rfl
  have g0 := gasSteps_rowZeroNext s M0 tl inv m0 m96 m64 m32 a0 pdst ret rest
    hcap hrun hcode hfork hnp hact hscr hminv hc he hsnap
  have g0' : Challenge.EvmProof.GasSteps
      { rowState s a0 M0 8 tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 4889 }
      (rowState s (UInt256.ofNat 0) (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest 1) := by
    simpa only [rowState, sqRowsCarry, sqTb, sqPrev, sqEnt_succ] using g0
  have next : ∀ i, i < 7 →
      Challenge.EvmProof.GasSteps
        (rowState s (UInt256.ofNat 0) (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest i)
        (rowState s (UInt256.ofNat 0) (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest (i + 1)) := by
    intro i hi
    have g := SquareRows.gasSteps_rowNext s (sqRowsCarry (mpZeroed s M0 8) 8 i) 8 i tl inv m0 m96 m64 m32
      (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 i) pdst ret rest hcap hrun hcode hfork hnp hact
      (Or.inr rfl) (by omega)
      (SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ i (by omega))
      (SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) i (by omega))
      (SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) i (by omega))
      (hsnapZ.sqRowsCarry i (by omega) (by decide))
    rw [sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 i (by omega) (by decide) ha0,
      ← sqRowsCarry_succ, sqEnt_succ 8 i] at g
    exact g
  have last := SquareRows.gasSteps_rowLastToExit s (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7 tl inv m0
    m96 m64 m32 (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7) pdst ret rest hcap hrun hcode hfork
    hnp hact (Or.inr rfl) (by decide)
    (SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 7 (by decide))
    (SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 7 (by decide))
    (SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 7 (by decide))
    (hsnapZ.sqRowsCarry 7 (by decide) (by decide))
  rw [sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7 (by decide) (by decide) ha0,
    ← sqRowsCarry_succ, sqEnt_succ 8 7] at last
  exact (g0'.trans (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => rowState s (UInt256.ofNat 0) (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest (i + 1))
    6 (fun i hi => next (i + 1) (by omega)))).trans last

def gasSteps_rowsZeroWidth (s : State) (a0 : UInt256) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 8)
    (hscr : R8RowZeroExact.ScratchZero M0)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 n) :
    Challenge.EvmProof.GasSteps
      { rowState s a0 M0 n tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 4889 }
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry (mpZeroed s M0 n) n n)
        (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n)) 2368 n (UInt256.ofNat 4065)
        (UInt256.ofNat (sqEnt n n)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqLast (mpZeroed s M0 n) n :: pdst :: ret :: rest)) := by
  subst n
  exact gasSteps_rowsToExit s a0 M0 tl inv m0 m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact hscr hminv hc he hsnap

end Challenge.Modexp.Submission.Proofs.Fast.R8Rows
