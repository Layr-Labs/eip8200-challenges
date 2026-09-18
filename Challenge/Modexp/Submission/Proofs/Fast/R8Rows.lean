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
`R8ZeroFirstRow`), which needs no zeroed `t` and lands at the second-loop join
3791 with the cell holding the row's first-loop carry and the memory untouched at the
scratch word.  With a zero scratch word that memory is the machine-carry row model of the
zeroed memory under `unflush` (`R8RowZeroExact.firstProduct_unflush`), so the second loop
(`R8FirstSuffix.gasSteps`, entered at 3791), the tail and rows 1..7 are the unchanged
`CarryRowGas` / `SquareRows` slot-channel chain on the model `mpZeroed s mem 8`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R8Rows
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareModel SquareResult SquareRow SquareRows
open CiosCachedMidMemory CarryRowModel StagedOperand CarryScratchAgreement

private theorem mul_comm' (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

/-! ## The first-row result as the second-loop entry frame of the row model -/

/-- `mu = t[n] * inv` of the first-row program is the model's `rowMu`. -/
theorem mu_eq (Q : ByteArray) (inv : UInt256) (hinv : inv = MachineState.readWord Q 2720) :
    MachineState.readWord Q 2336 * inv = rowMu Q 8 := by
  rw [hinv, mul_comm']
  rfl

/-- The carry `addMod t0 (mulMod m0 mu M) M` of the first-row program is the model's `rowC0`. -/
theorem c0_eq (Q : ByteArray) (m0 : UInt256) (hm0 : m0 = MachineState.readWord Q 224)
    (hinvQ : ((MachineState.readWord Q 224).toNat * (MachineState.readWord Q 2720).toNat + 1) %
      2 ^ 256 = 0)
    (hguard : MachineState.readWord Q 2720 ≠ UInt256.ofNat 1) :
    UInt256.addMod (MachineState.readWord Q 2336)
      (UInt256.mulMod m0 (rowMu Q 8) maxWord) maxWord = rowC0 Q 8 := by
  rw [N0Carry.addMod_comm, hm0]
  exact N0Carry.addMod_row_carry _ _ _ hinvQ hguard

/-- The row-0 first-loop result of the reassembled kernel: the model's `sqL1` on the real
memory with the entry scratch word of `mem` re-installed. -/
abbrev Q0 (s : State) (mem : ByteArray) : MacState :=
  sqL1 (unflush mem (mpZeroed s mem 8)) 8 0 (UInt256.ofNat 0)

theorem Q0_eq (s : State) (mem : ByteArray) :
    Q0 s mem = ⟨unflush mem (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory,
      (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry⟩ :=
  sqL1_unflush mem (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0) (by decide)

theorem readWord_Q0_low (s : State) (mem : ByteArray) (addr : Nat) (haddr : addr + 32 ≤ 2048) :
    MachineState.readWord (Q0 s mem).memory addr = MachineState.readWord mem addr := by
  rw [Q0_eq]
  show MachineState.readWord (unflush mem (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory)
    addr = _
  rw [readWord_unflush _ _ addr (Or.inl (by omega)),
    readWord_sqL1 _ 8 0 addr _ (by decide) (Or.inl (by omega)),
    StagedMonpro.readWord_mpZeroed s mem 8 addr (by decide) (Or.inl (by omega))]

theorem readWord_Q0_2720 (s : State) (mem : ByteArray) :
    MachineState.readWord (Q0 s mem).memory 2720 = MachineState.readWord mem 2720 := by
  rw [Q0_eq]
  show MachineState.readWord (unflush mem (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory)
    2720 = _
  rw [readWord_unflush _ _ 2720 (Or.inr (by decide)),
    readWord_sqL1 _ 8 0 2720 _ (by decide) (Or.inr (by decide)),
    StagedMonpro.readWord_mpZeroed s mem 8 2720 (by decide) (Or.inr (by decide))]

theorem result_eq_l2At (s : State) (mem : ByteArray) (tl inv m0 m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8) (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0) :
    R8ZeroFirstRow.result { s with memory := mem } (UInt256.ofNat 4190) (UInt256.ofNat 3547)
        negative32 inv m0 m96 m64 m32 (pdst :: ret :: rest) =
      l2At 3791 s (Q0 s mem).memory (UInt256.ofNat 0)
        (rowMu (Q0 s mem).memory 8) (rowC0 (Q0 s mem).memory 8)
        2368 8 0 0 (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 8 0 + 37)) (Q0 s mem).carry inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest) := by
  have hF := R8RowZeroExact.firstProduct_unflush s mem hscr
  have hFm : (R8ZeroFirstRow.firstProduct mem).memory = (Q0 s mem).memory := by
    rw [Q0_eq, hF.1]
    show unflush mem (midMem1 _ _) = unflush mem _
    unfold midMem1
    exact unflush_writeWord _ _ _ (YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _)
  have hFc : (R8ZeroFirstRow.firstProduct mem).carry = (Q0 s mem).carry := by
    rw [Q0_eq]
    exact (R8ZeroFirstRow.firstProduct_bridge s mem).2
  have hQ224 := readWord_Q0_low s mem 224 (by decide)
  have hQ2720 := readWord_Q0_2720 s mem
  have hmu := mu_eq (Q0 s mem).memory inv (by rw [hQ2720]; exact hc.inverse)
  have hc0 := c0_eq (Q0 s mem).memory m0 (by rw [hQ224]; exact hc.modulusLow)
    (by rw [hQ224, hQ2720]; exact hminv) (by rw [hQ2720, ← hc.inverse]; exact hc.inverseGuard)
  have hx : sqX (mpZeroed s mem 8) 8 0 = MachineState.readWord mem 2592 := by
    unfold sqX
    rw [StagedMonpro.readWord_mpZeroed s mem 8 (aAddr 8 0) (by decide)
      (Or.inr (by unfold aAddr; omega))]
    rfl
  simp only [R8ZeroFirstRow.result, R8ZeroFirstRow.endFrame, l2At, l2Step,
    ptrAt_zero, List.cons_append, List.nil_append]
  rw [hFm, hFc, hmu, hc0, hx, hc.lowAddress]
  rfl

/-! ## Row 0: the first-row program, the second loop and the tail -/

/-- The row-zero entry: the frame at the row-zero program (5013) on the real memory
`mem`, with an arbitrary first-loop register word `e` (the program re-materializes it) and
an arbitrary cell `cy` (the program installs the row carry over it). -/
def entryState (s : State) (mem : ByteArray) (e : Nat) (cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { outState s mem 2368 8 0 (UInt256.ofNat 4190) (UInt256.ofNat e) cy inv m0
    (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 5013 }

def gasSteps_rowZeroToTail (s : State) (mem : ByteArray) (e : Nat)
    (cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (entryState s mem e cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (tailState s (fromL2S (Q0 s mem) 8).memory (fromL2S (Q0 s mem) 8).carry
        (rowMu (Q0 s mem).memory 8) (UInt256.ofNat 0)
        2368 8 0 (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 8 0 + 37)) (Q0 s mem).carry inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest)) := by
  have hcap2 : (pdst :: ret :: rest).length ≤ 1002 := by simp only [List.length_cons]; omega
  have gP := R8RowZero.gasSteps_prologue s mem e cy inv m0 m96 m64 m32 aprev
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
  have heQ0 : CiosReadonlyExtra.ExtraCache (Q0 s mem).memory m96 m64 m32 := by
    rw [Q0_eq]
    exact extraCache_unflush heQ
  have htl := hc.lowAddress
  subst htl
  exact gP.trans (R8FirstSuffix.gasSteps s _ _ _ _ 2368 0 (UInt256.ofNat 4190)
    (UInt256.ofNat (sqEnt 8 0 + 37)) (Q0 s mem).carry _ inv m0 (sqX (mpZeroed s mem 8) 8 0)
    m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact heQ0)

theorem slotOverflow_zero (c : UInt256) : slotOverflow (UInt256.ofNat 0) c = UInt256.ofNat 0 := by
  unfold slotOverflow
  rw [R8ZeroFirstRow.zero_add_word, R8ZeroFirstRow.lt_self_word]

/-- The row model with a zero entering cell: the writeback's cell input is the head's carry
itself. -/
theorem fromMemS_zero (q : MacState) (n : Nat) :
    fromMemS q (UInt256.ofNat 0) n = tailMemS (fromL2S q n).memory q.carry (fromL2S q n).carry := by
  unfold fromMemS
  rw [R8ZeroFirstRow.zero_add_word]

theorem fromSlot_zero (q : MacState) (n : Nat) :
    fromSlot q (UInt256.ofNat 0) n = slotOverflow q.carry (fromL2S q n).carry + UInt256.ofNat 0 := by
  unfold fromSlot
  rw [R8ZeroFirstRow.zero_add_word, slotOverflow_zero]

def gasSteps_rowZeroNext (s : State) (mem : ByteArray) (e : Nat)
    (cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (entryState s mem e cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (outState s (fromMemS (Q0 s mem) (UInt256.ofNat 0) 8) 2368 8 (0 + 1)
        (UInt256.ofNat 4190) (UInt256.ofNat (sqEnt 8 0 + 37))
        (fromSlot (Q0 s mem) (UInt256.ofNat 0) 8) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest)) := by
  rw [fromMemS_zero, fromSlot_zero]
  exact (gasSteps_rowZeroToTail s mem e cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hrun
      hcode hfork hnp hact hscr hminv hc he).trans
    (CarryRowGas.gasSteps_tailNext s _ _ _ _ 2368 8 0 (UInt256.ofNat 4190)
      (UInt256.ofNat (sqEnt 8 0 + 37)) (Q0 s mem).carry
      inv m0 (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by decide)
      (by omega) jumpDest4710')

/-! ## Rows 0..7 -/

/-- **All eight rows of an eight-limb square** from the row-zero entry: the real memory is
the flushed machine-carry model `sqRowsCarry (mpZeroed s M0 8) 8 8` and the cell holds its
scratch word. -/
def gasSteps_rowsToExit (s : State) (a0 : UInt256) (M0 : ByteArray) (e : Nat)
    (cy tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero M0)
    (hminv : inverseInvariant M0 8)
    (hc : CiosReadonly.ReadonlyCache M0 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (entryState s M0 e cy tl inv m0 m96 m64 m32 a0 pdst ret rest)
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry (mpZeroed s M0 8) 8 8)
        (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 8)) 2368 8 (UInt256.ofNat 4190)
        (UInt256.ofNat (sqEnt 8 8))
        (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 8) 2080) inv m0
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
  -- row 0 through the dedicated program, bridged to the loop invariant at row head 1
  have g0 := gasSteps_rowZeroNext s M0 e cy tl inv m0 m96 m64 m32 a0 pdst ret rest
    hcap hrun hcode hfork hnp hact hscr hminv hc he
  have hb := sqRow_unflush M0 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0) (by decide) (by decide)
    (by decide)
  rw [readWord_mpZeroed_tn] at hb
  rw [hb.1, hb.2] at g0
  have g0' : Challenge.EvmProof.GasSteps
      (entryState s M0 e cy tl inv m0 m96 m64 m32 a0 pdst ret rest)
      (rowState s (UInt256.ofNat 0) M0 (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest 1) := by
    simpa only [rowState, sqRowsCarry, sqTb, sqPrev, sqEnt_succ] using g0
  -- rows 1..6
  have next : ∀ i, i < 7 →
      Challenge.EvmProof.GasSteps
        (rowState s (UInt256.ofNat 0) M0 (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest i)
        (rowState s (UInt256.ofNat 0) M0 (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest (i + 1)) :=
    fun i hi => SquareRows.gasSteps_rowStateNext s (UInt256.ofNat 0) M0 (mpZeroed s M0 8) 8 tl inv m0
      m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (Or.inr rfl) ha0 hminvZ hcZ heZ hsnapZ
      i (by omega)
  -- row 7 to `sq_exit`, with the flush
  have last := SquareRows.gasSteps_rowLastToExit s (unflush M0 (sqRowsCarry (mpZeroed s M0 8) 8 7)) 8 7
    (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) 2080) tl inv m0 m96 m64 m32
    (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7) pdst ret rest hcap hrun hcode hfork hnp hact
    (Or.inr rfl) (by decide)
    (inverse_unflush M0 _ 8 (by decide) (by decide)
      (SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 7 (by decide)))
    (readonlyCache_unflush (SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 7 (by decide))
      (by decide) (by decide))
    (extraCache_unflush (SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 7 (by decide)))
    (fun _ _ => rfl)
  have hb7 := sqRow_unflush M0 (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7
    (sqTb (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7) (by decide) (by decide) (by decide)
  rw [sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7 (by decide) (by decide) ha0, hb7.1, hb7.2,
    ← sqRowsCarry_succ, sqRowsCarry_unflush_flush, sqEnt_succ 8 7, sqX_unflush] at last
  exact (g0'.trans (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => rowState s (UInt256.ofNat 0) M0 (mpZeroed s M0 8) 8 tl inv m0 m96 m64 m32 pdst ret rest (i + 1))
    6 (fun i hi => next (i + 1) (by omega)))).trans last

def gasSteps_rowsZeroWidth (s : State) (a0 : UInt256) (M0 : ByteArray) (n e : Nat)
    (cy tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 8)
    (hscr : R8RowZeroExact.ScratchZero M0)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      { outState s M0 2368 n 0 (UInt256.ofNat 4190) (UInt256.ofNat e) cy inv m0
        (tl :: m96 :: m64 :: m32 :: a0 :: pdst :: ret :: rest) with pc := UInt256.ofNat 5013 }
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry (mpZeroed s M0 n) n n)
        (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n)) 2368 n (UInt256.ofNat 4190)
        (UInt256.ofNat (sqEnt n n))
        (MachineState.readWord (sqRowsCarry (mpZeroed s M0 n) n n) 2080) inv m0
        (tl :: m96 :: m64 :: m32 :: sqLast (mpZeroed s M0 n) n :: pdst :: ret :: rest)) := by
  subst n
  exact gasSteps_rowsToExit s a0 M0 e cy tl inv m0 m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact hscr hminv hc he

end Challenge.Modexp.Submission.Proofs.Fast.R8Rows
