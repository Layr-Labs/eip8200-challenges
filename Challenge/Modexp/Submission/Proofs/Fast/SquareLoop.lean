import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128Again
import Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
import Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
import Challenge.Modexp.Submission.Proofs.Fast.FusedMemory
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopRuns
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry
import Challenge.Modexp.Submission.Proofs.Fast.R4Loop
import Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
import Challenge.Modexp.Submission.Proofs.Fast.R4Trace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-!
# The in-kernel squaring loop: `k` squares in one call

For `n ∈ {4, 8}` the caller stores the number of squares in memory word 2624 and enters the
kernel once.  Each round runs the `n` square rows, and `sq_exit` decrements the counter:
while it stays non-zero the conditional subtraction runs as a subroutine and `again`
rebuilds the row-0 state for the next square; on zero the frame's `ret` slot is rewritten to
`after_sq` (3298) and the call leaves through the ordinary exit.

`gasSteps_squareLoop` is the whole call; `SquareLoopMem.sqLoopMem` is its memory and
`SquareLoopMem.sqLoopMem_represents` its value (`k` Montgomery squares).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareModel SquareResult SquareRow SquareRows
open SquareLoopBlocks StagedOperand CarryRowModel CiosCachedMidMemory CiosCachedMacCore

/-! The memory model and its caller-facing lemmas live in `SquareLoopMem`; they are
re-exported here so that the caller side only needs `SquareLoop`. -/
export Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem (sqLoopMem sqLoopMem_zero sqLoopMem_succ sqLoopMem_represents
  sqLoopMem_frame sqLoopMem_fastRepresents_outside sqLoopMem_readWord_outside
  sqLoopMem_readWord_high)

/-! ## The row-0 memory of a square -/

/-- The memory the kernel's `setup` — and the loop's `again` — hands to row 0: the operand
staged at 2368 and the accumulator zeroed. -/
def rowZero (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  mpZeroed s mem n

/-- The specialized first eight-limb row keeps the ordinary frame and changes only its entry PC. -/
def rowZeroState (s : State) (a0 : UInt256) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (ent : UInt256 := UInt256.ofNat (sqEnt n 0)) : State :=
  { CiosCached.outState s M0 2368 n 0 (UInt256.ofNat 4258) ent inv m0
      (tl :: m96 :: m64 :: m32 :: a0 :: pdst :: ret :: rest) with pc := UInt256.ofNat 5062 }

theorem rowZero_eq_input (s : State) (mem : ByteArray) (n : Nat) (hn : n = 4 ∨ n = 8)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1) :
    mpZeroed s (inputMemory mem 2112 n) n = rowZero s (stage mem 2112 n) n := by
  rw [rowZero, show inputMemory mem 2112 n = stage mem 2112 n from by
    unfold inputMemory; rw [if_pos (show eligible mem n from ⟨hn,hguard⟩)]]

theorem sqRound_eq (s : State) (mem : ByteArray) (n c : Nat) :
    SquareLoopMem.sqRound s n c mem =
      LazyCsub.resultMemory (countMem (sqRowsCarry (rowZero s mem n) n n) c) n (SquareLoopMem.roundDst c) := rfl

/-- Configuration words of the call memory survive staging, zeroing, the rows and the
counter store. -/
theorem read_prefix (s : State) (M : ByteArray) (n c addr : Nat) (hn32 : n ≤ 8)
    (_hfast : n = 4 ∨ n = 8) (hd : addr + 32 ≤ 2048 ∨ 2656 ≤ addr) :
    MachineState.readWord (countMem (sqRowsCarry (rowZero s M n) n n) c) addr =
      MachineState.readWord M addr := by
  rw [readWord_countMem_disjoint _ c addr (by omega),
    readWord_sqRowsCarry _ n addr hn32 (by omega) n le_rfl, rowZero,
    readWord_mpZeroed s _ n addr hn32 (by omega)]

theorem read_rowZero (s : State) (M : ByteArray) (n addr : Nat) (hn32 : n ≤ 8)
    (_hfast : n = 4 ∨ n = 8) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
    MachineState.readWord (rowZero s M n) addr = MachineState.readWord M addr := by
  rw [rowZero, readWord_mpZeroed s _ n addr hn32 hd]

/-! ## The loop invariant -/

/-- What the caller guarantees at a square's entry and every round re-establishes: the
configuration words, the cached frame words, the Montgomery inverse and the operand. -/
structure Entry (s : State) (mem : ByteArray) (p a mm : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) : Prop where
  s32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * (p + 2))
  tlw : MachineState.readWord mem 2784 = tl
  tlv : tl = UInt256.ofNat (2080 + 32 * (p + 2))
  ml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * (p + 2) - 32)
  invw : MachineState.readWord mem 2720 = inv
  m0w : MachineState.readWord mem (32 * (p + 2) - 32) = m0
  m96w : MachineState.readWord mem 96 = m96
  m64w : MachineState.readWord mem 64 = m64
  m32w : MachineState.readWord mem 32 = m32
  minv : (m0.toNat * inv.toNat + 1) % 2 ^ 256 = 0
  inverseGuard : inv ≠ UInt256.ofNat 1
  arep : Model.FastRepresents mem 2368 (p + 2) a
  mrep : Model.FastRepresents mem 0 (p + 2) mm
  alt : a < Limbs.radix^(p+2)
  mpos : 0 < mm

namespace Entry

variable {s : State} {mem : ByteArray} {p a mm : Nat} {tl inv m0 m96 m64 m32 : UInt256}

theorem minv' (h : Entry s mem p a mm tl inv m0 m96 m64 m32) :
    ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0 := by
  rw [h.m0w, h.invw]; exact h.minv

/-- The row-0 caches of `CiosReadonly` / `CiosReadonlyExtra` on the staged memory. -/
theorem cache (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    CiosReadonly.ReadonlyCache (rowZero s mem (p + 2)) (p + 2) tl inv m0 :=
  ⟨h.tlv, by
    rw [read_rowZero s mem (p + 2) 2720 hn32 hfast (Or.inr (by decide)), h.invw], by
    rw [read_rowZero s mem (p + 2) (32 * (p + 2) - 32) hn32 hfast (Or.inl (by omega)), h.m0w], h.inverseGuard⟩

theorem extra (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    CiosReadonlyExtra.ExtraCache (rowZero s mem (p + 2)) m96 m64 m32 :=
  ⟨by rw [read_rowZero s mem (p + 2) 96 hn32 hfast (Or.inl (by decide)), h.m96w],
   by rw [read_rowZero s mem (p + 2) 64 hn32 hfast (Or.inl (by decide)), h.m64w],
   by rw [read_rowZero s mem (p + 2) 32 hn32 hfast (Or.inl (by decide)), h.m32w]⟩

theorem inverse (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    inverseInvariant (rowZero s mem (p + 2)) (p + 2) := by
  unfold inverseInvariant
  rw [read_rowZero s mem (p + 2) (32 * (p + 2) - 32) hn32 hfast (Or.inl (by omega)),
    read_rowZero s mem (p + 2) 2720 hn32 hfast (Or.inr (by decide))]
  exact h.minv'

theorem snapshot (s : State) (mem : ByteArray) (p : Nat)
    (_hfast : p + 2 = 4 ∨ p + 2 = 8) :
    StagedOperand.Snapshot (rowZero s mem (p + 2)) 2368 (p + 2) := by
  intro k _; rfl

/-- Every round re-establishes the invariant, with the operand squared. -/
theorem round (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (c : Nat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hodd : mm % 2 = 1) (hmpos : 0 < mm) :
    Entry s (SquareLoopMem.sqRound s (p + 2) c mem) p (SquareLoopMem.sqRoundValue s (p+2) c mem mm) mm
      tl inv m0 m96 m64 m32 where
  s32 := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 2688 (by omega) hn32 hfast (by omega)]
    exact h.s32
  tlw := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 2784 (by omega) hn32 hfast (by omega)]
    exact h.tlw
  tlv := h.tlv
  ml := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 2752 (by omega) hn32 hfast (by omega)]
    exact h.ml
  invw := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 2720 (by omega) hn32 hfast (by omega)]
    exact h.invw
  m0w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c (32 * (p + 2) - 32) (by omega) hn32 hfast
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.m0w
  m96w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 96 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.m96w
  m64w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 64 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.m64w
  m32w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 32 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.m32w
  minv := h.minv
  inverseGuard := h.inverseGuard
  arep := by
    have hrep := SquareLoopMem.sqRound_represents s mem p a mm c hn32 hfast h.arep h.mrep hodd h.alt h.minv'
    simpa only [SquareLoopMem.roundDst] using hrep
  mrep := SquareLoopMem.sqRound_fastRepresents_outside s mem (p + 2) c 0 (p + 2) mm (by omega) hn32 hfast
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) h.mrep
  alt := (SquareLoopMem.sqRound_represents s mem p a mm c hn32 hfast
    h.arep h.mrep hodd h.alt h.minv').1
  mpos := hmpos

end Entry

/-! ## The conditional subtraction inside a round -/

/-- The `CSUB` return state as a record update (definitional). -/
theorem csReturnedState_eq (s : State) (M : ByteArray) (n : Nat) (pdst ret : UInt256)
    (rest : List UInt256) :
    Csub.csReturnedState s M n n pdst ret rest =
      { s with pc := ret, stack := rest, memory := Csub.csResultMemory M n pdst.toNat } := rfl

theorem word2048_toNat : (UInt256.ofNat 512).toNat = 512 := by decide

/-- The CSUB of one round: from `[2048, ret]` above any stack `tail` to `ret` with the
round's memory. -/
def gasSteps_csubRound (s : State) (M : ByteArray) (p c a mm : Nat)
    (ret : UInt256) (tail : List UInt256) (tl inv m0 m96 m64 m32 : UInt256)
    (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (h : Entry s M p a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (lazyCsubState s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) c)
        (UInt256.ofNat (SquareLoopMem.roundDst c)) ret tail)
      { s with pc := ret, stack := tail, memory := SquareLoopMem.sqRound s (p + 2) c M } :=
  (gasSteps_lazyCsubAt s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) c) (p + 2) (SquareLoopMem.roundDst c)
    ret tail hcap hrun hcode hfork hnp hact (by omega) hn32 (by simp only [SquareLoopMem.roundDst]; omega) hjump
    (by rw [read_prefix s M (p + 2) c 2752 hn32 hfast (Or.inr (by decide))]; exact h.ml)
    (by
      rw [read_prefix s M (p + 2) c 2784 hn32 hfast (Or.inr (by decide)), h.tlw]
      exact h.tlv)
    (by
      rw [Csub.csStep_readWord_disjoint _ (p + 2) 2688 (by omega) (Or.inr (by omega)) (p + 2)
        le_rfl, read_prefix s M (p + 2) c 2688 hn32 hfast (Or.inr (by decide))]
      exact h.s32)
    (by
      rw [Csub.csStep_readWord_disjoint _ (p + 2) 2080 (by omega) (Or.inr (by omega)) (p + 2)
          le_rfl,
        readWord_countMem_disjoint _ c 2080 (Or.inl (by omega))]
      exact SquareLoopMem.tn_le_one s M p a mm hn32 hfast h.arep h.mrep h.mpos h.minv') hfast).cast rfl
    (by rw [sqRound_eq])

theorem sqLast_eight (s : State) (M : ByteArray) :
    sqLast (rowZero s M 8) 8 = sqX M 8 7 := by
  change MachineState.readWord (sqRowsCarry (mpZeroed s M 8) 8 7) (aAddr 8 7) = _
  rw [readWord_sqRowsCarry_far _ 8 (aAddr 8 7) (Or.inr (by decide)) 7 (by decide),
    StagedMonpro.readWord_mpZeroed s M 8 (aAddr 8 7) (by decide) (Or.inr (by decide))]
  rfl

theorem rows128 (s : State) (M : ByteArray) :
    MachineState.readWord (sqRowsCarry (rowZero s M 8) 8 8) 128 =
      MachineState.readWord M 128 := by
  rw [readWord_sqRowsCarry _ 8 128 (by decide) (Or.inl (by decide)) 8 le_rfl,
    read_rowZero s M 8 128 (by decide) (Or.inr rfl) (Or.inl (by decide))]

theorem round128 (s : State) (M : ByteArray) (c : Nat) :
    MachineState.readWord (SquareLoopMem.sqRound s 8 c M) 128 =
      MachineState.readWord M 128 :=
  SquareLoopMem.sqRound_readWord_outside s M 8 c 128 (by decide) (by decide) (Or.inr rfl)
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))

/-! ## One round -/

/-- A round that is **not** the last: the rows, `sq_exit`'s decrement, the CSUB subroutine
and `again`, ending at the next square's row-0 head. -/
def gasSteps_roundMore (s : State) (M : ByteArray) (p c a mm : Nat)
    (a0 tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (_hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord M 2624 = UInt256.ofNat (c + 1))
    (h8 : p = 6) (hscr : R8RowZeroExact.ScratchZero M)
    (h : Entry s M p a mm tl inv m0 m96 m64 m32)
    (ent : UInt256 := UInt256.ofNat (sqEnt (p + 2) 0)) :
    Challenge.EvmProof.GasSteps
      (rowZeroState s a0 M (p + 2) tl inv m0 m96 m64 m32
        (UInt256.ofNat 512) ret rest ent)
      (rowZeroState s (sqLast (rowZero s M (p + 2)) (p + 2)) (SquareLoopMem.sqRound s (p + 2) c M) (p + 2)
        tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest (UInt256.ofNat 3858)) := by
  subst p
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  let env := TnM128SquareSteps.environment s hcode' hfork hrun hnp
  let tn := (TnM128SquareFullSteps.finalCache M).tn
  let X := sqRowsCarry (rowZero s M 8) 8 8
  let prev := sqX M 8 7
  let retained := TnM128SquareExit.frameStack tn (MachineState.readWord X 128) 8
    (UInt256.ofNat 2336) (UInt256.ofNat 3858) tl inv m0 m96 m64 m32 prev
    (UInt256.ofNat 512) ret rest
  have hc : TnCacheRowPreserves.Cached M 2368 8 tl inv m0 m96 m64 m32 :=
    ⟨⟨h.tlv, h.invw.symm, h.m0w.symm, h.inverseGuard⟩,
      ⟨h.m96w.symm, h.m64w.symm, h.m32w.symm⟩, h.minv', fun _ _ => rfl⟩
  have g1 := TnM128SquareFullSteps.square_steps s env M a0 tl inv m0 m96 m64 m32
    (UInt256.ofNat 512) ret rest (by omega) hact hc hscr ent
  have hinput : TnM128SquareFirstSteps.input s M a0 tl inv m0 m96 m64 m32
      (UInt256.ofNat 512) ret rest ent =
      rowZeroState s a0 M 8 tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest ent := rfl
  have hcountRows : MachineState.readWord X 2624 = UInt256.ofNat (c+1) := by
    dsimp only [X]
    rw [readWord_sqRowsCarry _ 8 2624 (by decide) (Or.inr (by decide)) 8 le_rfl,
      read_rowZero s M 8 2624 (by decide) (Or.inr rfl) (Or.inr (by decide))]
    exact hcount
  have g2 := TnM128SquareExit.gasSteps_sqExitMore tn (MachineState.readWord X 128) s X 8 c
    (UInt256.ofNat 2336) (UInt256.ofNat 3858) tl inv m0 m96 m64 m32 prev
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode' hfork hnp hact hcpos hc16 hcountRows
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 4232).toNat = true := R4Hooks.jumpDestH2
  have g3 := gasSteps_csubRound s M 6 c a mm (UInt256.ofNat 4232) retained
    tl inv m0 m96 m64 m32
    (by simp only [retained, TnM128SquareExit.frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact hn32 hfast hjump h
  have g4 := TnM128Again.steps s env (SquareLoopMem.sqRound s 8 c M) tn prev
    tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest (by omega) h.tlv
  have hi : TnM128Again.input s (SquareLoopMem.sqRound s 8 c M) tn prev
      tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest =
      { s with
          pc := UInt256.ofNat 4232
          stack := retained
          memory := SquareLoopMem.sqRound s 8 c M } := by
    simp only [TnM128Again.input, TnCacheFrameOps.frame, TnM128SquareExit.frameStack,
      retained, X, rows128, round128, framed, List.cons_append, List.nil_append]
  have ho : TnM128SquareFirstSteps.input s (SquareLoopMem.sqRound s 8 c M) prev
      tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest (UInt256.ofNat 3858) =
      rowZeroState s (sqLast (rowZero s M 8) 8) (SquareLoopMem.sqRound s 8 c M) 8
        tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest (UInt256.ofNat 3858) := by
    rw [sqLast_eight]; rfl
  exact (((g1.cast hinput rfl).trans g2).trans g3).trans (g4.cast hi ho)

/-- The **last** round: the rows, `sq_exit`'s decrement to zero, the `ret` rewrite, the
frame drop and the CSUB, returning to `after_sq` (3298). -/
def gasSteps_roundLast (s : State) (M : ByteArray) (p a mm : Nat)
    (a0 tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (hcds : s.executionEnv.calldata.size < 2^256) (hodd : mm % 2 = 1)
    (hcount : MachineState.readWord M 2624 = UInt256.ofNat 1)
    (h8 : p = 6) (hscr : R8RowZeroExact.ScratchZero M)
    (h : Entry s M p a mm tl inv m0 m96 m64 m32)
    (ent : UInt256 := UInt256.ofNat (sqEnt (p + 2) 0)) :
    Challenge.EvmProof.GasSteps
      (rowZeroState s a0 M (p + 2) tl inv m0 m96 m64 m32
        (UInt256.ofNat 512) ret rest ent)
      { s with pc := UInt256.ofNat 772, stack := rest,
               memory := StagedProduct.memory s (SquareLoopMem.sqRound s (p + 2) 0 M) (p+2) } := by
  subst p
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  let env := TnM128SquareSteps.environment s hcode' hfork hrun hnp
  let tn := (TnM128SquareFullSteps.finalCache M).tn
  let X := sqRowsCarry (rowZero s M 8) 8 8
  let prev := sqX M 8 7
  let retained := TnM128SquareExit.frameStack tn (MachineState.readWord X 128) 8
    (UInt256.ofNat 2336) (UInt256.ofNat 3858) tl inv m0 m96 m64 m32 prev
    (UInt256.ofNat 512) ret rest
  have hc : TnCacheRowPreserves.Cached M 2368 8 tl inv m0 m96 m64 m32 :=
    ⟨⟨h.tlv, h.invw.symm, h.m0w.symm, h.inverseGuard⟩,
      ⟨h.m96w.symm, h.m64w.symm, h.m32w.symm⟩, h.minv', fun _ _ => rfl⟩
  have g1 := TnM128SquareFullSteps.square_steps s env M a0 tl inv m0 m96 m64 m32
    (UInt256.ofNat 512) ret rest (by omega) hact hc hscr ent
  have hinput : TnM128SquareFirstSteps.input s M a0 tl inv m0 m96 m64 m32
      (UInt256.ofNat 512) ret rest ent =
      rowZeroState s a0 M 8 tl inv m0 m96 m64 m32 (UInt256.ofNat 512) ret rest ent := rfl
  have hcountRows : MachineState.readWord X 2624 = UInt256.ofNat 1 := by
    dsimp only [X]
    rw [readWord_sqRowsCarry _ 8 2624 (by decide) (Or.inr (by decide)) 8 le_rfl,
      read_rowZero s M 8 2624 (by decide) (Or.inr rfl) (Or.inr (by decide))]
    exact hcount
  have g2 := TnM128SquareExit.gasSteps_sqExitLast tn (MachineState.readWord X 128) s X 8
    (UInt256.ofNat 2336) (UInt256.ofNat 3858) tl inv m0 m96 m64 m32 prev
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode' hfork hnp hact hcountRows
  have g3 := TnM128SquareExit.gasSteps_last tn (MachineState.readWord X 128) s (countMem X 0) 8
    (UInt256.ofNat 2336) (UInt256.ofNat 3858) tl inv m0 m96 m64 m32 prev
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode' hfork hnp
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 3471).toNat = true := by
    exact Artifact.isValidJumpDest_index 2779 (by rfl)
  have g4 := gasSteps_csubRound s M 6 0 a mm (UInt256.ofNat 3471) retained tl inv m0 m96 m64 m32
    (by simp only [retained, TnM128SquareExit.frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact hn32 hfast hjump h
  have hp := h.round 0 hn32 hfast hodd h.mpos
  have g5 := FusedProductTrace.gasSteps_product tn s (SquareLoopMem.sqRound s 8 0 M) 6
    (SquareLoopMem.sqRoundValue s 8 0 M mm) mm
    (UInt256.ofNat 2336) (UInt256.ofNat 3858) tl inv m0 m96 m64 m32 prev
    (UInt256.ofNat 512) ret rest (by omega) hfast hrun hcode hfork hnp hact hcds hp.minv'
    ⟨hp.tlv, hp.invw.symm, hp.m0w.symm, hp.inverseGuard⟩
    ⟨hp.m96w.symm, hp.m64w.symm, hp.m32w.symm⟩
    hp.arep hp.mrep hp.alt hp.mpos hp.ml (hp.tlw.trans hp.tlv) hp.s32
  have hi : TnM128SquareExit.frameAt tn (MachineState.readWord (SquareLoopMem.sqRound s 8 0 M) 128)
      3471 s (SquareLoopMem.sqRound s 8 0 M) 8 (UInt256.ofNat 2336) (UInt256.ofNat 3858)
      tl inv m0 m96 m64 m32 prev (UInt256.ofNat 512) ret rest =
      { s with
          pc := UInt256.ofNat 3471
          stack := retained
          memory := SquareLoopMem.sqRound s 8 0 M } := by
    simp only [TnM128SquareExit.frameAt, retained, X, rows128, round128, framed]
  exact ((((g1.cast hinput rfl).trans g2).trans g3).trans g4).trans (g5.cast hi rfl)

/-! ## The loop -/

/-- **`k` squares in one kernel call**, from the row-0 head of the first one. -/
def gasSteps_loop (s : State) (p mm : Nat) (tl inv m0 m96 m64 m32 ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm) (h8 : p = 6) :
    ∀ (k : Nat) (M : ByteArray) (a : Nat) (a0 ent : UInt256), 1 ≤ k → k ≤ 16 →
      MachineState.readWord M 2624 = UInt256.ofNat k →
      R8RowZeroExact.ScratchZero M →
      Entry s M p a mm tl inv m0 m96 m64 m32 →
      Challenge.EvmProof.GasSteps
        (rowZeroState s a0 M (p + 2) tl inv m0 m96 m64 m32
          (UInt256.ofNat 512) ret rest ent)
        { s with pc := UInt256.ofNat 772, stack := rest,
                 memory := StagedProduct.memory s (SquareLoopMem.sqRunMem s (p + 2) k M) (p+2) } := by
  intro k
  induction k with
  | zero => intro M a a0 ent hk; exact absurd hk (by omega)
  | succ j ih =>
      intro M a a0 ent _ hk16 hcount hscr h
      match j, ih with
      | 0, _ =>
          exact gasSteps_roundLast s M p a mm a0 tl inv m0 m96 m64 m32 ret rest hcap hrun hcode
            hfork hnp hact hn32 hfast hcds hodd hcount h8 hscr h ent
      | (i + 1), ih =>
          exact (gasSteps_roundMore s M p (i + 1) a mm a0 tl inv m0 m96 m64 m32 ret rest hcap
            hrun hcode hfork hnp hact hn32 hfast hcds (by omega) (by omega) hcount h8 hscr h ent).trans
            (ih (SquareLoopMem.sqRound s (p + 2) (i + 1) M)
              (SquareLoopMem.sqRoundValue s (p+2) (i+1) M mm)
              (sqLast (rowZero s M (p + 2)) (p + 2))
              (UInt256.ofNat 3858)
              (by omega) (by omega)
              (SquareLoopMem.sqRound_count s M (p + 2) (i + 1) (by omega) hn32 hfast (by omega))
              (SquareLoopMem.scratchZero_sqRound s (p + 2) (i + 1) M (by omega) hn32)
              (h.round (i + 1) hn32 hfast hodd hmpos))

/-! ## The R4 rounds (`n = 4`)

For four limbs the hooks send every square through R4 (entered at `R4Hooks.pcR4`): the rows
are replaced by one straight-line routine whose memory is `R4Bridge.rows4`, and the CSUB
returns to H2, which jumps straight back into R4 while rounds remain; the last round's CSUB
returns to the fused product. -/

theorem rows4_eq_r4 (s : State) (M : ByteArray) (a mm : Nat) (tl inv m0 m96 m64 m32 : UInt256)
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    R4Bridge.r4Mem M (R4Bridge.r4Final M allOnes m0 m64 m32 inv) = R4Bridge.rows4 M := by
  have e0 : m0 = MachineState.readWord M 96 := h.m0w.symm
  have e64 : m64 = MachineState.readWord M 64 := h.m64w.symm
  have e32 : m32 = MachineState.readWord M 32 := h.m32w.symm
  have ei : inv = MachineState.readWord M 2720 := h.invw.symm
  subst e0 e64 e32 ei
  rfl

/-- Every R4 round re-establishes the invariant, with the operand squared. -/
theorem Entry.round4 {s : State} {M : ByteArray} {a mm : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) (c : Nat)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm) :
    Entry s (R4Loop.r4Round c M) 2 (R4Loop.r4RoundValue M c mm) mm
      tl inv m0 m96 m64 m32 where
  s32 := by rw [R4Loop.r4Round_readWord_high M c 2688 (by omega)]; exact h.s32
  tlw := by rw [R4Loop.r4Round_readWord_high M c 2784 (by omega)]; exact h.tlw
  tlv := h.tlv
  ml := by rw [R4Loop.r4Round_readWord_high M c 2752 (by omega)]; exact h.ml
  invw := by rw [R4Loop.r4Round_readWord_high M c 2720 (by omega)]; exact h.invw
  m0w := by
    rw [R4Loop.r4Round_readWord_outside M c (32 * (2 + 2) - 32) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.m0w
  m96w := by
    rw [R4Loop.r4Round_readWord_outside M c 96 (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.m96w
  m64w := by
    rw [R4Loop.r4Round_readWord_outside M c 64 (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.m64w
  m32w := by
    rw [R4Loop.r4Round_readWord_outside M c 32 (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.m32w
  minv := h.minv
  inverseGuard := h.inverseGuard
  arep := by
    have hrep := R4Loop.r4Round_represents M a mm c h.arep h.mrep hodd h.alt h.minv'
    simpa only [SquareLoopMem.roundDst] using hrep
  mrep := R4Loop.r4Round_fastRepresents_outside M c 0 (2 + 2) mm (Or.inl (by omega))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) h.mrep
  alt := (R4Loop.r4Round_represents M a mm c h.arep h.mrep hodd h.alt h.minv').1
  mpos := hmpos

/-- R4 itself on the retained frame: from the R4 entry to `sq_exit` with `rows4` in memory. -/
def gasSteps_r4Frame (s : State) (M : ByteArray) (a mm : Nat)
    (pbi ent aprev tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512) ret rest)
      (frameAt pcSqExit s (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 512) ret rest) := by
  have g := R4Trace.gasSteps_r4 {s with memory := M} pbi (UInt256.ofNat 4258)
    (UInt256.ofNat 2336) ent (UInt256.ofNat 0) allOnes (MachineState.readWord M 128)
    inv m0 tl m96 m64 m32 (aprev :: UInt256.ofNat 512 :: ret :: rest)
    (by simp only [List.length_cons]; omega) hcode hfork hrun hnp hact
    CiosCachedMacCore.allOnes_value h.minv h.inverseGuard
  rw [rows4_eq_r4 s M a mm tl inv m0 m96 m64 m32 h] at g
  simpa only [frameAt, frameStack, R4Hooks.pcR4, pcSqExit, List.cons_append, List.nil_append,
    R4Bridge.rows4_readWord_outside M 128 (Or.inl (by decide))]
    using g

/-- The CSUB of an R4 round, on `countMem (rows4 M) c`. -/
def gasSteps_r4Csub (s : State) (M : ByteArray) (a mm c dst : Nat) (ret : UInt256)
    (tail : List UInt256) (tl inv m0 m96 m64 m32 : UInt256)
    (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hdst : dst + 32 * 4 ≤ 2816)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (lazyCsubState s (countMem (R4Bridge.rows4 M) c) (UInt256.ofNat dst) ret tail)
      { s with pc := ret, stack := tail,
               memory := LazyCsub.resultMemory (countMem (R4Bridge.rows4 M) c) 4 dst } :=
  gasSteps_lazyCsubAt s (countMem (R4Bridge.rows4 M) c) 4 dst ret tail hcap hrun hcode hfork hnp hact
    (by norm_num) (by norm_num) hdst hjump
    (by
      rw [readWord_countMem_disjoint _ c 2752 (Or.inr (by norm_num)),
        R4Bridge.rows4_readWord_outside M 2752 (Or.inr (by norm_num))]
      exact h.ml)
    (by
      rw [readWord_countMem_disjoint _ c 2784 (Or.inr (by norm_num)),
        R4Bridge.rows4_readWord_outside M 2784 (Or.inr (by norm_num))]
      exact h.tlw.trans h.tlv)
    (by
      rw [Csub.csStep_readWord_disjoint _ 4 2688 (by omega) (Or.inr (by omega)) 4 le_rfl,
        readWord_countMem_disjoint _ c 2688 (Or.inr (by norm_num)),
        R4Bridge.rows4_readWord_outside M 2688 (Or.inr (by norm_num))]
      exact h.s32)
    (by
      rw [Csub.csStep_readWord_disjoint _ 4 2080 (by omega) (Or.inr (by omega)) 4 le_rfl,
        readWord_countMem_disjoint _ c 2080 (Or.inl (by norm_num))]
      exact LazySquareMemory.r4_tn_le_one M a mm h.arep h.mrep h.mpos h.minv')
    (Or.inl rfl)

/-- An R4 round that is **not** the last: R4, `sq_exit`, the CSUB returning to H2, and H2's
jump back into R4. -/
def gasSteps_r4More (s : State) (M : ByteArray) (c a mm : Nat)
    (pbi ent aprev tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord M 2624 = UInt256.ofNat (c + 1))
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512) ret rest)
      (frameAt R4Hooks.pcR4 s (R4Loop.r4Round c M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 512) ret rest) := by
  have g1 := gasSteps_r4Frame s M a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest hcap hrun
    hcode hfork hnp hact h
  have g2 := gasSteps_sqExitMore s (R4Bridge.rows4 M) 4 c pbi ent tl inv m0 m96 m64 m32 aprev
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode hfork hnp hact hcpos hc16
    (by rw [R4Bridge.rows4_readWord_outside M 2624 (Or.inr (by norm_num))]; exact hcount)
  have hjumpH2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 4232).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
    exact R4Hooks.jumpDestH2
  have g3 := gasSteps_r4Csub s M a mm c 2368 (UInt256.ofNat 4232)
    (frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512) ret rest)
    tl inv m0 m96 m64 m32
    (by simp only [frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact (by norm_num) hjumpH2 h
  have hr : R4Loop.r4Round c M =
      LazyCsub.resultMemory (countMem (R4Bridge.rows4 M) c) 4 2368 := by
    simp only [R4Loop.r4Round, SquareLoopMem.roundDst]
  rw [← hr] at g3
  have g4 := R4Hooks.gasSteps_h2Taken s (R4Loop.r4Round c M) pbi ent tl inv m0 m96 m64 m32 aprev
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode hfork hnp 4 rfl h.tlv
  have hm128 := R4Loop.r4Round_readWord_outside M c 128 (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have hi : frameAt SquareLoopBlocks.pcH2 s (R4Loop.r4Round c M) 4 pbi ent tl inv m0 m96 m64 m32
      aprev (UInt256.ofNat 512) ret rest =
      { s with
          pc := UInt256.ofNat 4232
          memory := R4Loop.r4Round c M
          stack := frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
            (UInt256.ofNat 512) ret rest } := by
    simp only [frameAt, frameStack, SquareLoopBlocks.pcH2, hm128,
      R4Bridge.rows4_readWord_outside M 128 (Or.inl (by decide))]
  exact ((g1.trans g2).trans g3).trans (g4.cast hi rfl)

/-- The **last** R4 round: R4, `sq_exit`'s decrement to zero, `last`, the CSUB returning to the
fused product, and the product itself. -/
def gasSteps_r4Last (s : State) (M : ByteArray) (a mm : Nat)
    (pbi ent aprev tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1)
    (hcount : MachineState.readWord M 2624 = UInt256.ofNat 1)
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512) ret rest)
      { s with pc := UInt256.ofNat 772, stack := rest,
               memory := StagedProduct.memory s (R4Loop.r4Round 0 M) 4 } := by
  have g1 := gasSteps_r4Frame s M a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest hcap hrun
    hcode hfork hnp hact h
  have g2 := gasSteps_sqExitLast s (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode hfork hnp hact
    (by rw [R4Bridge.rows4_readWord_outside M 2624 (Or.inr (by norm_num))]; exact hcount)
  have g3 := gasSteps_last s (countMem (R4Bridge.rows4 M) 0) 4 pbi ent tl inv m0 m96 m64 m32
    aprev (UInt256.ofNat 512) ret rest (by omega) hrun hcode hfork hnp
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 3471).toNat = true := by
    change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3471 = true
    exact Artifact.isValidJumpDest_index 2779 (by rfl)
  have g4 := gasSteps_r4Csub s M a mm 0 2368 (UInt256.ofNat 3471)
    (frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512) ret rest)
    tl inv m0 m96 m64 m32
    (by simp only [frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact (by norm_num) hjump h
  have hr : R4Loop.r4Round 0 M =
      LazyCsub.resultMemory (countMem (R4Bridge.rows4 M) 0) 4 2368 := by
    simp only [R4Loop.r4Round, SquareLoopMem.roundDst]
  rw [← hr] at g4
  have hp := h.round4 0 hodd h.mpos
  have g5 := FusedProductTrace.gasSteps_product (UInt256.ofNat 0) s (R4Loop.r4Round 0 M) 2
    (R4Loop.r4RoundValue M 0 mm) mm pbi ent tl inv m0 m96 m64 m32 aprev
    (UInt256.ofNat 512) ret rest (by omega) (Or.inl rfl) hrun hcode hfork hnp hact hcds hp.minv'
    ⟨hp.tlv, hp.invw.symm, hp.m0w.symm, hp.inverseGuard⟩
    ⟨hp.m96w.symm, hp.m64w.symm, hp.m32w.symm⟩
    hp.arep hp.mrep hp.alt hp.mpos hp.ml (hp.tlw.trans hp.tlv) hp.s32
  have hm128 := R4Loop.r4Round_readWord_outside M 0 128 (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have g3' := g3.cast rfl (show lazyCsubState s (countMem (R4Bridge.rows4 M) 0)
      (UInt256.ofNat 2368) (UInt256.ofNat 3471)
      (frameStack (countMem (R4Bridge.rows4 M) 0) 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 512) ret rest) =
      lazyCsubState s (countMem (R4Bridge.rows4 M) 0) (UInt256.ofNat 2368) (UInt256.ofNat 3471)
      (frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 512) ret rest) by
    rw [frameStack, readWord_countMem_disjoint _ 0 128 (Or.inl (by decide))]; rfl)
  have hi : TnM128SquareExit.frameAt (UInt256.ofNat 0)
      (MachineState.readWord (R4Loop.r4Round 0 M) 128) 3471 s (R4Loop.r4Round 0 M) 4
      pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512) ret rest =
      { s with
          pc := UInt256.ofNat 3471
          memory := R4Loop.r4Round 0 M
          stack := frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
            (UInt256.ofNat 512) ret rest } := by
    simp only [TnM128SquareExit.frameAt, TnM128SquareExit.frameStack, frameStack, framed, hm128,
      R4Bridge.rows4_readWord_outside M 128 (Or.inl (by decide))]
  exact (((g1.trans g2).trans g3').trans g4).trans (g5.cast hi rfl)

/-- **`k` R4 squares**, from the first R4 entry, ending after the fused product. -/
def gasSteps_loop4 (s : State) (mm : Nat) (tl inv m0 m96 m64 m32 ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm)
    (pbi ent aprev : UInt256) :
    ∀ (k : Nat) (M : ByteArray) (a : Nat), 1 ≤ k → k ≤ 16 →
      MachineState.readWord M 2624 = UInt256.ofNat k →
      Entry s M 2 a mm tl inv m0 m96 m64 m32 →
      Challenge.EvmProof.GasSteps
        (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 512)
          ret rest)
        { s with pc := UInt256.ofNat 772, stack := rest,
                 memory := StagedProduct.memory s (R4Loop.r4RunMem k M) 4 } := by
  intro k
  induction k with
  | zero => intro M a hk; exact absurd hk (by omega)
  | succ j ih =>
      intro M a _ hk16 hcount h
      match j, ih with
      | 0, _ =>
          exact gasSteps_r4Last s M a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest hcap hrun
            hcode hfork hnp hact hcds hodd hcount h
      | (i + 1), ih =>
          exact (gasSteps_r4More s M (i + 1) a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest
            hcap hrun hcode hfork hnp hact (by omega) (by omega) hcount h).trans
            (ih (R4Loop.r4Round (i + 1) M) (R4Loop.r4RoundValue M (i+1) mm)
              (by omega) (by omega) (R4Loop.r4Round_count M (i + 1) (by omega))
              (h.round4 (i + 1) hodd hmpos))

/-! ## The whole call -/


/-- **The looped square subroutine of the sqCP1mL artifact**: entered at the kernel's
`common` block with the row head `sq_row` and the counter `k` in memory word 2624, it runs
`k` Montgomery squares of the block at 2048 and returns to `after_sq` (3298). -/
def gasSteps_squareLoop (s : State) (mem : ByteArray) (p a mm k : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 982)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat k)
    (hslotn : rest[2]? = some (UInt256.ofNat (p + 2)))
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * (p + 2) - 32))
    (ha : Model.FastRepresents mem 2112 (p + 2) a) (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (_ham : a < mm) (hmpos : 0 < mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps
      (Cios2Dispatch.commonState s mem 4551 2112 512 (UInt256.ofNat 512) ret rest)
      { s with pc := UInt256.ofNat 772, stack := rest,
               memory := FusedMemory.memory s (p+2) k mem } := by
  have hs (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
      MachineState.readWord (stage mem 2112 (p + 2)) addr = MachineState.readWord mem addr :=
    read_stage_outside mem 2112 (p + 2) addr (by omega)
  have hentry : Entry s (stage mem 2112 (p + 2)) p a mm (MachineState.readWord mem 2784)
      (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * (p + 2) - 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64)
      (MachineState.readWord mem 32) := by
    refine ⟨(hs 2688 (Or.inr (by decide))).trans hs32, hs 2784 (Or.inr (by decide)), htl,
      (hs 2752 (Or.inr (by decide))).trans hml, hs 2720 (Or.inr (by decide)),
      hs (32 * (p + 2) - 32) (Or.inl (by omega)), hs 96 (Or.inl (by decide)),
      hs 64 (Or.inl (by decide)), hs 32 (Or.inl (by decide)), hminv, hguard,
      represents_stage mem (p + 2) a ha, ?_, ha.1, hmpos⟩
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [hs (0 + 32 * j) (Or.inl (by omega))]
  have g1 := Cios2Dispatch.gasSteps_commonSetupInputSq s mem (UInt256.ofNat 4551) 2112 512 (p + 2)
    (UInt256.ofNat 512) ret rest (by omega) hrun hcode hfork hnp hact hfast (by omega)
    (by decide) (by omega) hcds hs32 hml hslotn SquareStagedEntry.jumpDest hguard
      (CiosInverseGuard.inverse_ne_zero _ _ hminv)
  rw [rowZero_eq_input s mem (p + 2) hfast hguard] at g1
  have g2 := SquareStagedEntry.gasSteps_entry s (rowZero s (stage mem 2112 (p + 2)) (p + 2)) (p + 2)
    (UInt256.ofNat 3562) (MachineState.readWord mem 2720)
    (MachineState.readWord mem (32 * (p + 2) - 32))
    (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 :: MachineState.readWord mem 64 ::
      MachineState.readWord mem 32 :: UInt256.ofNat (2112 + 32 * (p + 2) - 32) ::
      UInt256.ofNat 512 :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp
  by_cases hp : p = 2
  · subst hp
    have hz (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
        MachineState.readWord (rowZero s (stage mem 2112 (2 + 2)) (2 + 2)) addr =
          MachineState.readWord (stage mem 2112 (2 + 2)) addr :=
      read_rowZero s _ (2 + 2) addr (by norm_num) (Or.inl rfl) hd
    have hentry4 : Entry s (rowZero s (stage mem 2112 (2 + 2)) (2 + 2)) 2 a mm
        (MachineState.readWord mem 2784) (MachineState.readWord mem 2720)
        (MachineState.readWord mem (32 * (2 + 2) - 32)) (MachineState.readWord mem 96)
        (MachineState.readWord mem 64) (MachineState.readWord mem 32) :=
      ⟨(hz 2688 (Or.inr (by decide))).trans hentry.s32,
        (hz 2784 (Or.inr (by decide))).trans hentry.tlw,
        hentry.tlv, (hz 2752 (Or.inr (by decide))).trans hentry.ml,
        (hz 2720 (Or.inr (by decide))).trans hentry.invw,
        (hz (32 * (2 + 2) - 32) (Or.inl (by decide))).trans hentry.m0w,
        (hz 96 (Or.inl (by decide))).trans hentry.m96w,
        (hz 64 (Or.inl (by decide))).trans hentry.m64w,
        (hz 32 (Or.inl (by decide))).trans hentry.m32w, hentry.minv, hentry.inverseGuard,
        represents_zeroed_stage s _ (2 + 2) a (by norm_num) hentry.arep,
        (Model.fastRepresents_congr (a := stage mem 2112 (2 + 2))
          (by intro j hj; rw [hz (0 + 32 * j) (Or.inl (by omega))]) mm).1 hentry.mrep,
        hentry.alt, hentry.mpos⟩
    have g3 := R4Hooks.gasSteps_h1Taken s (rowZero s (stage mem 2112 (2 + 2)) (2 + 2))
      (UInt256.ofNat (ptrAt (2368 + 32 * (2 + 2) - 32) 0)) (UInt256.ofNat 3562)
      (MachineState.readWord mem 2784) (MachineState.readWord mem 2720)
      (MachineState.readWord mem (32 * (2 + 2) - 32)) (MachineState.readWord mem 96)
      (MachineState.readWord mem 64) (MachineState.readWord mem 32)
      (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) (UInt256.ofNat 512) ret rest (by omega)
      hrun hcode hfork hnp (2 + 2) rfl htl
    have g4 := gasSteps_loop4 s mm (MachineState.readWord mem 2784)
      (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * (2 + 2) - 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64)
      (MachineState.readWord mem 32) ret rest hcap hrun hcode hfork hnp hact hcds hodd hmpos
      (UInt256.ofNat (ptrAt (2368 + 32 * (2 + 2) - 32) 0)) (UInt256.ofNat 3562)
      (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) k (rowZero s (stage mem 2112 (2 + 2)) (2 + 2)) a
      hk hk16 ((hz 2624 (Or.inr le_rfl)).trans ((hs 2624 (Or.inr (by decide))).trans hcount))
      hentry4
    have hcall : R4Loop.loopMem s (2 + 2) k mem =
        R4Loop.r4RunMem k (rowZero s (stage mem 2112 (2 + 2)) (2 + 2)) := by
      rw [R4Loop.loopMem, if_pos (show (2 + 2 : Nat) = 4 by norm_num)]
      cases k with
      | zero => omega
      | succ k => rfl
    change Challenge.EvmProof.GasSteps _
      { s with
        pc := UInt256.ofNat 772
        stack := rest
        memory := StagedProduct.memory s (R4Loop.loopMem s (2 + 2) k mem) (2 + 2) }
    rw [hcall]
    exact ((g1.trans g2).trans g3).trans g4
  · have h6 : p = 6 := by omega
    subst h6
    have g3 := R4Hooks.gasSteps_h1Fall s (rowZero s (stage mem 2112 (6 + 2)) (6 + 2))
      (UInt256.ofNat (ptrAt (2368 + 32 * (6 + 2) - 32) 0)) (UInt256.ofNat (sqEnt (6 + 2) 0))
      (MachineState.readWord mem 2784) (MachineState.readWord mem 2720)
      (MachineState.readWord mem (32 * (6 + 2) - 32)) (MachineState.readWord mem 96)
      (MachineState.readWord mem 64) (MachineState.readWord mem 32)
      (UInt256.ofNat (2112 + 32 * (6 + 2) - 32)) (UInt256.ofNat 512) ret rest (by omega)
      hrun hcode hfork hnp (6 + 2) (by omega) htl
    have hcall : R4Loop.loopMem s (6 + 2) k mem =
        SquareLoopMem.sqRunMem s (6 + 2) k (rowZero s (stage mem 2112 (6 + 2)) (6 + 2)) := by
      rw [rowZero, SquareLoopMem.sqRunMem_mpZeroed s (6 + 2) k _ hk, R4Loop.loopMem,
        if_neg (show ¬ (6 + 2 = 4) by omega)]
      cases k with
      | zero => omega
      | succ k => rfl
    have hz (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
        MachineState.readWord (rowZero s (stage mem 2112 (6 + 2)) (6 + 2)) addr =
          MachineState.readWord (stage mem 2112 (6 + 2)) addr :=
      read_rowZero s _ (6 + 2) addr hn32 hfast hd
    have hentryZ : Entry s (rowZero s (stage mem 2112 (6 + 2)) (6 + 2)) 6 a mm
        (MachineState.readWord mem 2784) (MachineState.readWord mem 2720)
        (MachineState.readWord mem (32 * (6 + 2) - 32)) (MachineState.readWord mem 96)
        (MachineState.readWord mem 64) (MachineState.readWord mem 32) :=
      ⟨(hz 2688 (Or.inr (by decide))).trans hentry.s32,
        (hz 2784 (Or.inr (by decide))).trans hentry.tlw,
        hentry.tlv, (hz 2752 (Or.inr (by decide))).trans hentry.ml,
        (hz 2720 (Or.inr (by decide))).trans hentry.invw,
        (hz (32 * (6 + 2) - 32) (Or.inl (by omega))).trans hentry.m0w,
        (hz 96 (Or.inl (by decide))).trans hentry.m96w,
        (hz 64 (Or.inl (by decide))).trans hentry.m64w,
        (hz 32 (Or.inl (by decide))).trans hentry.m32w, hentry.minv, hentry.inverseGuard,
        represents_zeroed_stage s _ (6 + 2) a hn32 hentry.arep,
        (Model.fastRepresents_congr (a := stage mem 2112 (6 + 2))
          (by intro j hj; rw [hz (0 + 32 * j) (Or.inl (by omega))]) mm).1 hentry.mrep,
        hentry.alt, hentry.mpos⟩
    change Challenge.EvmProof.GasSteps _
      { s with
        pc := UInt256.ofNat 772
        stack := rest
        memory := StagedProduct.memory s (R4Loop.loopMem s (6 + 2) k mem) (6 + 2) }
    rw [hcall]
    exact ((g1.trans g2).trans g3).trans (gasSteps_loop s 6 mm (MachineState.readWord mem 2784)
      (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * (6 + 2) - 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64)
      (MachineState.readWord mem 32) ret rest hcap hrun hcode hfork hnp hact hn32 hfast hcds
      hodd hmpos rfl k (rowZero s (stage mem 2112 (6 + 2)) (6 + 2)) a
      (UInt256.ofNat (2112 + 32 * (6 + 2) - 32)) (UInt256.ofNat (sqEnt (6 + 2) 0)) hk hk16
      ((hz 2624 (Or.inr le_rfl)).trans ((hs 2624 (Or.inr (by decide))).trans hcount))
      (R8RowZeroExact.scratchZero_mpZeroed s _ (6 + 2) (by omega)) hentryZ)

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoop
