import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
import Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
import Challenge.Modexp.Submission.Proofs.Fast.FusedMemory
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopRuns
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry
import Challenge.Modexp.Submission.Proofs.Fast.R4Loop
import Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
import Challenge.Modexp.Submission.Proofs.Fast.R4SquareScratchAgreement
import Challenge.Modexp.Submission.Proofs.Fast.R4Trace
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
import Challenge.Modexp.Submission.Proofs.Fast.SquareRoundC

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-!
# The in-kernel squaring loop: `k` squares in one call

For `n ∈ {4, 8}` the caller leaves the number of squares minus one in the frame's `pdst` slot
(dead until pc 3471 overwrites it) and enters the kernel once.  Each round runs the `n` square rows, and `sq_exit` decrements the counter:
while it stays non-zero `sq_exit` resets the carry slot and the row pointer, and the
conditional subtraction runs as a subroutine returning straight to the next row-0 head
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
  { CiosCached.outState s M0 2368 n 0 (UInt256.ofNat 4293) ent m32 m64 m0
      (tl :: m96 :: inv :: UInt256.ofNat 0 :: a0 :: pdst :: ret :: rest) with pc := UInt256.ofNat 5092 }

theorem rowZero_eq_input (s : State) (mem : ByteArray) (n : Nat) (hn : n = 4 ∨ n = 8)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1) :
    mpZeroed s (inputMemory mem 2112 n) n = rowZero s (stage mem 2112 n) n := by
  rw [rowZero, show inputMemory mem 2112 n = stage mem 2112 n from by
    unfold inputMemory; rw [if_pos (show eligible mem n from ⟨hn,hguard⟩)]]

theorem partial_eq_input (mem : ByteArray) (n : Nat) (hn : n = 4 ∨ n = 8)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1) :
    SquarePartialClear.memory (inputMemory mem 2112 n) =
      SquarePartialClear.memory (stage mem 2112 n) := by
  rw [show inputMemory mem 2112 n = stage mem 2112 n from by
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
  tlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * (p + 2))
  tlv : tl = MachineState.readWord mem 224
  ml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * (p + 2) - 32)
  invw : MachineState.readWord mem 2720 = inv
  m0w : MachineState.readWord mem (16 * (p + 2) + 32) = m0
  m96w : MachineState.readWord mem 96 = m96
  m64w : MachineState.readWord mem 64 = m64
  m32w : MachineState.readWord mem 32 = m32
  minv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat * inv.toNat + 1) % 2 ^ 256 = 0
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
  rw [h.invw]; exact h.minv

/-- The row-0 caches of `CiosReadonly` / `CiosReadonlyExtra` on the staged memory. -/
theorem cache (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 8)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    CiosReadonly.ReadonlyCache (rowZero s mem (p + 2)) (p + 2) tl inv m0 :=
  ⟨by rw [read_rowZero s mem (p + 2) 224 hn32 hfast (Or.inl (by decide))]; exact h.tlv, by
    rw [read_rowZero s mem (p + 2) 2720 hn32 hfast (Or.inr (by decide)), h.invw], by
    rw [read_rowZero s mem (p + 2) (16 * (p + 2) + 32) hn32 hfast (Or.inl (by omega)), h.m0w], h.inverseGuard⟩

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
  tlv := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 224 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.tlv
  ml := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 2752 (by omega) hn32 hfast (by omega)]
    exact h.ml
  invw := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 2720 (by omega) hn32 hfast (by omega)]
    exact h.invw
  m0w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c (16 * (p + 2) + 32) (by omega) hn32 hfast
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
  minv := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c (32 * (p + 2) - 32) (by omega) hn32 hfast
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.minv
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

/-! ## The eight-limb rounds (n8g, rarej, st8)

A round runs the eight square rows from row 0 (5092) to the `n8` block (4207) with the carry word
`tn` still on the stack.  For `tn = 0` the block copies `t → a` inline; otherwise the carry
continuation stores the row head at `0x820` and calls the eight-limb subtraction `s8` (or, in the
last round, goes through `last` and the lazy gate).  The new memory `roundC M` agrees with v9's
`sqRound` outside `0x820` (`SquareRoundC.Same`), which no later consumer reads. -/

open SquareRoundC in
/-- The memory an eight-limb round leaves. -/
def roundC (M : ByteArray) : ByteArray :=
  if (TnM128SquareFullSteps.finalCache M).tn = UInt256.ofNat 0 then
    copy8 (TnM128SquareFullSteps.finalCache M).memory
  else sub8 (TnCacheMemory.lift (TnM128SquareFullSteps.finalCache M).memory (UInt256.ofNat 4293))

open SquareRoundC TnCacheMemory in
theorem roundC_same (s : State) (M : ByteArray) (c : Nat) (hscr : R8RowZeroExact.ScratchZero M)
    (htn : (MachineState.readWord (sqRowsCarry (mpZeroed s M 8) 8 8) 2080).toNat ≤ 1) :
    Same (roundC M) (SquareLoopMem.sqRound s 8 c M) := by
  have hl := TnM128SquareFullSteps.final_lift s M hscr
  rw [← hl, read_lift] at htn
  show Same (roundC M) (LazyCsub.resultMemory (sqRowsCarry (mpZeroed s M 8) 8 8) 8 2368)
  rw [← hl]
  unfold roundC
  by_cases h0 : (TnM128SquareFullSteps.finalCache M).tn = UInt256.ofNat 0
  · rw [if_pos h0, h0]
    exact same_copy _
  · rw [if_neg h0]
    have h1 : (TnM128SquareFullSteps.finalCache M).tn = UInt256.ofNat 1 := by
      have hne : (TnM128SquareFullSteps.finalCache M).tn.toNat ≠ 0 := fun hz =>
        h0 (Challenge.EvmProof.Word.word_ext (by rw [hz]; decide))
      apply Challenge.EvmProof.Word.word_ext
      rw [show (UInt256.ofNat 1).toNat = 1 from by decide]
      omega
    rw [h1]
    exact same_sub _ _

/-- The square's memory reads like the call memory away from the scratch block. -/
theorem final_read (s : State) (M : ByteArray) (hscr : R8RowZeroExact.ScratchZero M) (addr : Nat)
    (hd : addr + 32 ≤ 2048 ∨ 2656 ≤ addr) :
    MachineState.readWord (TnM128SquareFullSteps.finalCache M).memory addr =
      MachineState.readWord M addr := by
  rw [← TnCacheMemory.read_lift_outside _ (TnM128SquareFullSteps.finalCache M).tn addr (by omega),
    TnM128SquareFullSteps.final_lift s M hscr]
  exact read_prefix s M 8 0 addr (by decide) (Or.inr rfl) hd

namespace Entry

variable {s : State} {p a mm : Nat} {tl inv m0 m96 m64 m32 : UInt256}

/-- The invariant ignores the carry word. -/
theorem ofSame {A B : ByteArray} (hs : SquareRoundC.Same A B)
    (h : Entry s B p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 8) :
    Entry s A p a mm tl inv m0 m96 m64 m32 where
  s32 := (hs.readWord 2688 (Or.inr (by decide))).trans h.s32
  tlw := (hs.readWord 2784 (Or.inr (by decide))).trans h.tlw
  tlv := h.tlv.trans (hs.readWord 224 (Or.inl (by decide))).symm
  ml := (hs.readWord 2752 (Or.inr (by decide))).trans h.ml
  invw := (hs.readWord 2720 (Or.inr (by decide))).trans h.invw
  m0w := (hs.readWord (16 * (p + 2) + 32) (Or.inl (by omega))).trans h.m0w
  m96w := (hs.readWord 96 (Or.inl (by decide))).trans h.m96w
  m64w := (hs.readWord 64 (Or.inl (by decide))).trans h.m64w
  m32w := (hs.readWord 32 (Or.inl (by decide))).trans h.m32w
  minv := by rw [hs.readWord (32 * (p + 2) - 32) (Or.inl (by omega))]; exact h.minv
  inverseGuard := h.inverseGuard
  arep := (Model.fastRepresents_congr (a := A) (b := B)
    (fun j hj => hs.readWord (2368 + 32 * j) (Or.inr (by omega))) a).2 h.arep
  mrep := (Model.fastRepresents_congr (a := A) (b := B)
    (fun j hj => hs.readWord (0 + 32 * j) (Or.inl (by omega))) mm).2 h.mrep
  alt := h.alt
  mpos := h.mpos

end Entry

/-- The rows' exit is the retained frame at `n8`. -/
theorem exitState_eq (s : State) (F : ByteArray) (tn aprev w3 tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) :
    TnM128SquareFinishSteps.exitState s F tn 8 aprev w3 tl inv m0 m96 m64 m32 dst ret rest =
      TnM128SquareExit.frameAt tn (MachineState.readWord F 128) 4207 s F 8 (UInt256.ofNat 0) w3
        (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 aprev dst ret rest := rfl

/-- The retained frame at 5092 is the next square's row-0 input. -/
theorem input_eq (s : State) (X : ByteArray) (aprev w3 tl inv m0 m96 m64 m32 dst ret ent : UInt256)
    (rest : List UInt256) :
    TnM128SquareExit.frameAt (UInt256.ofNat 0) (MachineState.readWord X 128) 5092 s X 8
        (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64 m32 aprev dst ret rest =
      TnM128SquareFirstSteps.input s X aprev w3 tl inv m0 m96 m64 m32 dst ret rest ent := rfl

/-- The rows of a round, as far as the `n8` block. -/
def gasSteps_rows (s : State) (M : ByteArray) (a mm : Nat)
    (a0 w3 tl inv m0 m96 m64 m32 dst ret ent : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hw3 : w3 = MachineState.readWord M 192)
    (h : Entry s M 6 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (TnM128SquareFirstSteps.input s M a0 w3 tl inv m0 m96 m64 m32 dst ret rest ent)
      (TnM128SquareExit.frameAt (TnM128SquareFullSteps.finalCache M).tn
        (MachineState.readWord (TnM128SquareFullSteps.finalCache M).memory 128) 4207 s
        (TnM128SquareFullSteps.finalCache M).memory 8 (UInt256.ofNat 0) w3 (UInt256.ofNat 3875)
        tl inv m0 m96 m64 m32 (sqX M 8 7) dst ret rest) := by
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  let env := TnM128SquareSteps.environment s hcode' hfork hrun hnp
  have hc : TnCacheRowPreserves.Cached M 2368 8 tl inv m0 m96 m64 m32 :=
    ⟨⟨h.tlv, h.invw.symm, h.m0w.symm, h.inverseGuard⟩,
      ⟨h.m96w.symm, h.m64w.symm, h.m32w.symm⟩, h.minv', fun _ _ => rfl⟩
  exact (TnM128SquareFullSteps.square_steps s env M a0 w3 tl inv m0 m96 m64 m32 dst ret rest
    (by omega) hact hc hw3 ent).cast rfl (exitState_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem jumpH2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 5092).toNat = true := by
  change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5092 = true
  exact Artifact.isValidJumpDest_index 3996 (by rfl)

theorem jumpSetup : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3487).toNat = true := by
  change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3487 = true
  exact Artifact.isValidJumpDest_index 2716 (by rfl)

theorem rare_isTrue (M : ByteArray)
    (h0 : ¬ (TnM128SquareFullSteps.finalCache M).tn = UInt256.ofNat 0) :
    UInt256.isTrue (TnM128SquareFullSteps.finalCache M).tn := by
  show (TnM128SquareFullSteps.finalCache M).tn.toNat ≠ 0
  intro hz
  exact h0 (Challenge.EvmProof.Word.word_ext (by rw [hz]; decide))

theorem flagWord (F : ByteArray) :
    (MachineState.readWord (TnCacheMemory.lift F (UInt256.ofNat 4293)) 2080).toNat ≠ 0 := by
  rw [TnCacheMemory.read_lift]; decide

/-- A round that is **not** the last: the rows, then the inline copy (`tn = 0`) or the
subtraction `s8` (`tn ≠ 0`), both returning to the next square's row 0 (5092). -/
def gasSteps_roundMore (s : State) (M : ByteArray) (c a mm : Nat)
    (a0 w3 tl inv m0 m96 m64 m32 ret ent : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hc15 : c + 1 ≤ 15)
    (hscr : R8RowZeroExact.ScratchZero M) (hw3 : w3 = MachineState.readWord M 192)
    (h : Entry s M 6 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (TnM128SquareFirstSteps.input s M a0 w3 tl inv m0 m96 m64 m32 (UInt256.ofNat (c + 1)) ret rest
        ent)
      (TnM128SquareFirstSteps.input s (roundC M) (sqX M 8 7) w3 tl inv m0 m96 m64 m32
        (UInt256.ofNat c) ret rest (UInt256.ofNat 3875)) := by
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  let F := (TnM128SquareFullSteps.finalCache M).memory
  have g1 := gasSteps_rows s M a mm a0 w3 tl inv m0 m96 m64 m32 (UInt256.ofNat (c + 1)) ret ent rest
    hcap hrun hcode hfork hnp hact hw3 h
  by_cases h0 : (TnM128SquareFullSteps.finalCache M).tn = UInt256.ofNat 0
  · rw [h0] at g1
    have g2 := TnM128SquareExit.gasSteps_n8aZero (MachineState.readWord F 128) s F 8 w3
      (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) (UInt256.ofNat (c + 1)) ret rest
      (by omega) hrun hcode' hfork hnp
    have g3 := TnM128SquareExit.gasSteps_n8bMore (MachineState.readWord F 128) s F 8 c w3
      (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) ret rest (by omega) hact hrun hcode'
      hfork hnp (by omega)
    have hm : roundC M = SquareRoundC.copy8 F := by unfold roundC; rw [if_pos h0]
    have hend : TnM128SquareExit.frameAt (UInt256.ofNat 0) (MachineState.readWord F 128) 5092 s
        (TnM128SquareExit.copyMem F) 8 (UInt256.ofNat 256) w3 (UInt256.ofNat 3875) tl inv m0 m96
        m64 m32 (sqX M 8 7) (UInt256.ofNat c) ret rest =
        TnM128SquareFirstSteps.input s (roundC M) (sqX M 8 7) w3 tl inv m0 m96 m64 m32
          (UInt256.ofNat c) ret rest (UInt256.ofNat 3875) := by
      rw [hm, ← input_eq, SquareRoundC.copy8_readWord F 128 (Or.inl (by decide))]
      rfl
    exact ((g1.trans g2).trans g3).cast rfl hend
  · have g2 := TnM128SquareExit.gasSteps_n8aRare (TnM128SquareFullSteps.finalCache M).tn
      (MachineState.readWord F 128) s F 8 w3 (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7)
      (UInt256.ofNat (c + 1)) ret rest (by omega) hrun hcode' hfork hnp (rare_isTrue M h0)
    have g3 := TnM128SquareExit.gasSteps_rareMore (MachineState.readWord F 128) s F 8 c w3
      (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) ret rest (by omega) hact hrun hcode'
      hfork hnp (by omega)
    let X := TnCacheMemory.lift F (UInt256.ofNat 4293)
    let stack := TnM128SquareExit.frameStack (UInt256.ofNat 0) (MachineState.readWord F 128) 8
      (UInt256.ofNat 256) w3 (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7)
      (UInt256.ofNat c) ret rest
    have hX (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2656 ≤ addr) :
        MachineState.readWord X addr = MachineState.readWord M addr := by
      rw [TnCacheMemory.read_lift_outside _ _ addr (by omega)]
      exact final_read s M hscr addr hd
    have hs32 : MachineState.readWord (Csub.csStep X 8 8).memory 2688 = UInt256.ofNat (32 * 8) := by
      rw [Csub.csStep_readWord_disjoint X 8 2688 (by decide) (Or.inr (by decide)) 8 le_rfl,
        hX 2688 (Or.inr (by decide))]
      exact h.s32
    have hflag : (MachineState.readWord (Csub.csStep X 8 8).memory 2080).toNat ≠ 0 := by
      rw [Csub.csStep_readWord_disjoint X 8 2080 (by decide) (Or.inr (by decide)) 8 le_rfl]
      exact flagWord F
    have g4 := Csub.gasSteps_csFixedFrom8Flag s X (UInt256.ofNat 2368) (UInt256.ofNat 5092) stack
      (by simp only [stack, TnM128SquareExit.frameStack, List.length_append, List.length_cons,
        List.length_nil]; omega)
      hrun hcode hact hfork hnp jumpH2 hs32 (by decide) hflag
    have hm : roundC M = SquareRoundC.sub8 X := by unfold roundC; rw [if_neg h0]
    have hstart : TnM128SquareExit.s8At s X (UInt256.ofNat 5092) stack =
        Csub.csFixedState s X 8 0 4374 (UInt256.ofNat 2368) (UInt256.ofNat 5092) stack := rfl
    have hend : Csub.subFlagReturnedState s X 8 (UInt256.ofNat 2368) (UInt256.ofNat 5092) stack =
        TnM128SquareFirstSteps.input s (roundC M) (sqX M 8 7) w3 tl inv m0 m96 m64 m32
          (UInt256.ofNat c) ret rest (UInt256.ofNat 3875) := by
      rw [hm, ← input_eq, SquareRoundC.sub8_readWord X 128 (Or.inl (by decide)),
        TnCacheMemory.read_lift_outside _ _ 128 (Or.inl (by decide))]
      rfl
    exact ((g1.trans g2).trans g3).trans ((g4.cast hstart.symm rfl).cast rfl hend)

/-- The **last** round: the rows, the copy or the subtraction (through `last` and the lazy gate),
and the fused product at 3487. -/
def gasSteps_roundLast (s : State) (M : ByteArray) (a mm : Nat)
    (a0 w3 tl inv m0 m96 m64 m32 ret ent : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hodd : mm % 2 = 1) (hscr : R8RowZeroExact.ScratchZero M)
    (hw3 : w3 = MachineState.readWord M 192)
    (h : Entry s M 6 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (TnM128SquareFirstSteps.input s M a0 w3 tl inv m0 m96 m64 m32 (UInt256.ofNat 0) ret rest ent)
      { s with pc := UInt256.ofNat 772, stack := rest,
               memory := StagedProduct.memory s (SquareLoopMem.sqRound s 8 0 M) 8 } := by
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  let F := (TnM128SquareFullSteps.finalCache M).memory
  have g1 := gasSteps_rows s M a mm a0 w3 tl inv m0 m96 m64 m32 (UInt256.ofNat 0) ret ent rest
    hcap hrun hcode hfork hnp hact hw3 h
  have hsame := roundC_same s M 0 hscr
    (SquareLoopMem.tn_le_one s M 6 a mm (by decide) (Or.inr rfl) h.arep h.mrep h.mpos h.minv')
  have hp := (h.round 0 (by decide) (Or.inr rfl) hodd h.mpos).ofSame hsame (by decide)
  have g4 := FusedProductTrace.gasSteps_product (UInt256.ofNat 0) s (roundC M) 6
    (SquareLoopMem.sqRoundValue s 8 0 M mm) mm (UInt256.ofNat 256) w3 (UInt256.ofNat 3875)
    tl inv m0 m96 m64 m32 (sqX M 8 7) allOnes ret rest (by omega) (Or.inr rfl) hrun hcode hfork hnp
    hact hcds hp.minv' ⟨hp.tlv, hp.invw.symm, hp.m0w.symm, hp.inverseGuard⟩
    ⟨hp.m96w.symm, hp.m64w.symm, hp.m32w.symm⟩ hp.arep hp.mrep hp.alt hp.mpos hp.ml hp.tlw hp.s32
    (fun _ => hw3.trans ((hsame.readWord 192 (Or.inl (by decide))).trans
      (SquareLoopMem.sqRound_readWord_outside s M 8 0 192 (by decide) (by decide) (Or.inr rfl)
        (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)))).symm)
  have hfin : StagedProduct.memory s (roundC M) (6 + 2) =
      StagedProduct.memory s (SquareLoopMem.sqRound s 8 0 M) 8 := hsame.stagedProduct s 8
  by_cases h0 : (TnM128SquareFullSteps.finalCache M).tn = UInt256.ofNat 0
  · rw [h0] at g1
    have g2 := TnM128SquareExit.gasSteps_n8aZero (MachineState.readWord F 128) s F 8 w3
      (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) (UInt256.ofNat 0) ret rest
      (by omega) hrun hcode' hfork hnp
    have g3 := TnM128SquareExit.gasSteps_n8bLast (MachineState.readWord F 128) s F 8 w3
      (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) ret rest (by omega) hact hrun hcode'
      hfork hnp
    have hm : roundC M = SquareRoundC.copy8 F := by unfold roundC; rw [if_pos h0]
    have hmid : TnM128SquareExit.frameAt (UInt256.ofNat 0) (MachineState.readWord F 128) 3487 s
        (TnM128SquareExit.copyMem F) 8 (UInt256.ofNat 256) w3 (UInt256.ofNat 3875) tl inv m0 m96
        m64 m32 (sqX M 8 7) allOnes ret rest =
        TnM128SquareExit.frameAt (UInt256.ofNat 0)
          (MachineState.readWord (roundC M) 128) 3487 s (roundC M) (6 + 2)
          (UInt256.ofNat 256) w3 (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) allOnes
          ret rest := by
      rw [hm, SquareRoundC.copy8_readWord F 128 (Or.inl (by decide))]
      rfl
    exact ((g1.trans g2).trans g3).trans (g4.cast hmid.symm (by rw [hfin]))
  · have g2 := TnM128SquareExit.gasSteps_n8aRare (TnM128SquareFullSteps.finalCache M).tn
      (MachineState.readWord F 128) s F 8 w3 (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7)
      (UInt256.ofNat 0) ret rest (by omega) hrun hcode' hfork hnp (rare_isTrue M h0)
    have g3 := TnM128SquareExit.gasSteps_rareLast (MachineState.readWord F 128) s F 8 w3
      (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) ret rest (by omega) hact hrun hcode'
      hfork hnp
    let X := TnCacheMemory.lift F (UInt256.ofNat 4293)
    let stack := TnM128SquareExit.frameStack (UInt256.ofNat 0) (MachineState.readWord F 128) 8
      (UInt256.ofNat 256) w3 (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) allOnes ret rest
    have hs : MachineState.readWord X 2688 = UInt256.ofNat (32 * 8) := by
      rw [TnCacheMemory.read_lift_outside _ _ 2688 (Or.inr (by decide)),
        final_read s M hscr 2688 (Or.inr (by decide))]
      exact h.s32
    have g5 := SquareRoundC.gasSteps_lazyFlag8 s X (UInt256.ofNat 3487) stack
      (by simp only [stack, TnM128SquareExit.frameStack, List.length_append, List.length_cons,
        List.length_nil]; omega)
      hrun hcode hfork hnp hact jumpSetup hs (flagWord F)
    have hm : roundC M = SquareRoundC.sub8 X := by unfold roundC; rw [if_neg h0]
    have hmid : { s with pc := UInt256.ofNat 3487, stack := stack, memory := SquareRoundC.sub8 X } =
        TnM128SquareExit.frameAt (UInt256.ofNat 0)
          (MachineState.readWord (roundC M) 128) 3487 s (roundC M) (6 + 2)
          (UInt256.ofNat 256) w3 (UInt256.ofNat 3875) tl inv m0 m96 m64 m32 (sqX M 8 7) allOnes
          ret rest := by
      rw [hm, SquareRoundC.sub8_readWord X 128 (Or.inl (by decide)),
        TnCacheMemory.read_lift_outside _ _ 128 (Or.inl (by decide))]
      rfl
    exact ((g1.trans g2).trans g3).trans ((g5.cast rfl hmid).trans
      (g4.cast rfl (by rw [hfin])))

/-! ## The loop -/

/-- **`k` squares in one kernel call**, from the row-0 head of the first one. -/
def gasSteps_loop (s : State) (mm : Nat) (w3 tl inv m0 m96 m64 m32 ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm) :
    ∀ (k : Nat) (M : ByteArray) (a : Nat) (a0 ent : UInt256), 1 ≤ k → k ≤ 16 →
      R8RowZeroExact.ScratchZero M → w3 = MachineState.readWord M 192 →
      Entry s M 6 a mm tl inv m0 m96 m64 m32 →
      Challenge.EvmProof.GasSteps
        (TnM128SquareFirstSteps.input s M a0 w3 tl inv m0 m96 m64 m32 (UInt256.ofNat (k - 1)) ret
          rest ent)
        { s with pc := UInt256.ofNat 772, stack := rest,
                 memory := StagedProduct.memory s (SquareLoopMem.sqRunMem s 8 k M) 8 } := by
  intro k
  induction k with
  | zero => intro M a a0 ent hk; exact absurd hk (by omega)
  | succ j ih =>
      intro M a a0 ent _ hk16 hscr hw3 h
      match j, ih with
      | 0, _ =>
          exact gasSteps_roundLast s M a mm a0 w3 tl inv m0 m96 m64 m32 ret ent rest hcap hrun hcode
            hfork hnp hact hcds hodd hscr hw3 h
      | (i + 1), ih =>
          have hsame := roundC_same s M (i + 1) hscr
            (SquareLoopMem.tn_le_one s M 6 a mm (by decide) (Or.inr rfl) h.arep h.mrep h.mpos
              h.minv')
          have hr := h.round (i + 1) (by decide) (Or.inr rfl) hodd hmpos
          have g := (gasSteps_roundMore s M i a mm a0 w3 tl inv m0 m96 m64 m32 ret ent rest hcap
            hrun hcode hfork hnp hact (by omega) hscr hw3 h).trans
            (ih (roundC M) (SquareLoopMem.sqRoundValue s 8 (i + 1) M mm) (sqX M 8 7)
              (UInt256.ofNat 3875) (by omega) (by omega)
              (hsame.scratchZero (SquareLoopMem.scratchZero_sqRound s 8 (i + 1) M (by omega)
                (by decide)))
              (hw3.trans ((hsame.readWord 192 (Or.inl (by decide))).trans
                (SquareLoopMem.sqRound_readWord_outside s M 8 (i + 1) 192 (by decide) (by decide)
                  (Or.inr rfl) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
                  (Or.inl (by decide)))).symm)
              (hr.ofSame hsame (by decide)))
          exact g.cast rfl (by rw [hsame.sqRunMem s 8 (i + 1) (by omega)]; rfl)

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
  tlv := by
    rw [R4Loop.r4Round_readWord_outside M c 224 (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.tlv
  ml := by rw [R4Loop.r4Round_readWord_high M c 2752 (by omega)]; exact h.ml
  invw := by rw [R4Loop.r4Round_readWord_high M c 2720 (by omega)]; exact h.invw
  m0w := by
    rw [R4Loop.r4Round_readWord_outside M c (16 * (2 + 2) + 32) (Or.inl (by omega))
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
  minv := by
    rw [R4Loop.r4Round_readWord_outside M c (32 * (2 + 2) - 32) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.minv
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
    (pbi ent aprev tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcSqExit s (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
        pdst ret rest) := by
  have g := R4Trace.gasSteps_r4 {s with memory := M} pbi (UInt256.ofNat 4293)
    (MachineState.readWord M 192) ent m32 allOnes (MachineState.readWord M 128)
    m64 m0 tl m96 inv (UInt256.ofNat 0) (aprev :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hcode hfork hrun hnp hact
    CiosCachedMacCore.allOnes_value (by rw [← h.m0w]; exact h.minv) h.inverseGuard
  rw [rows4_eq_r4 s M a mm tl inv m0 m96 m64 m32 h] at g
  simpa only [frameAt, frameStack, R4Hooks.pcR4, pcSqExit, List.cons_append, List.nil_append,
    R4Bridge.rows4_readWord_outside M 128 (Or.inl (by decide)),
    R4Bridge.rows4_readWord_outside M 192 (Or.inl (by decide))]
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
      exact h.tlw)
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

/-- An R4 round that is **not** the last: R4, `e4` and the shared counter block, and the
CSUB returning straight into R4. -/
def gasSteps_r4More (s : State) (M : ByteArray) (c a mm : Nat)
    (pbi ent aprev tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat c) ret rest)
      (frameAt R4Hooks.pcR4 s (R4Loop.r4Round c M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c - 1)) ret rest) := by
  have g1 := gasSteps_r4Frame s M a mm pbi ent aprev tl inv m0 m96 m64 m32 (UInt256.ofNat c) ret
    rest hcap hrun hcode hfork hnp hact h
  have hc1 : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
  have g2 := (gasSteps_sqExitMore s (R4Bridge.rows4 M) 4 (c - 1) pbi ent tl inv m0 m96 m64 m32
    aprev ret rest (by omega) hrun hcode hfork hnp (by omega)).cast (by rw [hc1]) rfl
  have hjumpR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 4610).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
    exact R4Hooks.jumpDestR4
  have g3 := gasSteps_r4Csub s M a mm c 2368 (UInt256.ofNat 4610)
    (frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat (c - 1)) ret
      rest)
    tl inv m0 m96 m64 m32
    (by simp only [frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact (by norm_num) hjumpR4 h
  have hr : R4Loop.r4Round c M =
      LazyCsub.resultMemory (countMem (R4Bridge.rows4 M) c) 4 2368 := by
    simp only [R4Loop.r4Round, SquareLoopMem.roundDst]
  rw [← hr] at g3
  have hm128 := R4Loop.r4Round_readWord_outside M c 128 (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have hm192 := R4Loop.r4Round_readWord_outside M c 192 (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have hi : frameAt R4Hooks.pcR4 s (R4Loop.r4Round c M) 4 pbi ent tl inv m0 m96 m64 m32
      aprev (UInt256.ofNat (c - 1)) ret rest =
      { s with
          pc := UInt256.ofNat 4610
          memory := R4Loop.r4Round c M
          stack := frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
            (UInt256.ofNat (c - 1)) ret rest } := by
    simp only [frameAt, frameStack, R4Hooks.pcR4, hm128, hm192,
      R4Bridge.rows4_readWord_outside M 128 (Or.inl (by decide)),
      R4Bridge.rows4_readWord_outside M 192 (Or.inl (by decide))]
  exact ((g1.trans g2).trans g3).cast rfl hi.symm

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
    (h : Entry s M 2 a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 0) ret rest)
      { s with pc := UInt256.ofNat 772, stack := rest,
               memory := StagedProduct.memory s (R4Loop.r4Round 0 M) 4 } := by
  have g1 := gasSteps_r4Frame s M a mm pbi ent aprev tl inv m0 m96 m64 m32 (UInt256.ofNat 0) ret
    rest hcap hrun hcode hfork hnp hact h
  have g2 := gasSteps_sqExitLast s (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
    ret rest (by omega) hrun hcode hfork hnp
  have g3 := gasSteps_last s (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32
    aprev allOnes ret rest (by omega) hrun hcode hfork hnp
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 3487).toNat = true := by
    change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3487 = true
    exact Artifact.isValidJumpDest_index 2716 (by rfl)
  have g4 := gasSteps_r4Csub s M a mm 0 2368 (UInt256.ofNat 3487)
    (frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev allOnes ret rest)
    tl inv m0 m96 m64 m32
    (by simp only [frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact (by norm_num) hjump h
  have hr : R4Loop.r4Round 0 M =
      LazyCsub.resultMemory (countMem (R4Bridge.rows4 M) 0) 4 2368 := by
    simp only [R4Loop.r4Round, SquareLoopMem.roundDst]
  rw [← hr] at g4
  have hp := h.round4 0 hodd h.mpos
  have g5 := FusedProductTrace.gasSteps_product (UInt256.ofNat 0) s (R4Loop.r4Round 0 M) 2
    (R4Loop.r4RoundValue M 0 mm) mm pbi (MachineState.readWord (R4Loop.r4Round 0 M) 192) ent tl inv
    m0 m96 m64 m32 aprev allOnes ret rest (by omega) (Or.inl rfl) hrun hcode hfork hnp hact hcds hp.minv'
    ⟨hp.tlv, hp.invw.symm, hp.m0w.symm, hp.inverseGuard⟩
    ⟨hp.m96w.symm, hp.m64w.symm, hp.m32w.symm⟩
    hp.arep hp.mrep hp.alt hp.mpos hp.ml hp.tlw hp.s32 (fun h => absurd h (by decide))
  have hm128 := R4Loop.r4Round_readWord_outside M 0 128 (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have hm192 := R4Loop.r4Round_readWord_outside M 0 192 (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have hi : TnM128SquareExit.frameAt (UInt256.ofNat 0)
      (MachineState.readWord (R4Loop.r4Round 0 M) 128) 3487 s (R4Loop.r4Round 0 M) 4
      pbi (MachineState.readWord (R4Loop.r4Round 0 M) 192) ent tl inv m0 m96 m64 m32 aprev allOnes
      ret rest =
      { s with
          pc := UInt256.ofNat 3487
          memory := R4Loop.r4Round 0 M
          stack := frameStack (R4Bridge.rows4 M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
            allOnes ret rest } := by
    simp only [TnM128SquareExit.frameAt, TnM128SquareExit.frameStack, frameStack, framed, hm128,
      hm192, R4Bridge.rows4_readWord_outside M 128 (Or.inl (by decide)),
      R4Bridge.rows4_readWord_outside M 192 (Or.inl (by decide))]
  exact (((g1.trans g2).trans g3).trans g4).trans (g5.cast hi rfl)

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
      Entry s M 2 a mm tl inv m0 m96 m64 m32 →
      Challenge.EvmProof.GasSteps
        (frameAt R4Hooks.pcR4 s M 4 pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat (k - 1))
          ret rest)
        { s with pc := UInt256.ofNat 772, stack := rest,
                 memory := StagedProduct.memory s (R4Loop.r4RunMem k M) 4 } := by
  intro k
  induction k with
  | zero => intro M a hk; exact absurd hk (by omega)
  | succ j ih =>
      intro M a _ hk16 h
      match j, ih with
      | 0, _ =>
          exact gasSteps_r4Last s M a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest hcap hrun
            hcode hfork hnp hact hcds hodd h
      | (i + 1), ih =>
          exact (gasSteps_r4More s M (i + 1) a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest
            hcap hrun hcode hfork hnp hact (by omega) (by omega) h).trans
            (ih (R4Loop.r4Round (i + 1) M) (R4Loop.r4RoundValue M (i+1) mm)
              (by omega) (by omega)
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
    (hw : rest[1]? = some (UInt256.ofNat (32 * (p + 2))))
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
      (Cios2Dispatch.commonState s mem 4582 2112 512 (UInt256.ofNat (k - 1)) ret rest)
      { s with pc := UInt256.ofNat 772, stack := rest,
               memory := FusedMemory.memory s (p+2) k mem } := by
  have hs (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
      MachineState.readWord (stage mem 2112 (p + 2)) addr = MachineState.readWord mem addr :=
    read_stage_outside mem 2112 (p + 2) addr (by omega)
  have hentry : Entry s (stage mem 2112 (p + 2)) p a mm (MachineState.readWord mem 224)
      (MachineState.readWord mem 2720) (MachineState.readWord mem (16 * (p + 2) + 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64)
      (MachineState.readWord mem 32) := by
    refine ⟨(hs 2688 (Or.inr (by decide))).trans hs32, (hs 2784 (Or.inr (by decide))).trans htl,
      (hs 224 (Or.inl (by decide))).symm,
      (hs 2752 (Or.inr (by decide))).trans hml, hs 2720 (Or.inr (by decide)),
      hs (16 * (p + 2) + 32) (Or.inl (by omega)), hs 96 (Or.inl (by decide)),
      hs 64 (Or.inl (by decide)), hs 32 (Or.inl (by decide)),
      (by rw [hs (32 * (p + 2) - 32) (Or.inl (by omega))]; exact hminv), hguard,
      represents_stage mem (p + 2) a ha, ?_, ha.1, hmpos⟩
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [hs (0 + 32 * j) (Or.inl (by omega))]
  have g1 := Cios2Dispatch.gasSteps_commonSetupInputSq s mem (UInt256.ofNat 4582) 2112 512 (p + 2)
    (UInt256.ofNat (k - 1)) ret rest (by omega) hrun hcode hfork hnp hact hfast (by omega)
    (by decide) (by omega) hcds hs32 hml hw hslotn SquareStagedEntry.jumpDest hguard
      (CiosInverseGuard.inverse_ne_zero _ _ hminv)
  rw [partial_eq_input mem (p + 2) hfast hguard] at g1
  have g2 := SquareStagedEntry.gasSteps_entry s (SquarePartialClear.memory (stage mem 2112 (p + 2))) (p + 2)
    (UInt256.ofNat 3579) (MachineState.readWord mem 32) (MachineState.readWord mem 64)
    (MachineState.readWord mem (16 * (p + 2) + 32))
    (MachineState.readWord mem 224 :: MachineState.readWord mem 96 :: MachineState.readWord mem 2720 ::
      UInt256.ofNat 0 :: UInt256.ofNat (2112 + 32 * (p + 2) - 32) ::
      UInt256.ofNat (k - 1) :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact
  by_cases hp : p = 2
  · subst hp
    have hz (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
        MachineState.readWord (SquarePartialClear.memory (stage mem 2112 (2 + 2))) addr =
          MachineState.readWord (stage mem 2112 (2 + 2)) addr :=
      SquarePartialClear.readWord_outside _ addr (by omega)
    have hentry4 : Entry s (SquarePartialClear.memory (stage mem 2112 (2 + 2))) 2 a mm
        (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
        (MachineState.readWord mem (16 * (2 + 2) + 32)) (MachineState.readWord mem 96)
        (MachineState.readWord mem 64) (MachineState.readWord mem 32) :=
      ⟨(hz 2688 (Or.inr (by decide))).trans hentry.s32,
        (hz 2784 (Or.inr (by decide))).trans hentry.tlw,
        hentry.tlv.trans (hz 224 (Or.inl (by decide))).symm, (hz 2752 (Or.inr (by decide))).trans hentry.ml,
        (hz 2720 (Or.inr (by decide))).trans hentry.invw,
        (hz (16 * (2 + 2) + 32) (Or.inl (by decide))).trans hentry.m0w,
        (hz 96 (Or.inl (by decide))).trans hentry.m96w,
        (hz 64 (Or.inl (by decide))).trans hentry.m64w,
        (hz 32 (Or.inl (by decide))).trans hentry.m32w,
        (by rw [hz (32 * (2 + 2) - 32) (Or.inl (by omega))]; exact hentry.minv), hentry.inverseGuard,
        SquarePartialClear.fastRepresents_outside _ 2368 (2 + 2) a (Or.inr (by decide)) hentry.arep,
        (Model.fastRepresents_congr (a := stage mem 2112 (2 + 2))
          (by intro j hj; rw [hz (0 + 32 * j) (Or.inl (by omega))]) mm).1 hentry.mrep,
        hentry.alt, hentry.mpos⟩
    have g3 := R4Hooks.gasSteps_h1Taken s (SquarePartialClear.memory (stage mem 2112 (2 + 2)))
      (SquareStagedEntry.qWord (2 + 2)) (UInt256.ofNat 3579)
      (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
      (MachineState.readWord mem (16 * (2 + 2) + 32)) (MachineState.readWord mem 96)
      (MachineState.readWord mem 64) (MachineState.readWord mem 32)
      (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) (UInt256.ofNat (k - 1)) ret rest (by omega)
      hrun hcode hfork hnp (2 + 2) rfl SquareStagedEntry.qWord_four
    have g4 := gasSteps_loop4 s mm (MachineState.readWord mem 224)
      (MachineState.readWord mem 2720) (MachineState.readWord mem (16 * (2 + 2) + 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64)
      (MachineState.readWord mem 32) ret rest hcap hrun hcode hfork hnp hact hcds hodd hmpos
      (SquareStagedEntry.qWord (2 + 2)) (UInt256.ofNat 3579)
      (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) k (SquarePartialClear.memory (stage mem 2112 (2 + 2))) a
      hk hk16 hentry4
    have hcall : R4Loop.loopMem s (2 + 2) k mem =
        R4Loop.r4RunMem k (SquarePartialClear.memory (stage mem 2112 (2 + 2))) := by
      rw [R4Loop.loopMem, if_pos (show (2 + 2 : Nat) = 4 by norm_num)]
      cases k with
      | zero => omega
      | succ k =>
          exact (R4SquareScratchAgreement.r4RunMem_partial_eq s (stage mem 2112 4)
            (k + 1) (by omega)).symm
    change Challenge.EvmProof.GasSteps _
      { s with
        pc := UInt256.ofNat 772
        stack := rest
        memory := StagedProduct.memory s (R4Loop.loopMem s (2 + 2) k mem) (2 + 2) }
    rw [hcall]
    exact ((g1.trans g2).trans g3).trans g4
  · have h6 : p = 6 := by omega
    subst h6
    have g3 := R4Hooks.gasSteps_h1Fall s (SquarePartialClear.memory (stage mem 2112 (6 + 2)))
      (SquareStagedEntry.qWord (6 + 2)) (UInt256.ofNat (sqEnt (6 + 2) 0))
      (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
      (MachineState.readWord mem (16 * (6 + 2) + 32)) (MachineState.readWord mem 96)
      (MachineState.readWord mem 64) (MachineState.readWord mem 32)
      (UInt256.ofNat (2112 + 32 * (6 + 2) - 32)) (UInt256.ofNat (k - 1)) ret rest (by omega)
      hrun hcode hfork hnp (6 + 2) rfl SquareStagedEntry.qWord_eight
    have hcall : R4Loop.loopMem s (6 + 2) k mem =
        SquareLoopMem.sqRunMem s (6 + 2) k (SquarePartialClear.memory (stage mem 2112 (6 + 2))) := by
      rw [SquarePartialClear.sqRunMem_eq s (6 + 2) k _ hk, R4Loop.loopMem,
        if_neg (show ¬ (6 + 2 = 4) by omega)]
      cases k with
      | zero => omega
      | succ k => rfl
    have hz (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
        MachineState.readWord (SquarePartialClear.memory (stage mem 2112 (6 + 2))) addr =
          MachineState.readWord (stage mem 2112 (6 + 2)) addr :=
      SquarePartialClear.readWord_outside _ addr (by omega)
    have hentryZ : Entry s (SquarePartialClear.memory (stage mem 2112 (6 + 2))) 6 a mm
        (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
        (MachineState.readWord mem (16 * (6 + 2) + 32)) (MachineState.readWord mem 96)
        (MachineState.readWord mem 64) (MachineState.readWord mem 32) :=
      ⟨(hz 2688 (Or.inr (by decide))).trans hentry.s32,
        (hz 2784 (Or.inr (by decide))).trans hentry.tlw,
        hentry.tlv.trans (hz 224 (Or.inl (by decide))).symm, (hz 2752 (Or.inr (by decide))).trans hentry.ml,
        (hz 2720 (Or.inr (by decide))).trans hentry.invw,
        (hz (16 * (6 + 2) + 32) (Or.inl (by omega))).trans hentry.m0w,
        (hz 96 (Or.inl (by decide))).trans hentry.m96w,
        (hz 64 (Or.inl (by decide))).trans hentry.m64w,
        (hz 32 (Or.inl (by decide))).trans hentry.m32w,
        (by rw [hz (32 * (6 + 2) - 32) (Or.inl (by omega))]; exact hentry.minv), hentry.inverseGuard,
        SquarePartialClear.fastRepresents_outside _ 2368 (6 + 2) a (Or.inr (by decide)) hentry.arep,
        (Model.fastRepresents_congr (a := stage mem 2112 (6 + 2))
          (by intro j hj; rw [hz (0 + 32 * j) (Or.inl (by omega))]) mm).1 hentry.mrep,
        hentry.alt, hentry.mpos⟩
    change Challenge.EvmProof.GasSteps _
      { s with
        pc := UInt256.ofNat 772
        stack := rest
        memory := StagedProduct.memory s (R4Loop.loopMem s (6 + 2) k mem) (6 + 2) }
    rw [hcall]
    exact ((g1.trans g2).trans g3).trans (gasSteps_loop s mm
      (MachineState.readWord (SquarePartialClear.memory (stage mem 2112 (6 + 2))) 192)
      (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
      (MachineState.readWord mem (16 * (6 + 2) + 32)) (MachineState.readWord mem 96)
      (MachineState.readWord mem 64) (MachineState.readWord mem 32) ret rest hcap hrun hcode hfork
      hnp hact hcds hodd hmpos k (SquarePartialClear.memory (stage mem 2112 (6 + 2))) a
      (UInt256.ofNat (2112 + 32 * (6 + 2) - 32)) (UInt256.ofNat (sqEnt (6 + 2) 0)) hk hk16
      (SquarePartialClear.scratchZero _) rfl hentryZ)

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoop
