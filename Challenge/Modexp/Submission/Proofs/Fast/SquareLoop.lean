import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
import Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
import Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
import Challenge.Modexp.Submission.Proofs.Fast.FusedMemory
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopRuns
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry
import Challenge.Modexp.Submission.Proofs.Fast.R4Loop
import Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory
import Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
import Challenge.Modexp.Submission.Proofs.Fast.R4Trace
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
import Challenge.Modexp.Submission.Proofs.Fast.SquareRoundC

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-!
# The four-word retained squaring loop

The common memory invariants remain available for both accelerated widths. The
execution proofs in this module cover only the unchanged four-word kernel.
`gasSteps_squareLoop4` runs its repeated squares and final product as one call.
The replacement eight-word loop supplies a separate CRTLoopInterface contract.
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
  { CiosCached.outState s M0 2368 n 0 (UInt256.ofNat 5297) ent m32 m64 m0
      (tl :: m96 :: inv :: UInt256.ofNat 0 :: a0 :: pdst :: ret :: rest) with pc := UInt256.ofNat 4816 }

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

/-! ## The four-limb retained loop

The replacement eight-limb kernel has a separate execution contract.
This module retains only the original four-limb execution proof. -/

structure Entry4 (mem : ByteArray) (a mm : Nat) (tl inv m0 m96 m64 m32 : UInt256) : Prop where
  s32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * (2 + 2))
  tlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * (2 + 2))
  tlv : tl = MachineState.readWord mem 224
  ml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * (2 + 2) - 32)
  invw : MachineState.readWord mem 2720 = inv
  m0w : MachineState.readWord mem (16 * (2 + 2) + 32) = m0
  m96w : MachineState.readWord mem 96 = m96
  m64w : MachineState.readWord mem 64 = m64
  m32w : MachineState.readWord mem 32 = m32
  minv : ((MachineState.readWord mem (32 * (2 + 2) - 32)).toNat * inv.toNat + 1) % 2 ^ 256 = 0
  inverseGuard : inv ≠ UInt256.ofNat 1
  arep : Model.FastRepresents mem 2112 4 a
  mrep : Model.FastRepresents mem 0 4 mm
  alt : a < Limbs.radix^4
  mpos : 0 < mm

namespace Entry4

variable {M : ByteArray} {a mm : Nat} {tl inv m0 m96 m64 m32 : UInt256}

theorem minv' (h : Entry4 M a mm tl inv m0 m96 m64 m32) :
    ((MachineState.readWord M 96).toNat * (MachineState.readWord M 2720).toNat + 1) %
      2 ^ 256 = 0 := by
  rw [h.invw]; exact h.minv

theorem rows4r_eq (h : Entry4 M a mm tl inv m0 m96 m64 m32) :
    R4Bridge.r4Mem M (R4Math.red4 m0 m64 m32 (MachineState.readWord M 0)
      (R4Bridge.r4Final M allOnes m0 m64 m32 inv)) = R4Bridge.rows4r M := by
  have e0 : m0 = MachineState.readWord M 96 := h.m0w.symm
  have e64 : m64 = MachineState.readWord M 64 := h.m64w.symm
  have e32 : m32 = MachineState.readWord M 32 := h.m32w.symm
  have ei : inv = MachineState.readWord M 2720 := h.invw.symm
  subst e0 e64 e32 ei
  rfl

/-- One-time overflow initialization preserves all operand and configuration facts. -/
theorem init (h : Entry4 M a mm tl inv m0 m96 m64 m32) :
    Entry4 (R4RetainedMemory.initMemory M) a mm tl inv m0 m96 m64 m32 := by
  have hr (addr : Nat) (hd : addr + 32 ≤ 2080 ∨ 2112 ≤ addr) :=
    R4RetainedMemory.initMemory_read M addr hd
  refine ⟨by rw [hr 2688 (Or.inr (by decide))]; exact h.s32,
    by rw [hr 2784 (Or.inr (by decide))]; exact h.tlw,
    by rw [hr 224 (Or.inl (by decide))]; exact h.tlv,
    by rw [hr 2752 (Or.inr (by decide))]; exact h.ml,
    by rw [hr 2720 (Or.inr (by decide))]; exact h.invw,
    by rw [hr 96 (Or.inl (by decide))]; exact h.m0w,
    by rw [hr 96 (Or.inl (by decide))]; exact h.m96w,
    by rw [hr 64 (Or.inl (by decide))]; exact h.m64w,
    by rw [hr 32 (Or.inl (by decide))]; exact h.m32w,
    by rw [hr 96 (Or.inl (by decide))]; exact h.minv,
    h.inverseGuard, ?_, ?_, h.alt, h.mpos⟩
  · apply Model.fastRepresents_writeBytes_disjoint
    · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega
    · exact h.arep
  · apply Model.fastRepresents_writeBytes_disjoint
    · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega
    · exact h.mrep

/-- Every R4 round re-establishes the invariant, with the operand squared. -/
theorem round (h : Entry4 M a mm tl inv m0 m96 m64 m32) (hodd : mm % 2 = 1) :
    Entry4 (R4Bridge.rows4r M) (LazySquareMemory.roundValue (R4Bridge.rows4 M) 4 mm) mm
      tl inv m0 m96 m64 m32 := by
  obtain ⟨hv, hvr, -, -⟩ := LazySquareMemory.r4r_result M a mm h.arep h.mrep hodd h.minv'
  have hw (addr : Nat) (hd : addr + 32 ≤ 2080 ∨ 2240 ≤ addr) :
      MachineState.readWord (R4Bridge.rows4r M) addr = MachineState.readWord M addr :=
    R4Bridge.rows4r_readWord_outside M addr hd
  exact ⟨by rw [hw 2688 (Or.inr (by norm_num))]; exact h.s32,
    by rw [hw 2784 (Or.inr (by norm_num))]; exact h.tlw,
    by rw [hw 224 (Or.inl (by norm_num))]; exact h.tlv,
    by rw [hw 2752 (Or.inr (by norm_num))]; exact h.ml,
    by rw [hw 2720 (Or.inr (by norm_num))]; exact h.invw,
    by rw [hw (16 * (2 + 2) + 32) (Or.inl (by norm_num))]; exact h.m0w,
    by rw [hw 96 (Or.inl (by norm_num))]; exact h.m96w,
    by rw [hw 64 (Or.inl (by norm_num))]; exact h.m64w,
    by rw [hw 32 (Or.inl (by norm_num))]; exact h.m32w,
    by rw [hw (32 * (2 + 2) - 32) (Or.inl (by norm_num))]; exact h.minv,
    h.inverseGuard, hv,
    R4Bridge.rows4r_fastRepresents_outside M 0 4 mm (Or.inl (by norm_num)) h.mrep,
    hvr, h.mpos⟩

/-- The lazy gate's copy of the window to 2368 after the last round (zero overflow word): the
operand the fused product reads, with every frame word intact. -/
theorem done (s : State) (h : Entry4 M a mm tl inv m0 m96 m64 m32)
    (h0 : MachineState.readWord M 2080 = ⟨0⟩) :
    Entry s (LazyCsub.resultMemory M 4 2368) 2 a mm tl inv m0 m96 m64 m32 := by
  have hw (addr : Nat) (hd : addr + 32 ≤ 1792 ∨ 2496 ≤ addr) :
      MachineState.readWord (LazyCsub.resultMemory M 4 2368) addr =
        MachineState.readWord M addr :=
    LazyCsub.result_readWord_outside M 4 2368 addr (by norm_num) (by omega) (by omega)
  have hcopy : LazyCsub.resultMemory M 4 2368 =
      MachineState.writeBytes M (MachineState.readPadded M 2112 (32 * 4)) 2368 := by
    unfold LazyCsub.resultMemory
    rw [h0, if_pos (show (⟨0⟩ : UInt256).toNat = 0 from rfl)]
  exact ⟨by rw [hw 2688 (Or.inr (by norm_num))]; exact h.s32,
    by rw [hw 2784 (Or.inr (by norm_num))]; exact h.tlw,
    by rw [hw 224 (Or.inl (by norm_num))]; exact h.tlv,
    by rw [hw 2752 (Or.inr (by norm_num))]; exact h.ml,
    by rw [hw 2720 (Or.inr (by norm_num))]; exact h.invw,
    by rw [hw (16 * (2 + 2) + 32) (Or.inl (by norm_num))]; exact h.m0w,
    by rw [hw 96 (Or.inl (by norm_num))]; exact h.m96w,
    by rw [hw 64 (Or.inl (by norm_num))]; exact h.m64w,
    by rw [hw 32 (Or.inl (by norm_num))]; exact h.m32w,
    by rw [hw (32 * (2 + 2) - 32) (Or.inl (by norm_num))]; exact h.minv,
    h.inverseGuard,
    by rw [hcopy]; exact Csub.fastRepresents_mcopy M 2112 2368 4 a (by norm_num) h.arep,
    LazyCsub.result_preserves_region M 4 2368 0 4 mm (by norm_num) (Or.inl (by norm_num))
      (Or.inr (by norm_num)) h.mrep,
    h.alt, h.mpos⟩

end Entry4

private theorem dec_succ4 (c : Nat) (hc : c ≤ 14) :
    allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := by
  interval_cases c <;> decide

/-- Repeated n=4 entry: five constants survive and the counter occupies the old row-pointer slot. -/
def repeatFrameAt (s : State) (M : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev c ret : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 8998
    memory := M
    stack := [m0,m64,m32,MachineState.readWord M 0,inv,c,UInt256.ofNat 5297,
      MachineState.readWord M 192,ent,m32,allOnes,MachineState.readWord M 128,
      m64,m0,tl,m96,inv,UInt256.ofNat 0,aprev,pbi,ret] ++ rest}

/-- An R4 round that is **not** the last: R4, the tail and `st4`, back at R4 with the counter
decremented and the reduced square over the operand. -/
def gasSteps_r4More (s : State) (M : ByteArray) (c a mm : Nat)
    (pbi ent aprev tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (h : Entry4 M a mm tl inv m0 m96 m64 m32) (hz : R4RetainedMemory.ZeroTN M) :
    Challenge.EvmProof.GasSteps
      (repeatFrameAt s M pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat c) ret rest)
      (repeatFrameAt s (R4Bridge.rows4r M) pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c - 1)) ret rest) := by
  have g1 := R4Trace.gasSteps_r4Cached { s with memory := M } (UInt256.ofNat c) (UInt256.ofNat 5297)
    (MachineState.readWord M 192) ent m32 allOnes (MachineState.readWord M 128)
    m64 m0 tl m96 inv (UInt256.ofNat 0) (aprev :: pbi :: ret :: rest)
    (by simp only [List.length_cons]; omega) hcode hfork hrun hnp hact
    CiosCachedMacCore.allOnes_value (by rw [← h.m0w]; exact h.minv) h.inverseGuard
  have hcNat : (UInt256.ofNat c).toNat = c := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htrue : UInt256.isTrue (UInt256.ofNat c) := by
    show (UInt256.ofNat c).toNat ≠ 0
    rw [hcNat]; omega
  have g2 := R4Trace.gasSteps_st4More { s with memory := M } hcode hfork hrun hnp
    (R4Math.red4 m0 m64 m32 (MachineState.readWord M 0) (R4Bridge.r4Final M allOnes m0 m64 m32 inv))
    allOnes m0 m64 m32 (MachineState.readWord M 0) inv (UInt256.ofNat c) (UInt256.ofNat 5297)
    (MachineState.readWord M 192) ent m32 allOnes (MachineState.readWord M 128) m64 m0 tl m96 inv
    (UInt256.ofNat 0) aprev pbi (ret :: rest)
    (by simp only [List.length_cons]; omega) hact htrue hz (R4RetainedMemory.red4_zero ..)
  have hdec : allOnes + UInt256.ofNat c = UInt256.ofNat (c - 1) := by
    have hd := dec_succ4 (c - 1) (by omega)
    rwa [Nat.sub_add_cancel hcpos] at hd
  have outEq : R4Bridge.r4Mem M (R4Math.red4 m0 m64 m32 (MachineState.readWord M 0)
      (R4Bridge.r4Final M allOnes m0 m64 m32 inv)) = R4Bridge.rows4r M := h.rows4r_eq
  simpa only [repeatFrameAt, List.cons_append, List.nil_append, outEq, hdec,
    R4Bridge.rows4r_readWord_outside M 0 (Or.inl (by decide)),
    R4Bridge.rows4r_readWord_outside M 128 (Or.inl (by decide)),
    R4Bridge.rows4r_readWord_outside M 192 (Or.inl (by decide))] using g1.trans g2

/-- The **last** R4 round: R4, the tail and `st4` with a zero counter, `m4j`, the lazy gate's
copy to 2368, and the fused product. -/
def gasSteps_r4Last (s : State) (M : ByteArray) (a mm : Nat)
    (pbi ent aprev tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1)
    (h : Entry4 M a mm tl inv m0 m96 m64 m32) (hzTN : R4RetainedMemory.ZeroTN M) :
    Challenge.EvmProof.GasSteps
      (repeatFrameAt s M pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 0) ret rest)
      { s with pc := UInt256.ofNat 690, stack := rest,
               memory := StagedProduct.memory s
                 (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 4 } := by
  have g1 := R4Trace.gasSteps_r4Cached { s with memory := M } (UInt256.ofNat 0) (UInt256.ofNat 5297)
    (MachineState.readWord M 192) ent m32 allOnes (MachineState.readWord M 128)
    m64 m0 tl m96 inv (UInt256.ofNat 0) (aprev :: pbi :: ret :: rest)
    (by simp only [List.length_cons]; omega) hcode hfork hrun hnp hact
    CiosCachedMacCore.allOnes_value (by rw [← h.m0w]; exact h.minv) h.inverseGuard
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have g2 := R4Trace.gasSteps_st4Last { s with memory := M } hcode hfork hrun hnp
    (R4Math.red4 m0 m64 m32 (MachineState.readWord M 0) (R4Bridge.r4Final M allOnes m0 m64 m32 inv))
    allOnes m0 m64 m32 (MachineState.readWord M 0) inv (UInt256.ofNat 0) (UInt256.ofNat 5297)
    (MachineState.readWord M 192) ent m32 allOnes (MachineState.readWord M 128) m64 m0 tl m96 inv
    (UInt256.ofNat 0) aprev pbi (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hfalse hzTN (R4RetainedMemory.red4_zero ..)
  have hp := h.round hodd
  obtain ⟨-, -, -, h0⟩ := LazySquareMemory.r4r_result M a mm h.arep h.mrep hodd h.minv'
  have hz : allOnes + UInt256.ofNat 0 = allOnes := by decide
  have hm : SquareLoopBlocks.m4jAt s (R4Bridge.rows4r M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
      allOnes ret rest =
      { ({ s with memory := M } : State) with
          pc := (3999 : UInt256)
          stack := pbi :: UInt256.ofNat 5297 :: MachineState.readWord M 192 :: ent :: m32 :: allOnes ::
            MachineState.readWord M 128 :: m64 :: m0 :: tl :: m96 :: inv :: UInt256.ofNat 0 ::
            aprev :: (allOnes + UInt256.ofNat 0) :: ret :: rest
          memory := R4Bridge.r4Mem M (R4Math.red4 m0 m64 m32 (MachineState.readWord M 0)
            (R4Bridge.r4Final M allOnes m0 m64 m32 inv)) } := by
    rw [h.rows4r_eq, hz]
    simp only [SquareLoopBlocks.m4jAt, frameStack, SquareLoopBlocks.pcM4j, List.cons_append,
      List.nil_append, R4Bridge.rows4r_readWord_outside M 128 (Or.inl (by decide)),
      R4Bridge.rows4r_readWord_outside M 192 (Or.inl (by decide)),
      Challenge.EvmProof.Word.literal_eq_ofNat]
  have g3 := SquareLoopBlocks.gasSteps_m4j s (R4Bridge.rows4r M) 4 pbi ent tl inv m0 m96 m64 m32
    aprev allOnes ret rest (by omega) hrun hcode hfork hnp
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 3256).toNat = true := by
    change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3256 = true
    exact Artifact.isValidJumpDest_index 2532 (by rfl)
  have g4 := gasSteps_lazyCsubAt s (R4Bridge.rows4r M) 4 2368 (UInt256.ofNat 3256)
    (frameStack (R4Bridge.rows4r M) 4 pbi ent tl inv m0 m96 m64 m32 aprev allOnes ret rest)
    (by simp only [frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact (by norm_num) (by norm_num) (by norm_num) hjump hp.ml
    hp.tlw
    (by
      rw [Csub.csStep_readWord_disjoint _ 4 2688 (by omega) (Or.inr (by omega)) 4 le_rfl]
      exact hp.s32)
    (by
      rw [Csub.csStep_readWord_disjoint _ 4 2080 (by omega) (Or.inr (by omega)) 4 le_rfl, h0]
      decide)
    (Or.inl rfl)
  have hE := hp.done s h0
  have g5 := FusedProductTrace.gasSteps_product (UInt256.ofNat 0) s
    (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 2
    (LazySquareMemory.roundValue (R4Bridge.rows4 M) 4 mm) mm pbi
    (MachineState.readWord (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 192) ent tl inv
    m0 m96 m64 m32 aprev allOnes ret rest (by omega) (Or.inl rfl) hrun hcode hfork hnp hact hcds hE.minv'
    ⟨hE.tlv, hE.invw.symm, hE.m0w.symm, hE.inverseGuard⟩
    ⟨hE.m96w.symm, hE.m64w.symm, hE.m32w.symm⟩
    hE.arep hE.mrep hE.alt hE.mpos hE.ml hE.tlw hE.s32 (fun h => absurd h (by decide))
  have h128 : MachineState.readWord (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 128 =
      MachineState.readWord (R4Bridge.rows4r M) 128 :=
    LazyCsub.result_readWord_outside _ 4 2368 128 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have h192 : MachineState.readWord (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 192 =
      MachineState.readWord (R4Bridge.rows4r M) 192 :=
    LazyCsub.result_readWord_outside _ 4 2368 192 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hi : TnM128SquareExit.frameAt (UInt256.ofNat 0)
      (MachineState.readWord (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 128) 3256 s
      (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 4
      pbi (MachineState.readWord (LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368) 192) ent tl inv
      m0 m96 m64 m32 aprev allOnes ret rest =
      { s with
          pc := UInt256.ofNat 3256
          stack := frameStack (R4Bridge.rows4r M) 4 pbi ent tl inv m0 m96 m64 m32 aprev
            allOnes ret rest
          memory := LazyCsub.resultMemory (R4Bridge.rows4r M) 4 2368 } := by
    simp only [TnM128SquareExit.frameAt, TnM128SquareExit.frameStack, frameStack, framed, h128, h192]
  simpa only [repeatFrameAt, List.cons_append, List.nil_append] using
    (((g1.trans g2).trans (g3.cast hm rfl)).trans g4).trans (g5.cast hi rfl)

/-- **`k` R4 squares**, from the first R4 entry, ending after the fused product. -/
def gasSteps_cachedLoop4 (s : State) (mm : Nat) (tl inv m0 m96 m64 m32 ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1)
    (pbi ent aprev : UInt256) :
    ∀ (k : Nat) (M : ByteArray) (a : Nat), 1 ≤ k → k ≤ 16 →
      Entry4 M a mm tl inv m0 m96 m64 m32 → R4RetainedMemory.ZeroTN M →
      Challenge.EvmProof.GasSteps
        (repeatFrameAt s M pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat (k - 1))
          ret rest)
        { s with pc := UInt256.ofNat 690, stack := rest,
                 memory := StagedProduct.memory s (R4Loop.r4RunMem k M) 4 } := by
  intro k
  induction k with
  | zero => intro M a hk; exact absurd hk (by omega)
  | succ j ih =>
      intro M a _ hk16 h hz
      match j, ih with
      | 0, _ =>
          exact gasSteps_r4Last s M a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest hcap hrun
            hcode hfork hnp hact hcds hodd h hz
      | (i + 1), ih =>
          exact (gasSteps_r4More s M (i + 1) a mm pbi ent aprev tl inv m0 m96 m64 m32 ret rest
            hcap hrun hcode hfork hnp hact (by omega) (by omega) h hz).trans
            (ih (R4Bridge.rows4r M) _ (by omega) (by omega) (h.round hodd) (R4RetainedMemory.rows4r_zero M))

/-- Initialize the unused overflow word once, then retain constants across all n=4 rounds. -/
def gasSteps_loop4 (s : State) (mm : Nat) (tl inv m0 m96 m64 m32 ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1)
    (pbi ent aprev : UInt256) (k : Nat) (M : ByteArray) (a : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16) (h : Entry4 M a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcH1Fall s M 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (k - 1)) ret rest)
      { s with pc := UInt256.ofNat 690, stack := rest,
               memory := StagedProduct.memory s (R4Loop.r4RunMem k M) 4 } := by
  have ge := R4Hooks.gasSteps_entry {s with memory := M}
    pbi (UInt256.ofNat 5297) (MachineState.readWord M 192) ent m32 allOnes
    (MachineState.readWord M 128) m64 m0 tl m96 inv (UInt256.ofNat 0) aprev
    (UInt256.ofNat (k - 1)) ret (MachineState.readWord M 0) rest
    (by omega) rfl hact hcode hfork hrun hnp
  have ge' : Challenge.EvmProof.GasSteps
      (frameAt R4Hooks.pcH1Fall s M 4 pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (k - 1)) ret rest)
      (repeatFrameAt s (R4RetainedMemory.initMemory M) pbi ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (k - 1)) ret rest) := by
    simpa only [frameAt, frameStack, R4Hooks.pcH1Fall, repeatFrameAt,
      List.cons_append, List.nil_append,
      R4RetainedMemory.initMemory_read M 0 (Or.inl (by decide)),
      R4RetainedMemory.initMemory_read M 128 (Or.inl (by decide)),
      R4RetainedMemory.initMemory_read M 192 (Or.inl (by decide))] using ge
  have gl := gasSteps_cachedLoop4 s mm tl inv m0 m96 m64 m32 ret rest
    hcap hrun hcode hfork hnp hact hcds hodd pbi ent aprev k
    (R4RetainedMemory.initMemory M) a hk hk16 h.init (R4RetainedMemory.zeroTN_init M)
  exact (ge'.trans gl).cast rfl (by rw [R4RetainedMemory.r4RunMem_init k M hk])

/-! ## The whole call -/


/-- The complete unchanged four-word call: stage the operand, perform `k`
Montgomery squares, run the fused product, and return to cleanup at PC 690. -/
def gasSteps_squareLoop4 (s : State) (mem : ByteArray) (p a mm k : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 982)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hfour : p + 2 = 4) (hk : 1 ≤ k) (hk16 : k ≤ 16)
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
      (Cios2Dispatch.commonState s mem 4245 2112 512 (UInt256.ofNat (k - 1)) ret rest)
      { s with pc := UInt256.ofNat 690, stack := rest,
               memory := FusedMemory.memory s (p+2) k mem } := by
  have hp : p = 2 := by omega
  subst hp
  have hfast : 2 + 2 = 4 ∨ 2 + 2 = 8 := Or.inl rfl
  have g1 := Cios2Dispatch.gasSteps_commonSetupSq s mem (UInt256.ofNat 4245) 2112 512 (2 + 2)
    (UInt256.ofNat (k - 1)) ret rest (by omega) hrun hcode hfork hnp hact hfast (by omega)
    (by decide) (by omega) hcds hs32 hml hw hslotn SquareStagedEntry.jumpDest hguard
      (CiosInverseGuard.inverse_ne_zero _ _ hminv)
  have g2 := SquareStagedEntry.gasSteps_entry s (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) (2 + 2)
    (UInt256.ofNat 3347) (MachineState.readWord mem 32) (MachineState.readWord mem 64)
    (MachineState.readWord mem (16 * (2 + 2) + 32))
    (MachineState.readWord mem 224 :: MachineState.readWord mem 96 :: MachineState.readWord mem 2720 ::
      UInt256.ofNat 0 :: UInt256.ofNat (2112 + 32 * (2 + 2) - 32) ::
      UInt256.ofNat (k - 1) :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact
  have hz (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2240 ≤ addr) :
      MachineState.readWord (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) addr =
        MachineState.readWord mem addr := by
    rw [SquarePartialClear.readWord_outside _ addr (by omega),
      read_stageW_four_outside mem addr (by omega)]
  have hentry4 : Entry4 (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) a mm
      (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
      (MachineState.readWord mem (16 * (2 + 2) + 32)) (MachineState.readWord mem 96)
      (MachineState.readWord mem 64) (MachineState.readWord mem 32) :=
    ⟨(hz 2688 (Or.inr (by decide))).trans hs32, (hz 2784 (Or.inr (by decide))).trans htl,
      (hz 224 (Or.inl (by decide))).symm,
      (hz 2752 (Or.inr (by decide))).trans hml, hz 2720 (Or.inr (by decide)),
      hz (16 * (2 + 2) + 32) (Or.inl (by decide)), hz 96 (Or.inl (by decide)),
      hz 64 (Or.inl (by decide)), hz 32 (Or.inl (by decide)),
      (by rw [hz (32 * (2 + 2) - 32) (Or.inl (by decide))]; exact hminv), hguard,
      SquarePartialClear.fastRepresents_outside _ 2112 4 a (Or.inr (by decide))
        (represents_stageW_four mem 2112 4 a (Or.inr (Or.inr ⟨rfl, le_rfl⟩)) ha),
      (Model.fastRepresents_congr (a := mem)
        (by intro j hj; rw [hz (0 + 32 * j) (Or.inl (by omega))]) mm).1 hm,
      ha.1, hmpos⟩
  have g3 := R4Hooks.gasSteps_h1Taken s (SquarePartialClear.memory (stageW mem 2112 (2 + 2)))
    (SquareStagedEntry.qWord (2 + 2)) (UInt256.ofNat 3347)
    (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
    (MachineState.readWord mem (16 * (2 + 2) + 32)) (MachineState.readWord mem 96)
    (MachineState.readWord mem 64) (MachineState.readWord mem 32)
    (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) (UInt256.ofNat (k - 1)) ret rest (by omega)
    hrun hcode hfork hnp (2 + 2) rfl SquareStagedEntry.qWord_four
  have g4 := gasSteps_loop4 s mm (MachineState.readWord mem 224)
    (MachineState.readWord mem 2720) (MachineState.readWord mem (16 * (2 + 2) + 32))
    (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) ret rest hcap hrun hcode hfork hnp hact hcds hodd
    (SquareStagedEntry.qWord (2 + 2)) (UInt256.ofNat 3347)
    (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) k
    (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) a hk hk16 hentry4
  have hcall : R4Loop.loopMem s (2 + 2) k mem =
      R4Loop.r4RunMem k (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) := by
    rw [R4Loop.loopMem, if_pos (show (2 + 2 : Nat) = 4 by norm_num)]
    cases k with
    | zero => omega
    | succ k => rfl
  change Challenge.EvmProof.GasSteps _
    { s with
      pc := UInt256.ofNat 690
      stack := rest
      memory := StagedProduct.memory s (R4Loop.loopMem s (2 + 2) k mem) (2 + 2) }
  rw [hcall]
  exact ((g1.trans g2).trans g3).trans g4

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoop
