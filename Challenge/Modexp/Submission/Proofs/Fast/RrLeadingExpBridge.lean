import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Minimal direct-RR bridge into `Fast.Exp`

This private module deliberately leaves the future concrete helper
`GasSteps` certificate outside the inherited `Fast.Exp` file.  It packages
only the state, frame, representation, and arithmetic interfaces consumed by
the existing RR body/last-body theorems.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingExpBridge

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Exp
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory

theorem logic_bitAt_eq (n k : Nat) :
    RrLeadingLogic.bitAt n k =
      Challenge.Modexp.Submission.Proofs.Fast.Exp.bitAt n k := by
  rfl

/-- The direct helper's symbolic exit is definitionally the inherited RR head
after rewriting the already-proved active-word identity. -/
theorem exitState_eq_rrHead (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ template.activeWords.toNat) :
    exitState template mem n bsize esize msize =
      Challenge.Modexp.Submission.Proofs.Fast.Exp.rrHead template
        (copiedMemory mem n) n bsize esize msize (directCounter n) := by
  rw [exitState, Challenge.Modexp.Submission.Proofs.Fast.Exp.rrHead,
    copiedActiveWords_eq template n hn32 hactive]
  rfl

/-- The copied memory retains the existing configuration-frame contract. -/
theorem frame_after_copy {mem : ByteArray} {n bsize minv : Nat}
    (hn32 : n ≤ 32) (hframe : Frame mem n bsize minv) :
    Frame (copiedMemory mem n) n bsize minv where
  s32 := by rw [copiedMemory_sizeWord mem n hn32]; exact hframe.s32
  minvW := by rw [copiedMemory_bsizeWord mem n hn32]; exact hframe.minvW
  ml := by rw [copiedMemory_esizeWord mem n hn32]; exact hframe.ml
  tl := by rw [copiedMemory_msizeWord mem n hn32]; exact hframe.tl
  eoff := by rw [copiedMemory_exponentPtrWord mem n hn32]; exact hframe.eoff

/-- Constructor-only conversion from the Artifact-independent copy invariant
to the exact inherited RR invariant. -/
theorem rrInv_after_copy {mem : ByteArray} {n mm R : Nat}
    (hcopy : RrCopyInv mem n mm R) :
    RrInv mem n mm R (Limbs.radix * R % mm) where
  modulus := hcopy.modulus
  r1 := hcopy.r1
  cc := hcopy.cc
  rr := hcopy.rr

/-- All semantic facts required to invoke an inherited RR suffix from the
direct helper exit.  The concrete helper trace composes before this bundle. -/
theorem direct_rejoin_facts (template : State) (mem : ByteArray)
    (n bsize esize msize mm R minv : Nat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ template.activeWords.toNat)
    (hframe : Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (R % mm))
    (hcc : Model.FastRepresents mem 5120 n (Limbs.radix * R % mm))
    (hacc : Model.FastRepresents mem 1024 n 0)
    (hbase : Model.FastRepresents mem 2048 n 0)
    (hone : Model.FastRepresents mem 3072 n 0) :
    exitState template mem n bsize esize msize =
        Challenge.Modexp.Submission.Proofs.Fast.Exp.rrHead template
          (copiedMemory mem n) n bsize esize msize (directCounter n) ∧
      Frame (copiedMemory mem n) n bsize minv ∧
      RrInv (copiedMemory mem n) n mm R (Limbs.radix * R % mm) ∧
      Model.FastRepresents (copiedMemory mem n) 1024 n 0 ∧
      Model.FastRepresents (copiedMemory mem n) 2048 n 0 ∧
      Model.FastRepresents (copiedMemory mem n) 3072 n 0 ∧
      directCounter n ≤ 5 := by
  have hcopy := rrCopyInv_after_copy mem n mm R hn2 hn32 hmod hr1 hcc
  exact ⟨exitState_eq_rrHead template mem n bsize esize msize hn32 hactive,
    frame_after_copy hn32 hframe, rrInv_after_copy hcopy,
    fastRepresents_accumulator_preserved mem n 0 hn32 hacc,
    fastRepresents_base_preserved mem n 0 hn32 hbase,
    fastRepresents_one_preserved mem n 0 hn32 hone,
    Nat.le_trans (directCounter_le_four hn2 hn32) (by omega)⟩

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingExpBridge
