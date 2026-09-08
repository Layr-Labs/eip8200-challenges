import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySwap

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence
open EvmSemantics PackedStepFrame PackedStep0 PackedEmit
open PackedBridge PackedTemplateGeneric PackedBoundarySwap

def Ready (f : Frame) : Prop := FrameStd f.suf ∧ SuffixStd f.suf

def roundFrame (memAt : UInt256 → UInt256) (i : Nat) (f : Frame) : Frame :=
  stepFrame (i / 16) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
    (memAt (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
      memAt (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8))) f

def boundaryFrame (i : Nat) (f : Frame) : Frame :=
  if (i + 1) % 16 = 0 ∧ i + 1 < 80 then replaceK (packedK ((i + 1) / 16)) f else f

def advanceFrame (memAt : UInt256 → UInt256) (i : Nat) (f : Frame) : Frame :=
  boundaryFrame i (roundFrame memAt i f)

def frameFrom (memAt : UInt256 → UInt256) : Nat → Nat → Frame → Frame
  | _, 0, f => f
  | i, n + 1, f => frameFrom memAt (i + 1) n (advanceFrame memAt i f)

theorem ready_step (group sl sr : Nat) (word : UInt256) (f : Frame)
    (h : Ready f) : Ready (stepFrame group sl sr word f) := h

theorem ready_replace (k : UInt256) (f : Frame) (h : Ready f) :
    Ready (replaceK k f) :=
  ⟨⟨h.1.mLR, h.1.mL, h.1.mR, h.1.cM, h.1.h21, h.1.h22⟩,
    ⟨h.2.h17, h.2.h18, h.2.h19, h.2.h20, h.2.h21, h.2.h22⟩⟩

theorem ready_boundary (i : Nat) (f : Frame) (h : Ready f) :
    Ready (boundaryFrame i f) := by
  unfold boundaryFrame
  split
  · exact ready_replace _ f h
  · exact h

theorem ready_advance (memAt : UInt256 → UInt256) (i : Nat) (f : Frame)
    (h : Ready f) : Ready (advanceFrame memAt i f) := by
  apply ready_boundary
  exact ready_step _ _ _ _ f h

theorem phase_replace (k : UInt256) (f : Frame) :
    (replaceK k f).phase = f.phase := rfl

theorem phase_boundary (i : Nat) (f : Frame) :
    (boundaryFrame i f).phase = f.phase := by
  unfold boundaryFrame
  split
  · exact phase_replace _ f
  · rfl

theorem phase_advance (memAt : UInt256 → UInt256) (i : Nat) (f : Frame) :
    (advanceFrame memAt i f).phase = f.phase.flip :=
  (phase_boundary i _).trans (stepFrame_phase _ _ _ _ f)

theorem boundary_exec (memAt : UInt256 → UInt256) (i : Nat)
    (f : Frame) (rest : List UInt256) :
    runOps memAt (kSwapAfter i) (frameStack f ++ rest)
      = some (frameStack (boundaryFrame i f) ++ rest) := by
  unfold kSwapAfter boundaryFrame
  split
  · exact kSwap_exec memAt _ f rest
  · rfl

/-- Sequential composition, with the ten per-class execution facts as a
separate explicit premise. No artifact/decode correspondence is assumed here. -/
theorem emitFrom_exec (memAt : UInt256 → UInt256)
    (hround : ∀ i, i < 80 → ∀ f, Ready f → ∀ rest,
      runOps memAt (emitRound f.phase i) (frameStack f ++ rest)
        = some (frameStack (roundFrame memAt i f) ++ rest))
    (i n : Nat) (hbound : i + n ≤ 80) (f : Frame) (hready : Ready f)
    (rest : List UInt256) :
    runOps memAt (emitFrom f.phase i n) (frameStack f ++ rest)
      = some (frameStack (frameFrom memAt i n f) ++ rest) := by
  induction n generalizing i f with
  | zero => rfl
  | succ n ih =>
      rw [emitFrom_succ, List.append_assoc, runOps_append,
        hround i (by omega) f hready rest, Option.bind_some,
        runOps_append, boundary_exec, Option.bind_some]
      rw [← phase_advance memAt i f]
      exact ih (i + 1) (by omega) (advanceFrame memAt i f)
        (ready_advance memAt i f hready)

#print axioms ready_advance
#print axioms phase_advance
#print axioms boundary_exec
#print axioms emitFrom_exec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence
