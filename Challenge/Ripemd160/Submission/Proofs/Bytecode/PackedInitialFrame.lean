import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence

set_option warningAsError true
set_option autoImplicit false

/-!
# Canonical initial packed compression frame

The concrete entry trace supplies the return and memory-range metadata.  The
arithmetic registers and all semantic constants are fixed here, so readiness,
initial constant, and phase premises do not have to be reconstructed at every
consumer.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedInitialFrame

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence

/-- Semantic suffix at compression entry; control metadata stays parametric. -/
def initialSuffix (ret xoff xend : UInt256) : Suffix :=
  ⟨maskLR, maskL, maskR, cMul,
    UInt256.ofNat 17, UInt256.ofNat 18, UInt256.ofNat 19,
    UInt256.ofNat 20, UInt256.ofNat 21, UInt256.ofNat 22,
    packedK 0, ret, xoff, xend⟩

/-- Canonical even-phase frame for an arbitrary chaining state. -/
def initialFrame (h : Compression.HashState) (ret xoff xend : UInt256) : Frame :=
  ⟨PackedHashEntry.initialRegs h, initialSuffix ret xoff xend, Phase.even⟩

theorem initialSuffix_frameStd (ret xoff xend : UInt256) :
    FrameStd (initialSuffix ret xoff xend) := by
  constructor <;> rfl

theorem initialSuffix_suffixStd (ret xoff xend : UInt256) :
    SuffixStd (initialSuffix ret xoff xend) := by
  constructor <;> rfl

/-- The constructed entry frame discharges both execution invariants. -/
theorem initialFrame_ready (h : Compression.HashState)
    (ret xoff xend : UInt256) : Ready (initialFrame h ret xoff xend) :=
  ⟨initialSuffix_frameStd ret xoff xend,
    initialSuffix_suffixStd ret xoff xend⟩

theorem initialFrame_regs (h : Compression.HashState)
    (ret xoff xend : UInt256) :
    (initialFrame h ret xoff xend).regs = PackedHashEntry.initialRegs h := rfl

theorem initialFrame_constant (h : Compression.HashState)
    (ret xoff xend : UInt256) :
    (initialFrame h ret xoff xend).suf.konst = packedK 0 := rfl

theorem initialFrame_phase (h : Compression.HashState)
    (ret xoff xend : UInt256) :
    (initialFrame h ret xoff xend).phase = Phase.even := rfl

#print axioms initialSuffix_frameStd
#print axioms initialSuffix_suffixStd
#print axioms initialFrame_ready
#print axioms initialFrame_regs
#print axioms initialFrame_constant
#print axioms initialFrame_phase

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedInitialFrame
