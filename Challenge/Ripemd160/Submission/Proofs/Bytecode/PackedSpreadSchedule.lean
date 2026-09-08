import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedReadWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombine

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSpreadSchedule

open EvmSemantics
open PackedStepCorrected PackedCompression

/-- The message operand family read from the actual descending spread. -/
def messageWords (memory : ByteArray) (words : Nat → UInt256) (round : Nat) : UInt256 :=
  PackedLoadModel.loadPair (PackedGapInvariant.spreadWords words 16 memory)
    Crypto.Ripemd160.r[round]! Crypto.Ripemd160.rP[round]!

/-- Same literal expression as PackedEmit.packedK, isolated from its code
generator dependencies. The located constant sites still need binding. -/
def groupConstant (group : Nat) : UInt256 :=
  UInt256.ofNat (Crypto.Ripemd160.K[group]!.toNat +
    Crypto.Ripemd160.KP[group]!.toNat * 2 ^ 64)

theorem groupConstant_ok (group : Nat) (hg : group < 5) :
    ConstOk (groupConstant group) Crypto.Ripemd160.K[group]!
      Crypto.Ripemd160.KP[group]! := by
  interval_cases group <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

theorem roundConstant_ok (round : Nat) (hr : round < 80) :
    ConstOk (groupConstant (round / 16)) Crypto.Ripemd160.K[round / 16]!
      Crypto.Ripemd160.KP[round / 16]! :=
  groupConstant_ok _ (by omega)

theorem schedule_indices (round : Nat) (hr : round < 80) :
    Crypto.Ripemd160.r[round]! < 16 ∧ Crypto.Ripemd160.rP[round]! < 16 := by
  interval_cases round <;> decide

/-- All eighty message operands meet the arithmetic round's actual contract.
The preprocessing trace must still supply the initial gap and stored values. -/
theorem messageWords_ok (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (round : Nat) (hr : round < 80) :
    WordOk (messageWords memory words round)
      (values Crypto.Ripemd160.r[round]!) (values Crypto.Ripemd160.rP[round]!) := by
  obtain ⟨hl, hh⟩ := schedule_indices round hr
  exact wordOk_of_spreadReads _ values
    (PackedReadWindow.spreadWords_reads memory words values hgap hv) _ _ hl hh

/-- The arithmetic fold now consumes concrete memory-derived message operands,
not a caller-supplied family of eighty WordOk assumptions. This does not yet
assert that a located EVM trace executes this fold. -/
theorem rounds_from_spread (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (constants : Nat → UInt256)
    (hk : ∀ i, i < 80 → ConstOk (constants i)
      Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!)
    (count : Nat) (hc : count ≤ 80) (g : Regs) (yl yr : Compression.Working)
    (hrep : RegsRepresents g yl yr) (hregs : RegsOk g) :
    RegsRepresents (packedRounds (messageWords memory words) constants count g)
        (CompressionCorrect.leftRounds values count yl)
        (CompressionCorrect.rightRounds values count yr) ∧
      RegsOk (packedRounds (messageWords memory words) constants count g) := by
  exact packedRounds_represents values (messageWords memory words) constants
    (messageWords_ok memory words values hgap hv) hk count hc g yl yr hrep hregs

/-- Full arithmetic compression with message and constant premises discharged.
The hash-register entry relation and concrete execution remain separate gates. -/
theorem compress_from_spread (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (h : Compression.HashState) (g0 : Regs)
    (hrep : RegsRepresents g0 (CompressionCorrect.workingOfHash h)
      (CompressionCorrect.workingOfHash h)) (hregs : RegsOk g0) :
    PackedCombine.packedCombine (Compression.embedHash h)
      (packedRounds (messageWords memory words) (fun i => groupConstant (i / 16)) 80 g0)
      = Compression.embedHash (CompressionCorrect.compressModel values h) := by
  exact PackedCombine.packedCompress_embed values (messageWords memory words)
    (fun i => groupConstant (i / 16)) (messageWords_ok memory words values hgap hv)
    roundConstant_ok h g0 hrep hregs

#print axioms compress_from_spread
#print axioms schedule_indices
#print axioms groupConstant_ok
#print axioms roundConstant_ok
#print axioms messageWords_ok
#print axioms rounds_from_spread

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSpreadSchedule
