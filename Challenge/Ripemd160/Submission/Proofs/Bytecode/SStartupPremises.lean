import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel

set_option warningAsError true

/-!
# S multiply-startup hash-load premises

The S experiment replaces the five masked hash loads by
`PUSH address; MLOAD; DUP; MUL` with `R = 1 + 2^128`.
Its only new proof obligation is that the five scheduled hash words are
canonical (`< 2^32`). This module transfers that fact from the existing
caller context through the existing schedule:

* `StackRunBridge.BlockContext.hash :
    hashAt32 s = Compression.embedHash h`
* `PairedBlockModel.scheduled_hashWords :
    hashWords (scheduledState s i).memory = hashWords s.memory`

No bytes, no central edits, no new axioms.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SStartupPremises

open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM

/-- The five scheduled hash loads the S multiply startup consumes. -/
def CanonicalHashLoads (memory : ByteArray) : Prop :=
  (MachineState.readWord memory 32).toNat < 2 ^ 32 ∧
  (MachineState.readWord memory 64).toNat < 2 ^ 32 ∧
  (MachineState.readWord memory 96).toNat < 2 ^ 32 ∧
  (MachineState.readWord memory 128).toNat < 2 ^ 32 ∧
  (MachineState.readWord memory 160).toNat < 2 ^ 32

/-- Scheduled memory preserves the caller's embedded hash. -/
theorem scheduled_embed (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    PairedBlockMath.hashWords (PairedBlockModel.scheduledState s i).memory =
      Compression.embedHash h :=
  (PairedBlockModel.scheduled_hashWords s i).trans ctx.hash

/-- Each scheduled hash load equals the caller's embedded word. -/
theorem scheduled_word32 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    MachineState.readWord (PairedBlockModel.scheduledState s i).memory 32 =
      Challenge.EvmProof.Word.ofUInt32 h.h0 :=
  congrArg Compression.EvmHashState.h0 (scheduled_embed s input i h ctx)

/-- Each scheduled hash load equals the caller's embedded word. -/
theorem scheduled_word64 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    MachineState.readWord (PairedBlockModel.scheduledState s i).memory 64 =
      Challenge.EvmProof.Word.ofUInt32 h.h1 :=
  congrArg Compression.EvmHashState.h1 (scheduled_embed s input i h ctx)

/-- Each scheduled hash load equals the caller's embedded word. -/
theorem scheduled_word96 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    MachineState.readWord (PairedBlockModel.scheduledState s i).memory 96 =
      Challenge.EvmProof.Word.ofUInt32 h.h2 :=
  congrArg Compression.EvmHashState.h2 (scheduled_embed s input i h ctx)

/-- Each scheduled hash load equals the caller's embedded word. -/
theorem scheduled_word128 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    MachineState.readWord (PairedBlockModel.scheduledState s i).memory 128 =
      Challenge.EvmProof.Word.ofUInt32 h.h3 :=
  congrArg Compression.EvmHashState.h3 (scheduled_embed s input i h ctx)

/-- Each scheduled hash load equals the caller's embedded word. -/
theorem scheduled_word160 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    MachineState.readWord (PairedBlockModel.scheduledState s i).memory 160 =
      Challenge.EvmProof.Word.ofUInt32 h.h4 :=
  congrArg Compression.EvmHashState.h4 (scheduled_embed s input i h ctx)

theorem scheduled_canonical32 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 32).toNat <
      2 ^ 32 := by
  rw [scheduled_word32 s input i h ctx,
    Challenge.EvmProof.Word.ofUInt32_toNat]
  exact h.h0.toNat_lt

theorem scheduled_canonical64 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 64).toNat <
      2 ^ 32 := by
  rw [scheduled_word64 s input i h ctx,
    Challenge.EvmProof.Word.ofUInt32_toNat]
  exact h.h1.toNat_lt

theorem scheduled_canonical96 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 96).toNat <
      2 ^ 32 := by
  rw [scheduled_word96 s input i h ctx,
    Challenge.EvmProof.Word.ofUInt32_toNat]
  exact h.h2.toNat_lt

theorem scheduled_canonical128 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 128).toNat <
      2 ^ 32 := by
  rw [scheduled_word128 s input i h ctx,
    Challenge.EvmProof.Word.ofUInt32_toNat]
  exact h.h3.toNat_lt

theorem scheduled_canonical160 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 160).toNat <
      2 ^ 32 := by
  rw [scheduled_word160 s input i h ctx,
    Challenge.EvmProof.Word.ofUInt32_toNat]
  exact h.h4.toNat_lt

/-- Combined reusable premise for the S multiply startup. -/
theorem scheduled_canonical (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    CanonicalHashLoads (PairedBlockModel.scheduledState s i).memory :=
  ⟨scheduled_canonical32 s input i h ctx,
   scheduled_canonical64 s input i h ctx,
   scheduled_canonical96 s input i h ctx,
   scheduled_canonical128 s input i h ctx,
   scheduled_canonical160 s input i h ctx⟩

theorem scheduled_proj32 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 32) =
      h.h0 := by
  rw [scheduled_word32 s input i h ctx,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]

theorem scheduled_proj64 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 64) =
      h.h1 := by
  rw [scheduled_word64 s input i h ctx,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]

theorem scheduled_proj96 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 96) =
      h.h2 := by
  rw [scheduled_word96 s input i h ctx,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]

theorem scheduled_proj128 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 128) =
      h.h3 := by
  rw [scheduled_word128 s input i h ctx,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]

theorem scheduled_proj160 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (PairedBlockModel.scheduledState s i).memory 160) =
      h.h4 := by
  rw [scheduled_word160 s input i h ctx,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]

#print axioms scheduled_embed
#print axioms scheduled_word32
#print axioms scheduled_word64
#print axioms scheduled_word96
#print axioms scheduled_word128
#print axioms scheduled_word160
#print axioms scheduled_canonical32
#print axioms scheduled_canonical64
#print axioms scheduled_canonical96
#print axioms scheduled_canonical128
#print axioms scheduled_canonical160
#print axioms scheduled_canonical
#print axioms scheduled_proj32
#print axioms scheduled_proj64
#print axioms scheduled_proj96
#print axioms scheduled_proj128
#print axioms scheduled_proj160

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SStartupPremises
