import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Mathlib.Tactic.NormNum

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-!
# Size-32 identification for the three hook words

A 32-byte calldata value is exactly one EVM word.  `CALLDATALOAD 0` therefore
pins the `ByteArray`, not merely a prefix of it.  The three hit words
`Hook32.word0`, `word1` and `word2` each select one literal.  `spec` on every
input is the 32-byte padded digest: twelve zero bytes followed by
`Crypto.Ripemd160.hash`.

`Hook32Return.push0/1/2` are copied as snapshots.  That module is still moving
and must not be imported (the return proof will import this certificate).
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Digest

open EvmSemantics
open Challenge.Ripemd160

private theorem byteFrom_toList_getElem (bytes : ByteArray) (i : Nat)
    (hi : i < bytes.size) :
    YulSemantics.EVM.byteFrom bytes.toList i = bytes[i] := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [Array.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some]
  rfl

/-- Equal covering words give equal bytes at every absolute index. -/
theorem byte_eq_of_readWord_eq (input target : ByteArray) (i : Nat)
    (hword : MachineState.readWord input (32 * (i / 32)) =
      MachineState.readWord target (32 * (i / 32))) :
    YulSemantics.EVM.byteFrom input.toList i =
      YulSemantics.EVM.byteFrom target.toList i := by
  have hr : i % 32 < 32 := Nat.mod_lt _ (by omega)
  have hinput := Challenge.EvmProof.Bytes.byteAt_readWord
    input (32 * (i / 32)) (i % 32) hr
  have htarget := Challenge.EvmProof.Bytes.byteAt_readWord
    target (32 * (i / 32)) (i % 32) hr
  rw [hword] at hinput
  rw [Nat.div_add_mod i 32] at hinput htarget
  have hbytes := congrArg UInt256.toNat (hinput.symm.trans htarget)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans
      (YulSemantics.EVM.byteFrom input.toList i).toNat_lt (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_trans
      (YulSemantics.EVM.byteFrom target.toList i).toNat_lt (by norm_num))] at hbytes
  exact UInt8.toNat.inj hbytes

/-- Equal size and equal covering `CALLDATALOAD` words force equal calldata. -/
theorem byteArray_eq_of_readWord_cover (input target : ByteArray)
    (hsize : input.size = target.size)
    (hwords : ∀ k, 32 * k < input.size →
      MachineState.readWord input (32 * k) =
        MachineState.readWord target (32 * k)) :
    input = target := by
  apply ByteArray.ext_getElem
  · exact hsize
  · intro i hiInput hiTarget
    let k := i / 32
    have hk : 32 * k < input.size := by
      dsimp [k]
      omega
    have hword : MachineState.readWord input (32 * (i / 32)) =
        MachineState.readWord target (32 * (i / 32)) := by
      simpa [k] using hwords k hk
    have hbyte := byte_eq_of_readWord_eq input target i hword
    exact (byteFrom_toList_getElem input i hiInput).symm.trans
      (hbyte.trans (byteFrom_toList_getElem target i hiTarget))

/-- Big-endian 32-byte encoding of an EVM word. -/
def canonical (w : UInt256) : ByteArray :=
  Data.Bytes.natToBytesPadded w.toNat 32

@[simp] theorem canonical_size (w : UInt256) : (canonical w).size = 32 := by
  simp [canonical, Data.Bytes.natToBytesPadded, ByteArray.size]

theorem readWord_canonical (w : UInt256) :
    MachineState.readWord (canonical w) 0 = w := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [show MachineState.readPadded (canonical w) 0 32 = canonical w by
    simpa [canonical_size w] using
      Challenge.EvmProof.Memory.readPadded_zero_size (canonical w)]
  unfold canonical
  refine Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
    w.toNat 32 ?_
  have hlt : w.toNat < 2 ^ 256 := w.val.isLt
  simpa [show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num] using hlt

/-- Any size-32 input is the canonical encoding of its loaded word. -/
theorem input_eq_canonical (input : ByteArray) (w : UInt256)
    (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = w) :
    input = canonical w := by
  apply byteArray_eq_of_readWord_cover input (canonical w)
  · rw [hsize, canonical_size]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa using hword.trans (readWord_canonical w).symm

theorem input_eq_word0 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word0) :
    input = canonical Hook32.word0 :=
  input_eq_canonical input Hook32.word0 hsize hword

theorem input_eq_word1 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word1) :
    input = canonical Hook32.word1 :=
  input_eq_canonical input Hook32.word1 hsize hword

theorem input_eq_word2 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word2) :
    input = canonical Hook32.word2 :=
  input_eq_canonical input Hook32.word2 hsize hword

theorem word0_ne_word1 : Hook32.word0 ≠ Hook32.word1 := by decide

theorem word0_ne_word2 : Hook32.word0 ≠ Hook32.word2 := by decide

theorem word1_ne_word2 : Hook32.word1 ≠ Hook32.word2 := by decide

/-- Twelve leading zero bytes, in the same loop `spec` uses. -/
def zeroPrefix : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for _ in [0:12] do
    out := out.push 0
  pure out

theorem zeroPrefix_eq_replicate :
    zeroPrefix = ByteArray.mk (Array.replicate 12 0) := by
  unfold zeroPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

/-- `spec` is the 32-byte padded digest of every input. -/
theorem spec_eq_paddedHash (input : ByteArray) :
    spec input = zeroPrefix ++ Crypto.Ripemd160.hash input := by
  unfold spec zeroPrefix
  rfl

theorem spec_eq_replicateHash (input : ByteArray) :
    spec input =
      ByteArray.mk (Array.replicate 12 0) ++ Crypto.Ripemd160.hash input := by
  rw [spec_eq_paddedHash, zeroPrefix_eq_replicate]

/-- Snapshot of `Hook32Return.push0`.  Not an import. -/
def returnPush0 : UInt256 :=
  UInt256.ofNat 864225204616626385640043679974750823807691915652

/-- Snapshot of `Hook32Return.push1`.  Not an import. -/
def returnPush1 : UInt256 :=
  UInt256.ofNat 330311920271539217756235131599613361701789350134

/-- Snapshot of the current `Hook32Return.push2`.  This value does not match
`Hook32.digest2` or the bytecode immediate at instruction 5458. -/
def returnPush2Snapshot : UInt256 :=
  UInt256.ofNat 1454518665044061220775692130387869399047568886206

theorem returnPush0_eq_digest0 : returnPush0 = Hook32.digest0 := by decide

theorem returnPush1_eq_digest1 : returnPush1 = Hook32.digest1 := by decide

theorem returnPush2Snapshot_ne_digest2 :
    returnPush2Snapshot ≠ Hook32.digest2 := by decide

/-- Bytecode immediate at instruction 5458 (`Hook32.get_5458`). -/
def bytecodePush2 : UInt256 :=
  UInt256.ofNat 1449722157075762988299117569158461631583316913598

theorem bytecodePush0_eq_digest0 :
    UInt256.ofNat 864225204616626385640043679974750823807691915652 =
      Hook32.digest0 :=
  returnPush0_eq_digest0

theorem bytecodePush1_eq_digest1 :
    UInt256.ofNat 330311920271539217756235131599613361701789350134 =
      Hook32.digest1 :=
  returnPush1_eq_digest1

theorem bytecodePush2_eq_digest2 : bytecodePush2 = Hook32.digest2 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Digest
