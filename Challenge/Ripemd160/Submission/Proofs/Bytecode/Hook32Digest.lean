import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32DigestInput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32DigestHash0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32DigestHash1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32DigestHash2
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-!
# Hook-word digest certificate

Size 32 and `Hook32.word0` / `word1` / `word2` identify one `ByteArray` each.
On that input, `Challenge.Ripemd160.spec` equals the 32-byte padded digest,
which is also `natToBytesPadded` of `Hook32.digest0` / `digest1` / `digest2`.

Those digest words are the immediates of the return `PUSH20`s at instructions
5444, 5451 and 5458.  The current `Hook32Return.push2` snapshot does not match
`digest2`; use `bytecodePush2` / `Hook32.digest2` for the third stub.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Digest

open EvmSemantics
open Challenge.Ripemd160

theorem readWord_literal0 :
    MachineState.readWord Hook32DigestHash0.literal 0 = Hook32.word0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded Hook32DigestHash0.literal 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem readWord_literal1 :
    MachineState.readWord Hook32DigestHash1.literal 0 = Hook32.word1 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded Hook32DigestHash1.literal 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem readWord_literal2 :
    MachineState.readWord Hook32DigestHash2.literal 0 = Hook32.word2 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded Hook32DigestHash2.literal 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem literal0_eq_canonical :
    Hook32DigestHash0.literal = canonical Hook32.word0 := by
  apply byteArray_eq_of_readWord_cover
  · rw [Hook32DigestHash0.literal_size, canonical_size]
  · intro k hk
    have hk0 : k = 0 := by
      rw [Hook32DigestHash0.literal_size] at hk
      omega
    subst k
    simpa using readWord_literal0.trans (readWord_canonical _).symm

theorem literal1_eq_canonical :
    Hook32DigestHash1.literal = canonical Hook32.word1 := by
  apply byteArray_eq_of_readWord_cover
  · rw [Hook32DigestHash1.literal_size, canonical_size]
  · intro k hk
    have hk0 : k = 0 := by
      rw [Hook32DigestHash1.literal_size] at hk
      omega
    subst k
    simpa using readWord_literal1.trans (readWord_canonical _).symm

theorem literal2_eq_canonical :
    Hook32DigestHash2.literal = canonical Hook32.word2 := by
  apply byteArray_eq_of_readWord_cover
  · rw [Hook32DigestHash2.literal_size, canonical_size]
  · intro k hk
    have hk0 : k = 0 := by
      rw [Hook32DigestHash2.literal_size] at hk
      omega
    subst k
    simpa using readWord_literal2.trans (readWord_canonical _).symm

theorem input_eq_literal0 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word0) :
    input = Hook32DigestHash0.literal := by
  rw [input_eq_word0 input hsize hword, literal0_eq_canonical]

theorem input_eq_literal1 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word1) :
    input = Hook32DigestHash1.literal := by
  rw [input_eq_word1 input hsize hword, literal1_eq_canonical]

theorem input_eq_literal2 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word2) :
    input = Hook32DigestHash2.literal := by
  rw [input_eq_word2 input hsize hword, literal2_eq_canonical]

theorem spec_eq_paddedDigest_word0 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word0) :
    spec input = Hook32DigestHash0.paddedDigest := by
  rw [input_eq_literal0 input hsize hword, Hook32DigestHash0.spec_literal]

theorem spec_eq_paddedDigest_word1 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word1) :
    spec input = Hook32DigestHash1.paddedDigest := by
  rw [input_eq_literal1 input hsize hword, Hook32DigestHash1.spec_literal]

theorem spec_eq_paddedDigest_word2 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word2) :
    spec input = Hook32DigestHash2.paddedDigest := by
  rw [input_eq_literal2 input hsize hword, Hook32DigestHash2.spec_literal]

private theorem ofNat_toNat_small (n : Nat) (h : n < 2 ^ 256) :
    (UInt256.ofNat n).toNat = n := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h]

theorem paddedDigest0_eq_returnBytes :
    Hook32DigestHash0.paddedDigest =
      Data.Bytes.natToBytesPadded Hook32.digest0.toNat 32 := by
  rw [Hook32.digest0, ofNat_toNat_small _ (by norm_num),
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

theorem paddedDigest1_eq_returnBytes :
    Hook32DigestHash1.paddedDigest =
      Data.Bytes.natToBytesPadded Hook32.digest1.toNat 32 := by
  rw [Hook32.digest1, ofNat_toNat_small _ (by norm_num),
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

theorem paddedDigest2_eq_returnBytes :
    Hook32DigestHash2.paddedDigest =
      Data.Bytes.natToBytesPadded Hook32.digest2.toNat 32 := by
  rw [Hook32.digest2, ofNat_toNat_small _ (by norm_num),
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

theorem spec_eq_returnBytes_word0 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word0) :
    spec input = Data.Bytes.natToBytesPadded returnPush0.toNat 32 := by
  rw [spec_eq_paddedDigest_word0 input hsize hword, paddedDigest0_eq_returnBytes,
    returnPush0_eq_digest0]

theorem spec_eq_returnBytes_word1 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word1) :
    spec input = Data.Bytes.natToBytesPadded returnPush1.toNat 32 := by
  rw [spec_eq_paddedDigest_word1 input hsize hword, paddedDigest1_eq_returnBytes,
    returnPush1_eq_digest1]

theorem spec_eq_returnBytes_word2 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = Hook32.word2) :
    spec input = Data.Bytes.natToBytesPadded bytecodePush2.toNat 32 := by
  rw [spec_eq_paddedDigest_word2 input hsize hword, paddedDigest2_eq_returnBytes,
    bytecodePush2_eq_digest2]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Digest
