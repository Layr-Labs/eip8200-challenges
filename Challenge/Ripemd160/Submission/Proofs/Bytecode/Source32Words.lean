import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Words
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def tail : ByteArray := ByteArray.mk #[128] ++ ByteArray.mk (Array.replicate 23 0) ++
  ByteArray.mk #[0, 1, 0, 0, 0, 0, 0, 0]

def scalar (input : ByteArray) (k : Nat) : UInt32 :=
  if k < 8 then Crypto.Ripemd160.readLE32 input (4*k)
  else if k = 8 then 128 else if k = 14 then 256 else 0

theorem padded_eq (input : ByteArray) (hsize : input.size = 32) :
    Padding.paddedMessage input = input ++ tail := by
  have hz : Padding.zeroBytes input.size = ByteArray.mk (Array.replicate 23 0) := by
    rw [hsize]; rfl
  have hl : Padding.lengthBytes input = ByteArray.mk #[0, 1, 0, 0, 0, 0, 0, 0] := by
    unfold Padding.lengthBytes
    rw [hsize]
    apply ByteArray.ext_getElem
    · simp; rfl
    · intro i hi hj
      have hi8 : i < 8 := by simpa using hi
      simp only [ByteArray.getElem_ofFn]
      interval_cases i <;> rfl
  rw [Padding.paddedMessage, hz, hl]
  simp only [tail, ByteArray.append_assoc]

theorem padded_size (input : ByteArray) (hsize : input.size = 32) :
    (Padding.paddedMessage input).size = 64 := by
  rw [Padding.paddedMessage_size, hsize]
  rfl

private theorem readLE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Crypto.Ripemd160.readLE32 bs off =
      let b0 := (bs[off]?.getD 0).toUInt32
      let b1 := (bs[off + 1]?.getD 0).toUInt32
      let b2 := (bs[off + 2]?.getD 0).toUInt32
      let b3 := (bs[off + 3]?.getD 0).toUInt32
      (b0 ||| (b1 <<< UInt32.ofNat 8)) |||
        ((b2 <<< UInt32.ofNat 16) ||| (b3 <<< UInt32.ofNat 24)) := by
  unfold Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl_cons, List.foldl_nil]
  have hbyte (i : Nat) :
      (if h : off + i < bs.size then bs[off + i].toUInt32 else 0) =
        (bs[off + i]?.getD 0).toUInt32 := by
    by_cases h : off + i < bs.size <;> simp [h]
  rw [hbyte 0, hbyte 1, hbyte 2, hbyte 3]
  norm_num
  rw [UInt32.or_assoc]
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.shiftLeft_zero]

theorem padded_lower (input : ByteArray) (hsize : input.size = 32) (k : Nat) (hk : k < 8) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4*k) =
      Crypto.Ripemd160.readLE32 input (4*k) := by
  rw [padded_eq input hsize, readLE32_eq_bytes, readLE32_eq_bytes]
  have hb (j : Nat) (hj : j < 4) :
      (input ++ tail)[4*k+j]?.getD 0 = input[4*k+j]?.getD 0 := by
    rw [Memory.getElem?_getD_append, if_pos (by omega)]
  simpa only [Nat.add_zero] using congrArg (fun x : UInt32 => x) (show
    (((input ++ tail)[4*k]?.getD 0).toUInt32 |||
      (((input ++ tail)[4*k+1]?.getD 0).toUInt32 <<< UInt32.ofNat 8)) |||
      ((((input ++ tail)[4*k+2]?.getD 0).toUInt32 <<< UInt32.ofNat 16) |||
      (((input ++ tail)[4*k+3]?.getD 0).toUInt32 <<< UInt32.ofNat 24)) = _ by
        rw [show (input ++ tail)[4*k]?.getD 0 = input[4*k]?.getD 0 from by simpa using hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)])

theorem padded_upper (input : ByteArray) (hsize : input.size = 32) (k : Nat)
    (hk : 8 ≤ k) (hk16 : k < 16) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4*k) =
      (if k = 8 then 128 else if k = 14 then 256 else 0) := by
  rw [padded_eq input hsize, readLE32_eq_bytes]
  simp only [Memory.getElem?_getD_append, hsize]
  interval_cases k <;> norm_num only <;> simp only [ite_true, ite_false] <;> decide

theorem words (input : ByteArray) (hsize : input.size = 32) (k : Nat) (hk : k < 16) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4*k) = scalar input k := by
  unfold scalar
  by_cases h : k < 8
  · rw [if_pos h]; exact padded_lower input hsize k h
  · rw [if_neg h]; exact padded_upper input hsize k (by omega) hk

theorem schedule_words (input : ByteArray) (hsize : input.size = 32) (k : Nat) (hk : k < 16) :
    (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]! = scalar input k := by
  have hs : (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]! =
      Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4*k) := by
    interval_cases k <;> simp [CompressionCorrect.schedule, List.range']
  rw [hs, words input hsize k hk]

theorem upper_bytes (input : ByteArray) (hsize : input.size = 32) (i : Nat) (hi : i < 32) :
    (Padding.paddedMessage input)[32+i]?.getD 0 =
      (Data.Bytes.natToBytesPadded (UInt256.ofNat (2^255 + 2^48)).toNat 32)[i]?.getD 0 := by
  rw [padded_eq input hsize, Memory.getElem?_getD_append, if_neg (by omega), hsize]
  rw [show 32+i-32=i by omega]
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32, tail[j.val]?.getD 0 =
      UInt8.ofNat ((UInt256.ofNat (2^255 + 2^48)).toNat / 256 ^ (32-1-j.val) %256) := by decide
  exact h ⟨i, hi⟩

theorem upper_word (input : ByteArray) (hsize : input.size = 32) :
    MachineState.readWord (Padding.paddedMessage input) 32 = UInt256.ofNat (2^255+2^48) := by
  let v := UInt256.ofNat (2^255+2^48)
  let wm := MachineState.writeBytes ByteArray.empty (Data.Bytes.natToBytesPadded v.toNat 32) 32
  have he : MachineState.readPadded (Padding.paddedMessage input) 32 32 =
      MachineState.readPadded wm 32 32 := by
    apply Memory.readPadded_congr
    intro i hi
    rw [upper_bytes input hsize i hi]
    simp only [wm, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
  calc
    MachineState.readWord (Padding.paddedMessage input) 32 = MachineState.readWord wm 32 := by
      unfold MachineState.readWord
      rw [he]
    _ = v := Memory.readWord_writeWord _ _ _

theorem reversed_upper_constant :
    PairedScheduleData.reversedWord (UInt256.ofNat (2^255+2^48)) =
      UInt256.ofNat (2^231+2^40) := by decide

theorem reversed_upper (input : ByteArray) (hsize : input.size = 32) :
    PairedScheduleData.reversedWord (MachineState.readWord (Padding.paddedMessage input) 32) =
      UInt256.ofNat (2^231+2^40) := by
  rw [upper_word input hsize, reversed_upper_constant]

#print axioms upper_bytes
#print axioms upper_word
#print axioms reversed_upper_constant
#print axioms reversed_upper
#print axioms padded_eq
#print axioms padded_size
#print axioms padded_lower
#print axioms padded_upper
#print axioms words
#print axioms schedule_words
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Words
