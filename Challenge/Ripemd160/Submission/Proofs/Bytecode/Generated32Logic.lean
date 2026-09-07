import Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Logic

open EvmSemantics EvmSemantics.EVM
open Generated32Data

/-- A 32-byte calldata is exactly the target iff its only EVM word is. -/
theorem readWord_eq_target_iff (input : ByteArray) (hsize : input.size = 32) :
    MachineState.readWord input 0 = targetWord ↔ input = targetInput := by
  constructor
  · intro hw
    apply ByteArray.ext_getElem
    · exact hsize.trans targetInput_size.symm
    · intro j hj hjtarget
      have hj32 : j < 32 := by simpa [hsize] using hj
      have hwords : MachineState.readWord input 0 =
          MachineState.readWord targetInput 0 := hw.trans targetInput_readWord.symm
      have hb := congrArg (UInt256.byteAt (UInt256.ofNat j)) hwords
      rw [Challenge.EvmProof.Bytes.byteAt_readWord input 0 j hj32,
        Challenge.EvmProof.Bytes.byteAt_readWord targetInput 0 j hj32] at hb
      have hbyte : YulSemantics.EVM.byteFrom input.toList j =
          YulSemantics.EVM.byteFrom targetInput.toList j := by
        apply UInt8.ext
        have hv := congrArg UInt256.toNat hb
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans
            (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans
            (YulSemantics.EVM.byteFrom targetInput.toList j).toNat_lt
              (by norm_num))] at hv
        exact hv
      rw [YulEvmCompiler.ByteArray.toList_eq_data,
        YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
      unfold YulSemantics.EVM.byteFrom at hbyte
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        Array.getElem?_toList, Array.getElem?_toList,
        Array.getElem?_eq_getElem (by simpa using hj),
        Array.getElem?_eq_getElem (by simpa using hjtarget)] at hbyte
      simpa only [Option.getD_some, ByteArray.getElem_eq_getElem_data] using hbyte
  · rintro rfl
    exact targetInput_readWord

theorem xor_isTrue_of_ne (a b : UInt256) (hne : a ≠ b) :
    UInt256.isTrue (UInt256.xor a b) := by
  intro hzero
  apply hne
  apply (KnownInputLogic.wordXor_eq_zero_iff a b).1
  apply Challenge.EvmProof.Word.word_ext
  simpa using hzero

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Logic
