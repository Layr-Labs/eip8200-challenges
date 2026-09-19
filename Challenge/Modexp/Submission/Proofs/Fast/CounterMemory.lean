import Challenge.EvmProof.Bytes
import Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CounterMemoryPrototype

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
open Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
open Monpro SquareModel SquareResult

theorem padded_bytes_eq_readPadded (mem : ByteArray) :
    Data.Bytes.natToBytesPadded (MachineState.readWord mem 2624).toNat 32 =
      MachineState.readPadded mem 2624 32 := by
  apply ByteArray.ext_getElem
  · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hi hread
    have hi32 : i < 32 := by
      simpa [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hi
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hread,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi32,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi32]
    have hbyte := Challenge.EvmProof.Bytes.byteAt_readWord mem 2624 i hi32
    rw [UInt256.byteAt] at hbyte
    have hbyte' := congrArg UInt256.toNat hbyte
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat] at hbyte'
    rw [Nat.shiftRight_eq_div_pow] at hbyte'
    have hi256 : i < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hi256] at hbyte'
    rw [if_neg (by omega), Challenge.EvmProof.Word.word_toNat_ofNat] at hbyte'
    rw [show 255 = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod] at hbyte'
    have hleft :
        (MachineState.readWord mem 2624).toNat /
            2 ^ (8 * (31 - i)) % 256 < 2 ^ 256 := by
      have hmod :
          (MachineState.readWord mem 2624).toNat /
              2 ^ (8 * (31 - i)) % 256 < 256 :=
        Nat.mod_lt _ (by norm_num)
      omega
    have hright :
        (YulSemantics.EVM.byteFrom mem.toList (2624 + i)).toNat < 2 ^ 256 := by
      exact (YulSemantics.EVM.byteFrom mem.toList (2624 + i)).toNat_lt.trans (by norm_num)
    rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hbyte'
    have hmem := (Challenge.EvmProof.Bytes.memMatch_toList mem) (2624 + i)
    have hmem' := congrArg UInt8.toNat hmem
    have hexp :
        (256 : Nat) ^ (32 - 1 - i) = 2 ^ (8 * (31 - i)) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num,
        (Nat.pow_mul 2 8 (32 - 1 - i)).symm]
    rw [hexp, hbyte', hmem']
    by_cases hmemsize : 2624 + i < mem.size
    · rw [dif_pos hmemsize,
        Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hmemsize]
      exact UInt8.ofNat_toNat
    · rw [dif_neg hmemsize,
        Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le mem _ (by omega)]
      rfl

theorem countMem_readWord_self (mem : ByteArray) (hsize : 2656 ≤ mem.size) :
    countMem mem (MachineState.readWord mem 2624).toNat = mem := by
  unfold countMem
  rw [padded_bytes_eq_readPadded mem]
  have hreadsize : (MachineState.readPadded mem 2624 32).size = 32 := by simp
  apply ByteArray.ext_getElem
  · rw [MachineState.writeBytes_size,
      hreadsize, if_neg (by omega), max_eq_left hsize]
  · intro i hi hi'
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi',
      MachineState.writeBytes_getElem?_getD, hreadsize]
    by_cases hwin : 2624 ≤ i ∧ i < 2656
    · rw [if_pos hwin]
      rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega)]
      rw [show 2624 + (i - 2624) = i by omega]
    · rw [if_neg hwin]

theorem r8_square_round_raw (mem : ByteArray) (p a mm pdst : Nat)
    (hn : p + 2 ≤ 8)
    (_h8 : p + 2 = 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue mem (p + 2) = 0)
    (hsize : 2656 ≤ (sqRowsCarry mem (p + 2) (p + 2)).size) :
    Model.FastRepresents
        (LazyCsub.resultMemory (sqRowsCarry mem (p + 2) (p + 2)) (p + 2) pdst)
        pdst (p + 2)
        (roundValue (sqRowsCarry mem (p + 2) (p + 2)) (p + 2) mm) ∧
      roundValue (sqRowsCarry mem (p + 2) (p + 2)) (p + 2) mm <
        Limbs.radix ^ (p + 2) ∧
      roundValue (sqRowsCarry mem (p + 2) (p + 2)) (p + 2) mm % mm =
        Model.montMul mm (Limbs.radix ^ (p + 2)) a a := by
  have hresult := LazySquareMemory.carry_result mem p a mm
    (MachineState.readWord (sqRowsCarry mem (p + 2) (p + 2)) 2624).toNat pdst
    hn ha hm hodd hminv hz
  dsimp only at hresult
  rw [countMem_readWord_self _ hsize] at hresult
  exact hresult

theorem r4_square_round_raw (mem : ByteArray) (a mm pdst : Nat)
    (ha : Model.FastRepresents mem 2368 4 a)
    (hm : Model.FastRepresents mem 0 4 mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0)
    (hsize : 2656 ≤ (R4Bridge.rows4 mem).size) :
    Model.FastRepresents
        (LazyCsub.resultMemory (R4Bridge.rows4 mem) 4 pdst)
        pdst 4 (roundValue (R4Bridge.rows4 mem) 4 mm) ∧
      roundValue (R4Bridge.rows4 mem) 4 mm < Limbs.radix ^ 4 ∧
      roundValue (R4Bridge.rows4 mem) 4 mm % mm =
        Model.montMul mm (Limbs.radix ^ 4) a a := by
  have hresult := LazySquareMemory.r4_result mem a mm
    (MachineState.readWord (R4Bridge.rows4 mem) 2624).toNat pdst
    ha hm hodd hminv
  dsimp only at hresult
  rw [countMem_readWord_self _ hsize] at hresult
  exact hresult

end CounterMemoryPrototype


