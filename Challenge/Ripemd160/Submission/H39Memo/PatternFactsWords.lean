import Challenge.Ripemd160.Submission.H39Memo.PatternFactsData
import Challenge.Ripemd160.Submission.H39Memo.Logic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternFacts

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

private theorem readWord_eq_of_bytes (bytes : ByteArray) (offset : Nat) (value : UInt256)
    (h : Bytes.bytesNat ((List.range 32).map
      (fun i => YulSemantics.EVM.byteFrom bytes.data.toList (offset + i))) = value.toNat) :
    MachineState.readWord bytes offset = value := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bytes offset 32) = _
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  exact h

theorem prefix_P32 (k : Fin 1) :
    MachineState.readWord inputP32 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k; apply readWord_eq_of_bytes; decide

theorem tail_P1 : MachineState.readWord inputP1 0 = tailWord 0 := by
  apply readWord_eq_of_bytes
  decide

theorem tail_P31 : MachineState.readWord inputP31 0 = tailWord 1 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P55 (k : Fin 1) :
    MachineState.readWord inputP55 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k; apply readWord_eq_of_bytes; decide

theorem tail_P55 : MachineState.readWord inputP55 32 = tailWord 3 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P56 (k : Fin 1) :
    MachineState.readWord inputP56 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k; apply readWord_eq_of_bytes; decide

theorem tail_P56 : MachineState.readWord inputP56 32 = tailWord 4 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P63 (k : Fin 1) :
    MachineState.readWord inputP63 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k; apply readWord_eq_of_bytes; decide

theorem tail_P63 : MachineState.readWord inputP63 32 = tailWord 5 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P64 (k : Fin 2) :
    MachineState.readWord inputP64 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem prefix_P65 (k : Fin 2) :
    MachineState.readWord inputP65 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem tail_P65 : MachineState.readWord inputP65 64 = tailWord 7 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P119 (k : Fin 3) :
    MachineState.readWord inputP119 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem tail_P119 : MachineState.readWord inputP119 96 = tailWord 8 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P120 (k : Fin 3) :
    MachineState.readWord inputP120 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem tail_P120 : MachineState.readWord inputP120 96 = tailWord 9 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P128 (k : Fin 4) :
    MachineState.readWord inputP128 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem prefix_P256 (k : Fin 8) :
    MachineState.readWord inputP256 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem prefix_P376 (k : Fin 11) :
    MachineState.readWord inputP376 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem tail_P376 : MachineState.readWord inputP376 352 = tailWord 12 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_P1000 (k : Fin 31) :
    MachineState.readWord inputP1000 (32 * k.val) =
      prefixWord ⟨k.val, by omega⟩ := by
  fin_cases k <;> (apply readWord_eq_of_bytes; decide)

theorem tail_P1000 : MachineState.readWord inputP1000 992 = tailWord 13 := by
  apply readWord_eq_of_bytes
  decide

theorem prefix_eq (p : Fin 14) (k : Fin 31)
    (h : 32 * (k.val + 1) ≤ (target p).size) :
    MachineState.readWord (target p) (32 * k.val) = prefixWord k := by
  fin_cases p
  · change 32 * (k.val + 1) ≤ 1 at h
    omega
  · change 32 * (k.val + 1) ≤ 31 at h
    omega
  · change 32 * (k.val + 1) ≤ 32 at h
    exact prefix_P32 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 55 at h
    exact prefix_P55 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 56 at h
    exact prefix_P56 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 63 at h
    exact prefix_P63 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 64 at h
    exact prefix_P64 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 65 at h
    exact prefix_P65 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 119 at h
    exact prefix_P119 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 120 at h
    exact prefix_P120 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 128 at h
    exact prefix_P128 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 256 at h
    exact prefix_P256 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 376 at h
    exact prefix_P376 ⟨k.val, by omega⟩
  · change 32 * (k.val + 1) ≤ 1000 at h
    exact prefix_P1000 ⟨k.val, by omega⟩

theorem tail_eq (p : Fin 14) (h : (target p).size % 32 ≠ 0) :
    MachineState.readWord (target p) (32 * ((target p).size / 32)) = tailWord p := by
  fin_cases p
  · exact tail_P1
  · exact tail_P31
  · exact False.elim (h rfl)
  · exact tail_P55
  · exact tail_P56
  · exact tail_P63
  · exact False.elim (h rfl)
  · exact tail_P65
  · exact tail_P119
  · exact tail_P120
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)
  · exact tail_P376
  · exact tail_P1000

end Challenge.Ripemd160.Submission.H39Memo.PatternFacts
