import Challenge.Modexp.Submission.Proofs.Fast.Guard257Logic
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Target

open EvmSemantics EvmSemantics.EVM
open Guard257Data Guard257Logic

theorem getD_eq_of_readWord_eq (a b : ByteArray) (start rem : Nat)
    (hrem : rem < 32)
    (hword : MachineState.readWord a start = MachineState.readWord b start) :
    a[start + rem]?.getD 0 = b[start + rem]?.getD 0 := by
  have hbyte := congrArg
    (fun w => UInt256.byteAt (UInt256.ofNat rem) w) hword
  rw [Challenge.EvmProof.Bytes.byteAt_readWord a start rem hrem,
    Challenge.EvmProof.Bytes.byteAt_readWord b start rem hrem] at hbyte
  have hnat := congrArg UInt256.toNat hbyte
  have ha_lt :
      (YulSemantics.EVM.byteFrom a.toList (start + rem)).toNat < 2 ^ 256 :=
    Nat.lt_trans (YulSemantics.EVM.byteFrom a.toList (start + rem)).toNat_lt
      (by norm_num)
  have hb_lt :
      (YulSemantics.EVM.byteFrom b.toList (start + rem)).toNat < 2 ^ 256 :=
    Nat.lt_trans (YulSemantics.EVM.byteFrom b.toList (start + rem)).toNat_lt
      (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hnat
  have hbyte' :
      YulSemantics.EVM.byteFrom a.toList (start + rem) =
        YulSemantics.EVM.byteFrom b.toList (start + rem) :=
    UInt8.toNat_inj.mp hnat
  have ha := Challenge.EvmProof.Bytes.memMatch_toList a (start + rem)
  have hb := Challenge.EvmProof.Bytes.memMatch_toList b (start + rem)
  by_cases hia : start + rem < a.size
  · rw [dif_pos hia] at ha
    by_cases hib : start + rem < b.size
    · rw [dif_pos hib] at hb
      simpa [getElem?_pos, hia, hib] using ha.symm.trans (hbyte'.trans hb)
    · rw [dif_neg hib] at hb
      simpa [getElem?_pos, hia, getElem?_neg, hib] using
        ha.symm.trans (hbyte'.trans hb)
  · rw [dif_neg hia] at ha
    by_cases hib : start + rem < b.size
    · rw [dif_pos hib] at hb
      simpa [getElem?_neg, hia, getElem?_pos, hib] using
        ha.symm.trans (hbyte'.trans hb)
    · rw [dif_neg hib] at hb
      simp [getElem?_neg, hia, hib]

theorem target_matches : Matches targetInput := by
  constructor
  · exact targetInput_size
  · intro p hp
    simp only [checks, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      apply Challenge.EvmProof.Word.word_ext
      rw [Challenge.EvmProof.Bytes.readWord_toNat]
      unfold Precompile.bytesToNatPadded
      rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
        Challenge.EvmProof.Bytes.readPadded_toList]
      simp only [YulEvmCompiler.ByteArray.toList_eq_data]
      simp (config := { maxSteps := 4000000 }) [List.range_succ,
        Challenge.EvmProof.Bytes.bytesNat, Challenge.EvmProof.Bytes.step,
        targetInput, YulSemantics.EVM.byteFrom]
      rfl

theorem matches_eq_target (input : ByteArray) (h : Matches input) :
    input = targetInput := by
  apply ByteArray.ext_getElem
  · rw [h.1, targetInput_size]
  · intro i hi hti
    have hi163 : i < 163 := by
      simpa [targetInput_size] using hti
    let q := i / 32
    let rem := i % 32
    have hq6 : q < 6 := by
      dsimp [q]
      omega
    have hq : q < checks.length := by
      simp [checks_length]
      exact hq6
    let p := checks[q]'hq
    have hp : p ∈ checks := List.getElem_mem hq
    have hoff : p.1 = 32 * q := by
      dsimp [p]
      interval_cases q <;> simp [checks]
    have hwi := h.2 p hp
    have hwt := target_matches.2 p hp
    have hw : MachineState.readWord input (32 * q) =
        MachineState.readWord targetInput (32 * q) := by
      rw [← hoff]
      exact hwi.trans hwt.symm
    have hrem : rem < 32 := Nat.mod_lt _ (by omega)
    have hrecompose : 32 * q + rem = i := by
      have hmod := Nat.mod_add_div i 32
      dsimp [q, rem]
      omega
    have hd := getD_eq_of_readWord_eq input targetInput (32 * q) rem hrem hw
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem input i hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem targetInput i hti]
    simpa [hrecompose] using hd

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Target
