import Challenge.Modexp.Submission.Proofs.Fast.SquareSelect
import Challenge.Modexp.Submission.Proofs.Fast.SquareInitMemory
import Challenge.Modexp.Submission.Proofs.Fast.SquareProductGas
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareInit StagedOperand

def selected (mem : ByteArray) (pa pb n : Nat) : ByteArray :=
  if n = 4 ∨ n = 8 then SquareSelect.selectedMemory mem (UInt256.ofNat pa) (UInt256.ofNat pb) else mem

def before (mem : ByteArray) (pa pb n : Nat) : ByteArray :=
  inputMemory (selected mem pa pb n) pa n

def prepared (s : State) (mem : ByteArray) (pa pb n : Nat) : ByteArray :=
  if n = 8 ∧ pa = pb then initMemory (mpZeroed s (before mem pa pb n) n)
  else mpZeroed s (before mem pa pb n) n

theorem read_select_outside (mem : ByteArray) (pa pb : UInt256) (addr : Nat)
    (hd : addr+32 ≤ 2368 ∨ 2752 ≤ addr) :
    MachineState.readWord (SquareSelect.selectedMemory mem pa pb) addr = MachineState.readWord mem addr := by
  unfold SquareSelect.selectedMemory
  split
  · exact read_storeWord_outside _ _ _ _ (by omega)
  · rw [read_storeWord_outside _ _ _ _ (by omega), read_storeWord_outside _ _ _ _ (by omega)]

theorem read_selected_outside (mem : ByteArray) (pa pb n addr : Nat)
    (hd : addr+32 ≤ 2368 ∨ 2752 ≤ addr) :
    MachineState.readWord (selected mem pa pb n) addr = MachineState.readWord mem addr := by
  unfold selected
  split
  · exact read_select_outside _ _ _ _ hd
  · rfl

theorem read_before_outside (mem : ByteArray) (pa pb n addr : Nat)
    (hd : addr+32 ≤ 2048 ∨ 2752 ≤ addr) :
    MachineState.readWord (before mem pa pb n) addr = MachineState.readWord mem addr := by
  rw [before, read_inputMemory_outside _ _ _ _ (by omega), read_selected_outside _ _ _ _ _ (by omega)]

theorem read_prepared_outside (s : State) (mem : ByteArray) (pa pb n addr : Nat)
    (hn : n ≤ 8) (hd : addr+32 ≤ 2048 ∨ 2752 ≤ addr) :
    MachineState.readWord (prepared s mem pa pb n) addr = MachineState.readWord mem addr := by
  unfold prepared
  split
  · rw [read_init_outside _ _ (by omega), mpZeroed_readWord_outside _ _ _ _ (by omega),
      read_before_outside _ _ _ _ _ hd]
  · rw [mpZeroed_readWord_outside _ _ _ _ (by omega), read_before_outside _ _ _ _ _ hd]

theorem represents_before (mem : ByteArray) (pa pb n ptr count v : Nat)
    (hd : ptr+32*count ≤ 2048 ∨ 2752 ≤ ptr)
    (hr : Model.FastRepresents mem ptr count v) : Model.FastRepresents (before mem pa pb n) ptr count v := by
  exact (Model.fastRepresents_congr (fun j hj => read_before_outside mem pa pb n (ptr+32*j) (by omega)) v).2 hr

theorem represents_prepared (s : State) (mem : ByteArray) (pa pb n ptr count v : Nat)
    (hn : n ≤ 8) (hd : ptr+32*count ≤ 2048 ∨ 2752 ≤ ptr)
    (hr : Model.FastRepresents mem ptr count v) : Model.FastRepresents (prepared s mem pa pb n) ptr count v := by
  exact (Model.fastRepresents_congr (fun j hj => read_prepared_outside s mem pa pb n (ptr+32*j) hn (by omega)) v).2 hr

theorem represents_double (s : State) (mem : ByteArray) (pa a : Nat)
    (hpa : pa+256 ≤ 2048) (ha : Model.FastRepresents mem pa 8 a) :
    Model.FastRepresents (prepared s mem pa pa 8) 2368 9 (2*a) := by
  rw [prepared, if_pos ⟨rfl,rfl⟩]
  apply init_represents
  have hsel : Model.FastRepresents (selected mem pa pa 8) pa 8 a :=
    (Model.fastRepresents_congr (fun j hj => read_selected_outside mem pa pa 8 (pa+32*j) (by omega)) a).2 ha
  have hs := Csub.fastRepresents_mcopy (selected mem pa pa 8) pa 2400 8 a (by decide) hsel
  have hb : Model.FastRepresents (before mem pa pa 8) 2400 8 a := by
    simpa only [before, inputMemory, if_pos (show 8=4 ∨ 8=8 from Or.inr rfl), or_true, ite_true, stage] using hs
  exact (Model.fastRepresents_congr (fun j hj =>
    mpZeroed_readWord_outside s (before mem pa pa 8) 8 (2400+32*j) (Or.inr (by omega))) a).2 hb

theorem tValue_zero (s : State) (mem : ByteArray) (pa : Nat) :
    tValue (prepared s mem pa pa 8) 8 = 0 := by
  rw [prepared, if_pos ⟨rfl,rfl⟩, tValue, read_init_outside _ 2080 (Or.inl (by decide)), readWord_mpZeroed_tn]
  have hrep : Model.FastRepresents (initMemory (mpZeroed s (before mem pa pa 8) 8)) 2112 8 0 :=
    (Model.fastRepresents_congr (fun j hj => read_init_outside _ (2112+32*j) (Or.inl (by omega))) 0).2
      (fastRepresents_mpZeroed s (before mem pa pa 8) 8)
  have hlow := Model.fastRepresents_value_unique (Csub.fastRepresents_lowValue _ 2112 8) hrep
  rw [hlow]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]

theorem init_high_clear (mem : ByteArray) :
    SquareWords.clearBit (MachineState.readWord (initMemory mem) 2368) = UInt256.ofNat 0 := by
  have ha := Csub.fastRepresents_lowValue mem 2400 8
  have h := SquareProductGas.last_coefficient_zero (initMemory mem) (UInt256.ofNat 0)
    (Csub.lowValue mem 2400 8 8) (init_represents mem _ ha) ha.1
  simpa only [SquareCoefficients.coefficient, Nat.reduceEqDiff, if_false, ite_true,
    SquareCoefficients.dWord, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] using h

end Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
