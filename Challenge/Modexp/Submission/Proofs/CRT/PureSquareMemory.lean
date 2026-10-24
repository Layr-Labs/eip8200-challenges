import Challenge.Modexp.Submission.Proofs.CRT.PureLoop
import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.PureSquareMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopArithmetic HistoricalSearch.CRTAdapterMeaning HistoricalSearch.PureLoop

def initial (k : Nat) (mem : ByteArray) : ByteArray :=
  entryMemory (SquarePartialClear.memory (StagedOperand.stage mem 2112 8)) (UInt256.ofNat (k-1))

def memory (s : State) : Nat → ByteArray → ByteArray
  | 0, mem => mem
  | k+1, mem => PureLoop.memory s (MachineState.readWord mem 2720) (inputWord mem 0) (k+1) (initial (k+1) mem)

theorem initial_live (k : Nat) (mem : ByteArray) : Live (initial k mem) mem := by
  intro addr hd
  unfold initial MachineState.readWord
  rw [entry_keep _ _ addr 32 (by omega)]
  change MachineState.readWord (SquarePartialClear.memory _) addr = _
  rw [SquarePartialClear.readWord_outside _ addr (by omega)]
  exact StagedOperand.read_stage_outside mem 2112 8 addr (by omega)

theorem initial_represents (k : Nat) (mem : ByteArray) (A : Nat)
    (ha : Model.FastRepresents mem 2112 8 A) : Represents (initial k mem) A := by
  apply entry_represents
  apply SquarePartialClear.fastRepresents_outside _ 2368 8 A (by omega)
  exact Csub.fastRepresents_mcopy mem 2112 2368 8 A (by decide) ha

theorem memory_live (s : State) (k : Nat) (mem : ByteArray) : Live (memory s k mem) mem := by
  cases k with
  | zero => exact Live.refl mem
  | succ k => exact (PureLoop.memory_live s _ _ (k+1) (initial (k+1) mem)).trans (initial_live (k+1) mem)

theorem low (s : State) (k : Nat) (mem : ByteArray) (addr : Nat) (h : addr+32 ≤ 512) :
    MachineState.readWord (memory s k mem) addr = MachineState.readWord mem addr :=
  memory_live s k mem addr (Or.inl h)

theorem inverse (s : State) (k : Nat) (mem : ByteArray) :
    MachineState.readWord (memory s k mem) 2720 = MachineState.readWord mem 2720 :=
  memory_live s k mem 2720 (Or.inr (by decide))

theorem value (s : State) (k : Nat) (mem : ByteArray) (A N : Nat) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2112 8 A) (hm : Model.FastRepresents mem 0 8 N)
    (hodd : N%2=1) (hAN : A<N)
    (hinv : ((MachineState.readWord mem 224).toNat * (MachineState.readWord mem 2720).toNat+1)%2^256=0) :
    ∃ v, Model.FastRepresents (memory s k mem) 2368 8 v ∧
      v%N = ((fun x => Model.montMul N (Limbs.radix^8) x x)^[k] A)%N := by
  have hNodd : Odd N := Nat.odd_iff.mpr hodd
  have hpos : 0 < N := by omega
  have hlow : (MachineState.readWord mem 224).toNat = N % 2^256 := by
    simpa [Limbs.radix] using
      Model.readLimb_of_fastRepresents hm (k:=0) (by decide)
  have hinv' : (N*(MachineState.readWord mem 2720).toNat+1)%2^256=0 := by
    rw [hlow] at hinv
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using hinv
  cases k with
  | zero => omega
  | succ k =>
    rw [LegacyNormalize.old_radix]
    exact PureLoop.memory_value s (MachineState.readWord mem 2720) (inputWord mem 0) (k+1) (by omega)
      (initial (k+1) mem) A N (initial_represents (k+1) mem A ha)
      ((initial_live (k+1) mem).modulus N hm) hpos hNodd
      (fun i hi => inputWord_low hm i hi) (inputWord_high hm) hinv'

#print axioms initial_represents
#print axioms memory_live
#print axioms low
#print axioms inverse
#print axioms value
end HistoricalSearch.PureSquareMemory
