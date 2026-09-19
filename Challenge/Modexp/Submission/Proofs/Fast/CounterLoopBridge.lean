import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
External proof component for GPT 6 Pro's final counter-restoration proposal.
The concrete row/CSUB commutation and caller invariant remain separate duties.
-/
namespace CounterLoopBridge

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

theorem readWord_zero_of_size_le (mem : ByteArray) (addr : Nat)
    (hsize : mem.size ≤ addr) :
    MachineState.readWord mem addr = UInt256.ofNat 0 := by
  have hzero : MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) addr) addr =
      UInt256.ofNat 0 :=
    Challenge.EvmProof.Memory.readWord_writeBytes_of_lt mem addr 0 (by norm_num)
  have hread : MachineState.readPadded mem addr 32 =
      MachineState.readPadded
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) addr) addr 32 := by
    apply Challenge.EvmProof.Memory.readPadded_congr
    intro i hi
    rw [Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le mem _ (by omega),
      MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, if_pos (by omega),
      Challenge.Modexp.Submission.Proofs.Fast.Monpro.natToBytesPadded_zero_byte
        32 (addr + i - addr) (by omega)]
  rw [← hzero]
  unfold MachineState.readWord
  rw [hread]

/-- A nonzero configuration word implies physical memory reaches that word.
This uses no claim about the activeWords gas-accounting field. -/
theorem physicalSize_of_s32 (mem : ByteArray) (n : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n)) :
    2656 ≤ mem.size := by
  by_contra hsmall
  have hz := readWord_zero_of_size_le mem 2688 (by omega)
  rw [hs32] at hz
  have heq := congrArg UInt256.toNat hz
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (show 32 * n < 2 ^ 256 by omega)] at heq
  norm_num at heq
  omega

theorem countMem_overwrite (mem : ByteArray) (a b : Nat) :
    countMem (countMem mem a) b = countMem mem b := by
  have ha : (Data.Bytes.natToBytesPadded a 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size a 32
  have hb : (Data.Bytes.natToBytesPadded b 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size b 32
  unfold countMem
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, ha, hb]
    split_ifs <;> omega
  · intro i hi hi'
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi',
      MachineState.writeBytes_getElem?_getD, hb]
    by_cases hwin : 2624 ≤ i ∧ i < 2656
    · rw [if_pos hwin, MachineState.writeBytes_getElem?_getD, hb, if_pos hwin]
    · rw [if_neg hwin, MachineState.writeBytes_getElem?_getD, ha, if_neg hwin,
        MachineState.writeBytes_getElem?_getD, hb, if_neg hwin]

section Abstract

variable {Memory : Type}

def rawRun (raw : Memory → Memory) : Nat → Memory → Memory
  | 0, mem => mem
  | k + 1, mem => rawRun raw k (raw mem)

def paintedRun (paint : Memory → Nat → Memory) (raw : Memory → Memory) :
    Nat → Memory → Memory
  | 0, mem => mem
  | k + 1, mem => paintedRun paint raw k (paint (raw mem) k)

/-- Every positive old run is one final paint of the corresponding raw run.
The hypotheses explicitly require the concrete invariant and commutation.
No claim is made that arbitrary MODEXP memories satisfy those hypotheses. -/
theorem paintedRun_eq_final_paint
    (paint : Memory → Nat → Memory) (raw : Memory → Memory)
    (Good : Memory → Prop)
    (hcollapse : ∀ mem a b, paint (paint mem a) b = paint mem b)
    (hraw : ∀ mem, Good mem → Good (raw mem))
    (hcomm : ∀ mem c, Good mem → raw (paint mem c) = paint (raw mem) c)
    (k : Nat) : ∀ mem c, Good mem →
      paintedRun paint raw (k + 1) (paint mem c) =
        paint (rawRun raw (k + 1) mem) 0 := by
  induction k with
  | zero =>
      intro mem c hm
      simp only [paintedRun, rawRun, hcomm mem c hm, hcollapse]
  | succ k ih =>
      intro mem c hm
      rw [paintedRun, hcomm mem c hm, hcollapse]
      exact ih (raw mem) (k + 1) (hraw mem hm)

theorem unpaintedRun_eq_final_paint
    (paint : Memory → Nat → Memory) (raw : Memory → Memory)
    (Good : Memory → Prop)
    (hcollapse : ∀ mem a b, paint (paint mem a) b = paint mem b)
    (hraw : ∀ mem, Good mem → Good (raw mem))
    (hcomm : ∀ mem c, Good mem → raw (paint mem c) = paint (raw mem) c)
    (k : Nat) (mem : Memory) (hm : Good mem) :
    paintedRun paint raw (k + 1) mem =
      paint (rawRun raw (k + 1) mem) 0 := by
  cases k with
  | zero => rfl
  | succ k =>
      exact paintedRun_eq_final_paint paint raw Good hcollapse hraw hcomm
        k (raw mem) (k + 1) (hraw mem hm)

end Abstract
end CounterLoopBridge


