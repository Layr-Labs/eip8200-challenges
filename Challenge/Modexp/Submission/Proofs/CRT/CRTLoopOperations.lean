import Challenge.Modexp.Submission.Proofs.CRT.CRTGasStepsNormalized
import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopInduction
import Challenge.Modexp.Submission.Proofs.Fast.CRTExitTail
import Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTLoopOperations
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.PureLoop
open HistoricalSearch.LoopInvariant HistoricalSearch.CRTLoopInduction

variable (s : State) (minv : UInt256) (n : Nat → UInt256)

theorem raw_digits (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (h : Invariant mem n minv f N k A) :
    ∀ i < 9, (rawDigits (raw s minv n mem) i).toNat < 2^244 := by
  exact (result_contract {s with memory := mem} minv n [] A N h.operand
    (by simpa only [LegacyNormalize.old_radix] using h.modulus.1)
    h.positive h.odd h.toStatic.nlow h.toStatic.nhigh h.inverse).1

theorem flag_value (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (h : Invariant mem n minv f N k A) :
    (UInt256.shiftRight (rawDigits (raw s minv n mem) 8) (UInt256.ofNat 192)).toNat =
      Q s minv n mem / R :=
  CRTWordPacking.overflow_toNat _ (raw_digits s minv n mem f N k A h)

theorem flag_word (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (h : Invariant mem n minv f N k A) :
    MachineState.readWord (checked s minv n mem) 1760 = UInt256.ofNat (Q s minv n mem / R) := by
  rw [word_eq_ofNat_toNat (MachineState.readWord (checked s minv n mem) 1760)]
  unfold checked
  rw [checked_flag _ (raw_digits s minv n mem f N k A h)]
  rfl

theorem counter_word (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (h : Invariant mem n minv f N k A) :
    MachineState.readWord (checked s minv n mem) 1728 = UInt256.ofNat (k-1) := by
  rw [checked_counter, word_eq_ofNat_toNat (MachineState.readWord mem 1728), h.counter]

def checkedRound (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (h : Invariant mem n minv f N k A) :
    GasSteps (atCache s mem 5859 n minv f)
      (atCache s (checked s minv n mem) (if Q s minv n mem < R then 8398 else 8800) n minv f) := by
  have g1 := CRTGasStepsNormalized.kernel s mem n minv f env hcap hact
  have g2 := CRTGasStepsNormalized.overflow s (raw s minv n mem) n minv f env hcap hact
  have he := flag_value s minv n mem f N k A h
  rw [he] at g2
  by_cases hl : Q s minv n mem < R
  · have hz := Nat.div_eq_of_lt hl
    simpa only [checked, hz, ↓reduceIte, if_pos hl] using g1.trans g2
  · have hnz : Q s minv n mem / R ≠ 0 := Nat.ne_of_gt (Nat.div_pos (by omega) (Nat.two_pow_pos 2048))
    simpa only [checked, if_neg hnz, if_neg hl] using g1.trans g2

#print axioms flag_word
#print axioms counter_word
#print axioms checkedRound
end HistoricalSearch.CRTLoopOperations
