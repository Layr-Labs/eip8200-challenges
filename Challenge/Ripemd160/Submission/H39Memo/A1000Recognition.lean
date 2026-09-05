import Challenge.Ripemd160.Submission.H39Memo.A1000State
import Challenge.Ripemd160.Submission.H39Memo.Logic
import Challenge.Ripemd160.Submission.H39Memo.InputData

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM

theorem input_eq_of_checks (bytes : ByteArray) (hsize : bytes.size = 1000)
    (hfirst : MachineState.readWord bytes 0 = cacheWord)
    (hloop : ∀ k, k < 30 → MachineState.readWord bytes (32 * (k + 1)) = cacheWord)
    (htail : MachineState.readWord bytes 992 = tailWord) :
    bytes = inputA1000 := by
  apply Logic.byteArray_eq_of_readWord_cover bytes inputA1000
    (hsize.trans inputA1000_size.symm)
  intro k hk
  have hk32 : k < 32 := by omega
  change MachineState.readWord bytes (32 * k) =
    MachineState.readWord Proofs.Bytecode.KnownInputData.targetInput (32 * k)
  rw [Proofs.Bytecode.KnownInputData.targetInput_readWord k hk32]
  by_cases hk31 : k < 31
  · rw [Proofs.Bytecode.KnownInputData.expectedWord, if_pos hk31]
    by_cases hk0 : k = 0
    · simpa only [hk0, Nat.mul_zero] using hfirst
    · have hkpred : k - 1 + 1 = k := by omega
      simpa only [hkpred] using hloop (k - 1) (by omega)
  · have hkeq : k = 31 := by omega
    subst k
    exact htail

end Challenge.Ripemd160.Submission.H39Memo.A1000
