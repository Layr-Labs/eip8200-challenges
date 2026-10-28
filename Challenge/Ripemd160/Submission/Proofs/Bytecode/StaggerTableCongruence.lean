import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
open EvmSemantics PairedScheduleMemory

theorem storeDescending_congr (memory : ByteArray) (a b : Nat → UInt256)
    (first count : Nat) (h : ∀ j, first ≤ j → j < first + count → a j = b j) :
    storeDescending memory a first count = storeDescending memory b first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [storeDescending, storeDescending,
      ih (first + 1) (fun j hj hj' => h j (by omega) (by omega)),
      h first (by omega) (by omega)]
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
open EvmSemantics StaggerTableMemory

theorem resultMemory_congr (memory : ByteArray) (a b : Nat → UInt256)
    (h : ∀ i, i < 16 → a i = b i) : resultMemory memory a = resultMemory memory b := by
  apply storeDescending_congr
  intro j hj hj'
  exact h slots[j]! (slots_lt j (by omega))
#print axioms resultMemory_congr
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
