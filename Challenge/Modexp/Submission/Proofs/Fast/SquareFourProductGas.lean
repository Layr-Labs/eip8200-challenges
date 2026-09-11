import Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowModel
import Challenge.Modexp.Submission.Proofs.Fast.SquareProductGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourProductGas
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareInit
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

theorem coefficient_shift (mem : ByteArray) (ai : UInt256) (i j : Nat) :
    SquareFourCoefficients.coefficient mem ai i j =
      SquareCoefficients.coefficient mem ai (i+4) (j+4) := by
  have hp : 8-(j+4) = 4-j := by omega
  have he : j+4 = i+4 ↔ j=i := by omega
  have hn : j+4 = i+4+1 ↔ j=i+1 := by omega
  simp only [SquareFourCoefficients.coefficient, SquareCoefficients.coefficient,
    SquareFourCoefficients.dWord, SquareCoefficients.dWord, hp, he, hn]

theorem products_shift (mem : ByteArray) (ai : UInt256) (i : Nat) :
    ∀ k, i+k ≤ 4 →
      SquareFourProducts.products mem (SquareFourCoefficients.coefficient mem ai i) ai i k =
        SquareProducts.products mem (SquareCoefficients.coefficient mem ai (i+4)) ai (i+4) k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have prev := ih (by omega)
    have ha : tAddr 4 (i+k) = tAddr 8 (i+4+k) := by
      simp only [tAddr]
      congr 1
      omega
    have hc := coefficient_shift mem ai i (i+k)
    have hi : i+k+4 = i+4+k := by omega
    rw [hi] at hc
    simp only [SquareFourProducts.products, SquareProducts.products]
    rw [prev, ha, hc]

theorem product_eq (mem : ByteArray) (ai : UInt256) (i : Nat) (hi : i ≤ 4) :
    SquareFourRowModel.product mem ai i = SquareRowModel.product mem ai (i+4) := by
  have hn : 8-(i+4) = 4-i := by omega
  simp only [SquareFourRowModel.product, SquareRowModel.product, hn]
  exact products_shift mem ai i (4-i) (by omega)

theorem extra_eq (mem : ByteArray) (ai : UInt256) (i : Nat) :
    SquareFourRowModel.extra mem ai i = SquareRowModel.extra mem ai (i+4) := by
  simp only [SquareFourRowModel.extra, SquareRowModel.extra]
  exact congrArg (fun x : UInt256 => ai*x) (coefficient_shift mem ai i 4)

theorem mid_eq (mem : ByteArray) (ai : UInt256) (i : Nat) (hi : i ≤ 4) :
    SquareFourRowModel.mid mem ai i = SquareRowModel.mid mem ai (i+4) := by
  rw [SquareFourRowModel.mid, SquareRowModel.mid, product_eq mem ai i hi, extra_eq]

theorem flag_eq (mem : ByteArray) (ai : UInt256) (i : Nat) (hi : i ≤ 4) :
    SquareFourRowModel.flag mem ai i = SquareRowModel.flag mem ai (i+4) := by
  rw [SquareFourRowModel.flag, SquareRowModel.flag, product_eq mem ai i hi, extra_eq]

def gasSteps_product (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb tag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 4)
    (hpbi : pbi.toNat+32 ≤ 9472) (hdelta : pbi-pa = SquareParts.delta (i+4))
    (hai : MachineState.readWord mem pbi.toNat = ai)
    (hhigh : SquareWords.clearBit (MachineState.readWord mem 8928) = UInt256.ofNat 0)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5191 (base pbi pa pb tag dst ret rest))
      (stateAt s (SquareFourRowModel.mid mem ai i) 4500
        (SquareFourRowModel.flag mem ai i :: base pbi pa pb (SquareParts.delta (i+4)) dst ret rest)) := by
  have hl : i+4 = 7 → SquareCoefficients.coefficient mem ai (i+4) 8 = UInt256.ofNat 0 := by
    intro h
    simpa only [h, SquareCoefficients.coefficient, Nat.reduceEqDiff, if_false, ite_true,
      SquareCoefficients.dWord, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] using hhigh
  have h := SquareProductGas.gasSteps_product s mem ai (i+4) pbi pa pb tag dst ret rest
    hcap hact (by omega) hpbi hdelta hai hl env
  rw [← mid_eq mem ai i (by omega), ← flag_eq mem ai i (by omega)] at h
  exact h

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourProductGas
