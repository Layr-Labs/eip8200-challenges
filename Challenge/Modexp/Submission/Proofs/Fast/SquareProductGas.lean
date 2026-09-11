import Challenge.Modexp.Submission.Proofs.Fast.SquareParts

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareProductGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open SquareProducts SquareCoefficients SquareL1 SquareParts
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

theorem last_coefficient_zero (mem : ByteArray) (ai : UInt256) (a : Nat)
    (hd : Model.FastRepresents mem 8928 9 (2*a)) (ha : a < Limbs.radix^8) :
    coefficient mem ai 7 8 = UInt256.ofNat 0 := by
  have hc := coefficient_high_le_one mem a ai 0 hd ha (by decide)
  simp only [coefficient, Nat.reduceEqDiff, if_false] at hc
  apply Challenge.EvmProof.Word.word_ext
  simp only [coefficient, Nat.reduceEqDiff, if_false, ite_true,
    SquareWords.clearBit_toNat, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod]
  omega

def gasSteps_product (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb tag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpbi : pbi.toNat+32 ≤ 9472) (hdelta : pbi-pa = delta i)
    (hai : MachineState.readWord mem pbi.toNat = ai)
    (hlast : i = 7 → coefficient mem ai i 8 = UInt256.ofNat 0)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5191 (base pbi pa pb tag dst ret rest))
      (stateAt s (SquareRowModel.mid mem ai i) 4500
        (SquareRowModel.flag mem ai i :: base pbi pa pb (delta i) dst ret rest)) := by
  let P := products mem (coefficient mem ai i) ai i
  have hguard : Challenge.EvmProof.GasSteps
      (partState s mem ai i 1 5230 pbi pa pb (delta i) dst ret rest)
      (partState s mem ai i 1 (if i = 7 then 5295 else 5236) pbi pa pb (delta i) dst ret rest) := by
    apply SquareControls.guardBlock.steps (s := partState s mem ai i 1 5230 pbi pa pb (delta i) dst ret rest)
      (env.transfer rfl rfl) rfl
    have h := SquareControls.run_guard {s with memory := (P 1).memory} (P 1).carry ai pbi pa pb (delta i)
      (negative32 :: allOnes :: dst :: ret :: rest) (by simp only [List.length_cons]; omega)
      (by change Decode.isValidJumpDest s.executionEnv.code 5295 = true; rw [env.code]; exact jump_last)
    simpa only [partState, P, stateAt, framed, base, List.cons_append, List.nil_append,
      delta, SquareControls.guard_index i hi, apply_ite UInt256.ofNat] using h
  refine (gasSteps_head s mem ai i pbi pa pb tag dst ret rest hcap hact hi hpbi hdelta hai env).trans <|
    hguard.trans ?_
  by_cases hilast : i = 7
  · subst i
    have he : SquareRowModel.extra mem ai 7 = UInt256.ofNat 0 := by
      rw [SquareRowModel.extra, hlast rfl, SquareTop.mul_zero]
    let bs := base pbi pa pb (delta 7) dst ret rest
    have hlen : bs.length ≤ 1016 := by simp only [bs, base, List.length_append, List.length_cons, List.length_nil]; omega
    have hl : Challenge.EvmProof.GasSteps (stateAt s (P 1).memory 5295 ((P 1).carry :: ai :: bs))
        (stateAt s (storeWord (P 1).memory 8224 (MachineState.readWord (P 1).memory 8224+(P 1).carry)) 4497
          (UInt256.lt (MachineState.readWord (P 1).memory 8224+(P 1).carry) (P 1).carry :: ai :: bs)) :=
      SquareControls.lastBlock.steps (env.transfer rfl rfl) rfl
        (SquareControls.run_last s (P 1).memory (P 1).carry ai bs hlen hact
          (by rw [env.code]; exact jump_mu))
    have hm := SquareControls.muBlock.steps
      (env.transfer (t := stateAt s (storeWord (P 1).memory 8224 (MachineState.readWord (P 1).memory 8224+(P 1).carry))
        4497 (UInt256.lt (MachineState.readWord (P 1).memory 8224+(P 1).carry) (P 1).carry :: ai :: bs)) rfl rfl) rfl
      (SquareControls.run_mu s _ _ ai bs (by omega))
    simpa only [partState, stateAt, SquareRowModel.mid, SquareRowModel.flag, he,
      SquareTop.memory_zero, SquareTop.flag_zero, SquareRowModel.product, Nat.reduceSub,
      P, bs, Monpro.midMem1, storeWord, ite_true, List.cons_append, List.nil_append] using hl.trans hm
  · have hin : i < 7 := by omega
    have hj : Decode.isValidJumpDest s.executionEnv.code (SquareControls.target (delta i)).toNat = true := by
      rw [env.code, delta, SquareControls.target_index i hin, Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      interval_cases i
      · exact Artifact.isValidJumpDest_index 3213 (by rfl)
      · exact Artifact.isValidJumpDest_index 3245 (by rfl)
      · exact Artifact.isValidJumpDest_index 3277 (by rfl)
      · exact Artifact.isValidJumpDest_index 3309 (by rfl)
      · exact Artifact.isValidJumpDest_index 3341 (by rfl)
      · exact Artifact.isValidJumpDest_index 3373 (by rfl)
      · exact Artifact.isValidJumpDest_index 3405 (by rfl)
    have hd : Challenge.EvmProof.GasSteps
        (partState s mem ai i 2 5283 pbi pa pb (delta i) dst ret rest)
        (partState s mem ai i 2 (4166+38*(i+2)) pbi pa pb (delta i) dst ret rest) := by
      apply SquareControls.dispatchBlock.steps (s := partState s mem ai i 2 5283 pbi pa pb (delta i) dst ret rest)
        (env.transfer rfl rfl) rfl
      have h := SquareControls.run_dispatch {s with memory := (P 2).memory} (P 2).carry ai pbi pa pb (delta i)
        (negative32 :: allOnes :: dst :: ret :: rest) (by simp only [List.length_cons]; omega) hj
      simpa only [partState, P, stateAt, framed, base, List.cons_append, List.nil_append,
        delta, SquareControls.target_index i hin] using h
    have he : ai*MachineState.readWord (P (8-i)).memory 8928 = SquareRowModel.extra mem ai i := by
      rw [read_products_outside mem _ ai i 8928 (Or.inr (by decide)) (8-i) (by omega)]
      simp only [SquareRowModel.extra, coefficient, if_neg (show 8 ≠ i by omega),
        if_neg (show 8 ≠ i+1 by omega), dWord, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    have ht := SquareTop.gasSteps_top s (P (8-i)).memory (P (8-i)).carry ai
      (base pbi pa pb (delta i) dst ret rest)
      (by simp only [base, List.length_append, List.length_cons, List.length_nil]; omega)
      hact env.code env.forkEq env.running env.noPrecompile
    rw [he] at ht
    have ht' : Challenge.EvmProof.GasSteps
        (partState s mem ai i (8-i) 4470 pbi pa pb (delta i) dst ret rest)
        (stateAt s (SquareRowModel.mid mem ai i) 4500
          (SquareRowModel.flag mem ai i :: base pbi pa pb (delta i) dst ret rest)) := ht
    simpa only [if_neg hilast] using
      (gasSteps_cross s mem ai i pbi pa pb dst ret rest hcap hact hin env).trans
        (hd.trans ((gasSteps_suffix s mem ai i pbi pa pb (delta i) dst ret rest hcap hact hin
          env.code env.forkEq env.running env.noPrecompile).trans ht'))

end Challenge.Modexp.Submission.Proofs.Fast.SquareProductGas
