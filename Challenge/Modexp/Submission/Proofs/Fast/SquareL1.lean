import Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
import Challenge.Modexp.Submission.Proofs.Fast.SquareCoefficients
import Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareL1
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open SquareProducts SquareCoefficients
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

theorem run_cell (s : State) (pc off t c ai pbi pa pb delta dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8960+off).toNat 32) = s.activeWords)
    (ht : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat t.toNat 32) = s.activeWords) :
    runInstructions (StagedOperand.l1Program off t)
      (framed s pc ([c,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed {s with memory := (storeWord s.memory t.toNat
        (macSum (MachineState.readWord s.memory (UInt256.ofNat 8960+off).toNat)
          ai (MachineState.readWord s.memory t.toNat) c))}
        (pc+UInt256.ofNat 38)
        ([macCarry (MachineState.readWord s.memory (UInt256.ofNat 8960+off).toNat)
          ai (MachineState.readWord s.memory t.toNat) c,ai] ++ base pbi pa pb delta dst ret rest)) := by
  let x := MachineState.readWord s.memory (UInt256.ofNat 8960+off).toNat
  have hl := StagedOperand.run_load s pc off c ai pbi pa pb delta dst ret rest hcap ha
  have hp := L2.run_product s (pc+UInt256.ofNat 6) x ai c
    (base pbi pa pb delta dst ret rest)
    (by simp only [base, List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := L2.run_finish s (advancePC 18 (pc+UInt256.ofNat 6)) x ai c t t
    (base pbi pa pb delta dst ret rest)
    (by simp only [base, List.length_append, List.length_cons, List.length_nil]; omega) ht ht
  have hpc : advancePC 18 (pc+UInt256.ofNat 6)+UInt256.ofNat 14 = pc+UInt256.ofNat 38 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have h := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hl hp) hf
  simpa only [StagedOperand.l1Program, hpc, base, x, storeWord,
    List.cons_append, List.nil_append] using h

def partState (s : State) (mem : ByteArray) (ai : UInt256) (i k pc : Nat)
    (pbi pa pb delta dst ret : UInt256) (rest : List UInt256) : State :=
  let p := products mem (coefficient mem ai i) ai i k
  stateAt s p.memory pc ([p.carry,ai] ++ base pbi pa pb delta dst ret rest)

def cellBlock (j : Nat) (hj : 1 ≤ j) (hj8 : j < 8) :
    Block Artifact.submissionArtifact .Osaka (4157+38*j)
      (StagedOperand.l1Program (UInt256.ofNat (32*(7-j))) (UInt256.ofNat (tAddr 8 j))) := by
  interval_cases j
  · exact CarryRowBlocks.l1Mac1
  · exact CarryRowBlocks.l1Mac2
  · exact CarryRowBlocks.l1Mac3
  · exact CarryRowBlocks.l1Mac4
  · exact CarryRowBlocks.l1Mac5
  · exact CarryRowBlocks.l1Mac6
  · exact CarryRowBlocks.l1Mac7

theorem run_part (s : State) (mem : ByteArray) (ai : UInt256) (i k : Nat)
    (pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hk : 2 ≤ k) (hjk : i+k < 8) :
    runInstructions (StagedOperand.l1Program (UInt256.ofNat (32*(7-(i+k))))
        (UInt256.ofNat (tAddr 8 (i+k))))
      (partState s mem ai i k (4157+38*(i+k)) pbi pa pb delta dst ret rest) =
      some (partState s mem ai i (k+1) (4157+38*(i+(k+1))) pbi pa pb delta dst ret rest) := by
  let p := products mem (coefficient mem ai i) ai i k
  have hD : (UInt256.ofNat 8960+UInt256.ofNat (32*(7-(i+k)))).toNat = 8928+32*(8-(i+k)) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hT : (UInt256.ofNat (tAddr 8 (i+k))).toNat = tAddr 8 (i+k) := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    simp only [tAddr]; omega
  have hread : MachineState.readWord p.memory (8928+32*(8-(i+k))) = coefficient mem ai i (i+k) := by
    rw [read_products_outside _ _ _ _ _ (Or.inr (by omega)) k (by omega)]
    simp only [coefficient, if_neg (show i+k ≠ i by omega), if_neg (show i+k ≠ i+1 by omega), dWord]
  have ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8928+32*(8-(i+k))) 32) = s.activeWords :=
    EarlyCsub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have ht : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (tAddr 8 (i+k)) 32) = s.activeWords :=
    EarlyCsub.activeWords_fix s _ 32 (by decide) (by simp only [tAddr]; omega) hact
  have h := run_cell {s with memory := p.memory} (UInt256.ofNat (4157+38*(i+k)))
    (UInt256.ofNat (32*(7-(i+k)))) (UInt256.ofNat (tAddr 8 (i+k))) p.carry ai
    pbi pa pb delta dst ret rest hcap (by simpa only [hD] using ha) (by simpa only [hT] using ht)
  rw [hD, hT, hread, Challenge.EvmProof.Word.ofNat_add_mod] at h
  have hpc : 4157+38*(i+k)+38 = 4157+38*(i+(k+1)) := by omega
  simpa only [partState, products, stateAt, framed, p, hpc] using h

def gasSteps_part (s : State) (mem : ByteArray) (ai : UInt256) (i k : Nat)
    (pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hk : 2 ≤ k) (hjk : i+k < 8)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (partState s mem ai i k (4157+38*(i+k)) pbi pa pb delta dst ret rest)
      (partState s mem ai i (k+1) (4157+38*(i+(k+1))) pbi pa pb delta dst ret rest) :=
  (cellBlock (i+k) (by omega) hjk).steps
    (EarlyCsub.environment (partState s mem ai i k (4157+38*(i+k)) pbi pa pb delta dst ret rest)
      hcode hfork hrun hnp) rfl
    (run_part s mem ai i k pbi pa pb delta dst ret rest hcap hact hk hjk)

def gasSteps_suffix (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 7)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (partState s mem ai i 2 (4157+38*(i+2)) pbi pa pb delta dst ret rest)
      (partState s mem ai i (8-i) 4461 pbi pa pb delta dst ret rest) := by
  have h : ∀ k, i+(2+k) ≤ 8 → Challenge.EvmProof.GasSteps
      (partState s mem ai i 2 (4157+38*(i+2)) pbi pa pb delta dst ret rest)
      (partState s mem ai i (2+k) (4157+38*(i+(2+k))) pbi pa pb delta dst ret rest) := by
    intro k
    induction k with
    | zero => intro _; exact Challenge.EvmProof.GasSteps.refl _
    | succ k ih =>
      intro hk
      exact (ih (by omega)).trans (gasSteps_part s mem ai i (2+k) pbi pa pb delta dst ret rest
        hcap hact (by omega) (by omega) hcode hfork hrun hnp)
  have hf := h (6-i) (by omega)
  have he : 2+(6-i) = 8-i := by omega
  have he' : i+(8-i) = 8 := by omega
  simpa only [he, he', Nat.reduceMul, Nat.reduceAdd] using hf

end Challenge.Modexp.Submission.Proofs.Fast.SquareL1
