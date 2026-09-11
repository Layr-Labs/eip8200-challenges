import Challenge.Modexp.Submission.Proofs.Fast.SquareCross
import Challenge.Modexp.Submission.Proofs.Fast.SquareControls
import Challenge.Modexp.Submission.Proofs.Fast.SquareL1
import Challenge.Modexp.Submission.Proofs.Fast.SquareRowModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareParts
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open SquareProducts SquareCoefficients SquareL1
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

def headProgram := SquareDiagonal.headProgram ++ SquareDiagonal.diagProgram

def headBlock : Block Artifact.submissionArtifact .Osaka 5191 headProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3937 35 5191 headProgram
    (by decide) (by rfl) (by rfl) (by decide)
def crossBlock : Block Artifact.submissionArtifact .Osaka 5236 SquareCross.crossProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3976 40 5236 SquareCross.crossProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jump_last : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5295 = true :=
  Artifact.isValidJumpDest_index 4024 (by rfl)
theorem jump_mu : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4497 = true :=
  Artifact.isValidJumpDest_index 3428 (by rfl)
theorem jump_row : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5191 = true :=
  Artifact.isValidJumpDest_index 3937 (by rfl)
theorem jump_init : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5040 = true :=
  Artifact.isValidJumpDest_index 3836 (by rfl)

def delta (i : Nat) : UInt256 := UInt256.ofNat (32*(7-i))

theorem addr (a i : Nat) (ha : a ≤ 9280) :
    (UInt256.ofNat a+delta i).toNat = a+32*(7-i) := by
  rw [delta, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem run_head (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb tag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpbi : pbi.toNat+32 ≤ 9472) (hdelta : pbi-pa = delta i)
    (hai : MachineState.readWord mem pbi.toNat = ai) :
    runInstructions headProgram (stateAt s mem 5191 (base pbi pa pb tag dst ret rest)) =
      some (partState s mem ai i 1 5230 pbi pa pb (delta i) dst ret rest) := by
  have haddr : (UInt256.ofNat 8256+delta i).toNat = tAddr 8 i := by
    rw [addr 8256 i (by decide)]; rfl
  have ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8256+delta i).toNat 32) = s.activeWords := by
    rw [haddr]
    exact EarlyCsub.activeWords_fix s _ 32 (by decide) (by simp only [tAddr]; omega) hact
  have hh := SquareDiagonal.run_head {s with memory := mem} pbi pa pb tag dst ret rest hcap hact hpbi
  rw [hdelta, hai] at hh
  have hd := SquareDiagonal.run_diag {s with memory := mem} ai pbi pa pb (delta i) dst ret rest hcap ha
  rw [haddr] at hd
  have h := runInstructions_append_some _ _ _ _ _ hh hd
  simpa only [headProgram, partState, products, coefficient, if_pos rfl, ite_true,
    stateAt, framed, Nat.add_zero] using h

def gasSteps_head (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb tag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpbi : pbi.toNat+32 ≤ 9472) (hdelta : pbi-pa = delta i)
    (hai : MachineState.readWord mem pbi.toNat = ai)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5191 (base pbi pa pb tag dst ret rest))
      (partState s mem ai i 1 5230 pbi pa pb (delta i) dst ret rest) :=
  headBlock.steps (env.transfer rfl rfl) rfl
    (run_head s mem ai i pbi pa pb tag dst ret rest hcap hact hi hpbi hdelta hai)

theorem run_cross (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 7) :
    runInstructions SquareCross.crossProgram
      (partState s mem ai i 1 5236 pbi pa pb (delta i) dst ret rest) =
      some (partState s mem ai i 2 5283 pbi pa pb (delta i) dst ret rest) := by
  let p := products mem (coefficient mem ai i) ai i 1
  have hD : (UInt256.ofNat 8928+delta i).toNat = 8928+32*(8-(i+1)) := by
    rw [addr 8928 i (by decide)]; omega
  have hT : (UInt256.ofNat 8224+delta i).toNat = tAddr 8 (i+1) := by
    rw [addr 8224 i (by decide)]; simp only [tAddr]; omega
  have hread : SquareCross.xword p.memory (delta i) = coefficient mem ai i (i+1) := by
    rw [SquareCross.xword, hD,
      read_products_outside _ _ _ _ _ (Or.inr (by omega)) 1 (by omega)]
    simp only [coefficient, if_neg (show i+1 ≠ i by omega), ite_true, dWord]
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8928+delta i).toNat 32) = s.activeWords := by
    rw [hD]; exact EarlyCsub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8224+delta i).toNat 32) = s.activeWords := by
    rw [hT]; exact EarlyCsub.activeWords_fix s _ 32 (by decide) (by simp only [tAddr]; omega) hact
  have h := SquareCross.run_cross {s with memory := p.memory} p.carry ai pbi pa pb (delta i)
    dst ret rest hcap hA hB
  rw [hread, hT] at h
  simpa only [partState, products, p, stateAt, framed] using h

def gasSteps_cross (s : State) (mem : ByteArray) (ai : UInt256) (i : Nat)
    (pbi pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) (hi : i < 7)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps
      (partState s mem ai i 1 5236 pbi pa pb (delta i) dst ret rest)
      (partState s mem ai i 2 5283 pbi pa pb (delta i) dst ret rest) :=
  crossBlock.steps (env.transfer rfl rfl) rfl
    (run_cross s mem ai i pbi pa pb dst ret rest hcap hact hi)

end Challenge.Modexp.Submission.Proofs.Fast.SquareParts
