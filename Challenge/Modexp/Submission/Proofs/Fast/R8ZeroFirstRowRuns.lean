import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowModel
import Mathlib.Algebra.Group.Fin.Basic

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro

def cellProgram (a t : UInt256) : List Instr :=
  [.push 2 a, .op .MLOAD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .GT,
   .op .SUB, .op .SUB, .op (.Swap ⟨0, by decide⟩), .push 2 t, .op .MSTORE]

def cellA (a : UInt256) : List Instr := (cellProgram a 0).take 9
def cellB : List Instr := ((cellProgram 0 0).drop 9).take 12
def cellC (t : UInt256) : List Instr := (cellProgram 0 t).drop 21

theorem run_cellA (s : State) (pc c bi w0 w1 w2 w3 w4 M : UInt256)
    (a : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (ha : a + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory a
    runInstructions (cellA (UInt256.ofNat a))
      { s with pc := pc, stack := c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } =
    some { s with pc := advancePC 11 pc,
                  stack := UInt256.mulMod bi x M :: (x*bi) :: c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  have han : (UInt256.ofNat a).toNat = a := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hA := activeWords_fix s a 32 (by decide) ha hact
  simp [cellA, cellProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h8, h9, h10, h11, h12, State.activeWordsAfterUInt256, han, hA, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  rfl

theorem run_cellB (s : State) (pc mm lo c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1017) :
    runInstructions cellB
      { s with pc := pc, stack := mm :: lo :: c :: rest } =
    some { s with pc := advancePC 12 pc,
                  stack := ((UInt256.gt c (c+lo) - (UInt256.gt lo mm - mm)) - lo) :: (c+lo) :: rest } := by
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  simp [cellB, cellProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h3, h4, h5, h6, advancePC]

theorem run_cellC (s : State) (pc c u : UInt256) (t : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1020)
    (ht : t + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (cellC (UInt256.ofNat t))
      { s with pc := pc, stack := c :: u :: rest } =
    some { s with pc := advancePC 5 pc, stack := c :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded u.toNat 32) t } := by
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have htn : (UInt256.ofNat t).toNat = t := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hT := activeWords_fix s t 32 (by decide) ht hact
  simp [cellC, cellProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h2, h3, State.activeWordsAfterUInt256, htn, hT, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  rfl

theorem run_cell (s : State) (pc c bi w0 w1 w2 w3 w4 M : UInt256)
    (a t : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (ha : a + 32 ≤ 2816) (ht : t + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory a
    runInstructions (cellProgram (UInt256.ofNat a) (UInt256.ofNat t))
      { s with pc := pc, stack := c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } =
    some { s with pc := advancePC 28 pc,
                  stack := R4Math.zCarry x bi c M :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (R4Math.zSum x bi c).toNat 32) t } := by
  let x := MachineState.readWord s.memory a
  have h0 := run_cellA s pc c bi w0 w1 w2 w3 w4 M a rest hcap ha hact
  have h1 := run_cellB s (advancePC 11 pc) (UInt256.mulMod bi x M) (x*bi) c
    (bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest) (by simp only [List.length_cons]; omega)
  have h2 := run_cellC s (advancePC 23 pc) (R4Math.zCarry x bi c M) (R4Math.zSum x bi c) t
    (bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest) (by simp only [List.length_cons]; omega) ht hact
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  exact runInstructions_append_some _ _ _ _ _ h01 h2

def cellsProgram : Nat → List Instr
  | 0 => []
  | k+1 => cellsProgram k ++ cellProgram (UInt256.ofNat (SquareModel.aAddr 8 (k+1)))
      (UInt256.ofNat (Monpro.tAddr 8 (k+1)))

theorem run_cells (s : State) (pc bi w0 w1 w2 w3 w4 : UInt256)
    (q : MacState) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (hact : 88 ≤ s.activeWords.toNat) :
    ∀ k, k ≤ 7 →
      runInstructions (cellsProgram k)
        { s with pc := pc, stack := q.carry :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: maxWord :: rest,
                 memory := q.memory } =
      some { s with pc := advancePC (28*k) pc,
                    stack := (zeroRun q bi k).carry :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: maxWord :: rest,
                    memory := (zeroRun q bi k).memory } := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have h0 := ih (by omega)
      have h1 := run_cell { s with memory := (zeroRun q bi k).memory }
        (advancePC (28*k) pc) (zeroRun q bi k).carry bi w0 w1 w2 w3 w4 maxWord
        (SquareModel.aAddr 8 (k+1)) (Monpro.tAddr 8 (k+1)) rest hcap
        (by unfold SquareModel.aAddr; omega) (by unfold Monpro.tAddr; omega) hact
      have h := runInstructions_append_some _ _ _ _ _ h0 h1
      have hpc : advancePC 28 (advancePC (28*k) pc) = advancePC (28*(k+1)) pc := by
        rw [← advancePC_add]
        congr 1
      simpa only [cellsProgram, zeroRun, zeroStep, hpc] using h

#print axioms run_cell
#print axioms run_cells
end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
