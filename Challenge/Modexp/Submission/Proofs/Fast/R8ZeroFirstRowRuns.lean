import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowModel
import Mathlib.Algebra.Group.Fin.Basic

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro

/-- The pre-existing twenty-four-instruction cell. Only the last cell of the first row, whose
store is merged into `finishStore`, still runs its first twenty-one instructions (`cellAB`). -/
def cellProgramOld (a t : UInt256) : List Instr :=
  [.push 2 a, .op .MLOAD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .GT,
   .op .SUB, .op .SUB, .op (.Swap ⟨0, by decide⟩), .push 2 t, .op .MSTORE]

/-- The zero-accumulator cell: twenty-three instructions in the same twenty-eight bytes as the
twenty-four-instruction cell it replaces.  The sum is stored as soon as it exists, and the
low product is folded into the high-word correction by one `ADD` instead of a separate
`SUB`, which removes one `SWAP`.  The store address is a `PUSH3` so the byte length is kept. -/
def cellProgram (a t : UInt256) : List Instr :=
  [.push 2 a, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .MUL,
   .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .push 3 t, .op .MSTORE,
   .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op .SUB, .op .ADD, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .SUB]

def cellA (a : UInt256) : List Instr := (cellProgramOld a 0).take 9
def cellB : List Instr := ((cellProgramOld 0 0).drop 9).take 12

def newA (a : UInt256) : List Instr := (cellProgram a 0).take 5
def newB (t : UInt256) : List Instr := ((cellProgram 0 t).drop 5).take 8
def newC : List Instr := (cellProgram 0 0).drop 13

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
  simp [cellA, cellProgramOld, runInstructions, Challenge.EvmProof.Stepper.runInstr,
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
  simp [cellB, cellProgramOld, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h3, h4, h5, h6, advancePC]

private theorem word_mul_comm' (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

private theorem word_sub_add (a b c : UInt256) : a - (b + c) = a - b - c := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val - (b.val + c.val)).val = (a.val - b.val - c.val).val
  rw [sub_add_eq_sub_sub]

theorem run_newA (s : State) (pc c bi : UInt256)
    (a : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1016)
    (ha : a + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory a
    runInstructions (newA (UInt256.ofNat a))
      { s with pc := pc, stack := c :: bi :: rest } =
    some { s with pc := advancePC 7 pc, stack := (x*bi) :: x :: c :: bi :: rest } := by
  have u2 : rest.length + 1 + 1 < 1024 := by omega
  have u3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have u4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have u5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have han : (UInt256.ofNat a).toNat = a := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hA := activeWords_fix s a 32 (by decide) ha hact
  simp [newA, cellProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, u2, u3, u4, u5, u6, State.activeWordsAfterUInt256, han, hA, advancePC]
  try constructorm* _ ∧ _
  all_goals (try simp only [succ_eq_add, word_add_assoc])
  all_goals first
    | exact word_mul_comm' _ _
    | omega
    | rfl
    | (congr 1; decide)

theorem run_newB (s : State) (pc lo x c bi w0 w1 w2 w3 w4 M : UInt256)
    (t : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (ht : t + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (newB (UInt256.ofNat t))
      { s with pc := pc, stack := lo :: x :: c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } =
    some { s with pc := advancePC 11 pc,
                  stack := (c + lo) :: bi :: M :: lo :: x :: c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (c + lo).toNat 32) t } := by
  have u10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u14 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u15 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have htn : (UInt256.ofNat t).toNat = t := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hT := activeWords_fix s t 32 (by decide) ht hact
  simp [newB, cellProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, u10, u11, u12, u13, u14, u15, State.activeWordsAfterUInt256, htn, hT, advancePC]
  try constructorm* _ ∧ _
  all_goals (try simp only [succ_eq_add, word_add_assoc])
  all_goals first
    | omega
    | rfl
    | (congr 1; decide)

theorem run_newC (s : State) (pc sm bi M lo x c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1017) :
    runInstructions newC
      { s with pc := pc, stack := sm :: bi :: M :: lo :: x :: c :: rest } =
    some { s with pc := advancePC 10 pc,
                  stack := (UInt256.gt c sm - ((UInt256.gt lo (UInt256.mulMod x bi M) -
                    UInt256.mulMod x bi M) + lo)) :: rest } := by
  have u1 : rest.length + 1 < 1024 := by omega
  have u2 : rest.length + 1 + 1 < 1024 := by omega
  have u3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have u4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have u5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have u6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [newC, cellProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, u1, u2, u3, u4, u5, u6, advancePC]

theorem run_cell (s : State) (pc c bi w0 w1 w2 w3 w4 M : UInt256)
    (a t : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (ha : a + 32 ≤ 2816) (ht : t + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory a
    runInstructions (cellProgram (UInt256.ofNat a) (UInt256.ofNat t))
      { s with pc := pc, stack := c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } =
    some { s with pc := advancePC 28 pc,
                  stack := R4Math.zCarry x bi c M :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (R4Math.zSum x bi c).toNat 32) t } := by
  let x := MachineState.readWord s.memory a
  have h0 := run_newA s pc c bi a (w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest)
    (by simp only [List.length_cons]; omega) ha hact
  have h1 := run_newB s (advancePC 7 pc) (x*bi) x c bi w0 w1 w2 w3 w4 M t rest hcap ht hact
  let mem' := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (c + x*bi).toNat 32) t
  have h2 := run_newC { s with memory := mem' } (advancePC 11 (advancePC 7 pc))
    (c + x*bi) bi M (x*bi) x c (bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest)
    (by simp only [List.length_cons]; omega)
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h := runInstructions_append_some _ _ _ _ _ h01 h2
  have hsplit : cellProgram (UInt256.ofNat a) (UInt256.ofNat t) =
      (newA (UInt256.ofNat a) ++ newB (UInt256.ofNat t)) ++ newC := by
    simp [cellProgram, newA, newB, newC]
  have hpc : advancePC 10 (advancePC 11 (advancePC 7 pc)) = advancePC 28 pc := by
    rw [← advancePC_add, ← advancePC_add]
  rw [hsplit]
  simp only [hpc] at h
  rw [h]
  unfold R4Math.zCarry R4Math.zSum
  rw [mulMod_comm x bi M, word_sub_add]

/-- A cell without its final store (`cellA ++ cellB`): used for the last cell of the
first row, whose store is merged into `finishStore`. -/
def cellAB (a : UInt256) : List Instr := cellA a ++ cellB

theorem run_cellAB (s : State) (pc c bi w0 w1 w2 w3 w4 M : UInt256)
    (a : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (ha : a + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory a
    runInstructions (cellAB (UInt256.ofNat a))
      { s with pc := pc, stack := c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } =
    some { s with pc := advancePC 23 pc,
                  stack := R4Math.zCarry x bi c M :: R4Math.zSum x bi c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } := by
  let x := MachineState.readWord s.memory a
  have h0 := run_cellA s pc c bi w0 w1 w2 w3 w4 M a rest hcap ha hact
  have h1 := run_cellB s (advancePC 11 pc) (UInt256.mulMod bi x M) (x*bi) c
    (bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest) (by simp only [List.length_cons]; omega)
  exact runInstructions_append_some _ _ _ _ _ h0 h1

def cellsProgram : Nat → List Instr
  | 0 => []
  | k+1 => cellsProgram k ++ cellProgram (UInt256.ofNat (SquareModel.aAddr 8 (k+1)))
      (UInt256.ofNat (Monpro.tAddr 8 (k+1)))

theorem run_cells (s : State) (pc bi w0 w1 w2 w3 w4 : UInt256)
    (q : MacState) (rest : List UInt256) (hcap : rest.length ≤ 1008)
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
