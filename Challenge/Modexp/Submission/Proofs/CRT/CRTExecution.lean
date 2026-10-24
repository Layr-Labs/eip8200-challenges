import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace HistoricalSearch.CRTExecution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

/-- Reconstruction for a column whose low digit does not need to be stored.
The full kernel has an additional store in its output columns. -/
def residueProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MOD,
   .op (.Dup ⟨3, by decide⟩), .op .SUB, .op .ADD,
   .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨0, by decide⟩), .op .MOD]

def highProgram (high : UInt256) : List Instr :=
  [.push 1 5, .op .SHR, .push 1 high, .op .SHL]

def carryProgram (low : UInt256) : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 1 low, .op .SHR, .op .ADD,
   .op (.Swap ⟨0, by decide⟩), .op .POP]

def program (low high : UInt256) : List Instr :=
  residueProgram ++ highProgram high ++ carryProgram low

def carryWord (H lo P low high : UInt256) : UInt256 :=
  UInt256.shiftRight lo low +
    UInt256.shiftLeft
      (UInt256.shiftRight (((P - lo % P) + H) % P) (UInt256.ofNat 5))
      high

theorem run_residue (s : State) (pc H lo P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1018) :
    runInstructions residueProgram {s with pc := pc, stack := H :: lo :: P :: rest} =
      some {s with pc := advancePC 9 pc, stack := ((P - lo % P + H) % P) :: lo :: P :: rest} := by
  have capacity (j : Nat) (hj : j ≤ 5) : rest.length + j < 1024 := by omega
  simp [residueProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    capacity, Nat.add_assoc, List.exchange, advancePC]

theorem run_high (s : State) (pc x high : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1021) :
    runInstructions (highProgram high) {s with pc := pc, stack := x :: rest} =
      some {s with pc := advancePC 6 pc, stack := UInt256.shiftLeft (UInt256.shiftRight x (UInt256.ofNat 5)) high :: rest} := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [highProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc1, hc2, List.exchange, advancePC, succ_eq_add, hp2, word_add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat]

theorem run_carry (s : State) (pc q lo low : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1019) :
    runInstructions (carryProgram low) {s with pc := pc, stack := q :: lo :: rest} =
      some {s with pc := advancePC 7 pc, stack := (UInt256.shiftRight lo low + q) :: rest} := by
  have capacity (j : Nat) (hj : j ≤ 4) : rest.length + j < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [carryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    capacity, Nat.add_assoc, List.exchange, advancePC, succ_eq_add, hp2, word_add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat]

/-- Exact symbolic execution, for arbitrary words, starting address and frame.
This theorem makes no whole-kernel or whole-program acceptance claim. -/
theorem run (s : State) (pc H lo P low high : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1018) :
    runInstructions (program low high) {s with pc := pc, stack := H :: lo :: P :: rest} =
      some {s with pc := advancePC 22 pc, stack := carryWord H lo P low high :: P :: rest} := by
  have h0 := run_residue s pc H lo P rest hcap
  have h1 := run_high s (advancePC 9 pc) ((P - lo % P + H) % P) high
    (lo :: P :: rest) (by simp only [List.length_cons]; omega)
  have h2 := run_carry s (advancePC 6 (advancePC 9 pc))
    (UInt256.shiftLeft (UInt256.shiftRight ((P - lo % P + H) % P) (UInt256.ofNat 5)) high)
    lo low (P :: rest) (by simp only [List.length_cons]; omega)
  have both := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ h0 h1) h2
  simpa only [program, carryWord, ← advancePC_add] using both

end HistoricalSearch.CRTExecution
