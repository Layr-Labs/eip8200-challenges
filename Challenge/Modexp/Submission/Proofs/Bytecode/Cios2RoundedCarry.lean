import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Cios2RoundedCarry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word

theorem gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := by
  rfl

/-- The rounded high-word identity holds for arbitrary words, including lo=0. -/
theorem rounded_high (mm lo : UInt256) :
    UInt256.lt (UInt256.ofNat 0) lo + (mm - (lo + UInt256.lt mm lo)) =
      (UInt256.gt mm (UInt256.lnot (UInt256.ofNat 0) + lo) + mm) - lo := by
  apply word_ext
  have hm : mm.toNat < 2 ^ 256 := mm.val.isLt
  have hl : lo.toNat < 2 ^ 256 := lo.val.isLt
  have hn : (UInt256.lnot (UInt256.ofNat 0)).toNat = 2 ^ 256 - 1 := by decide
  simp only [gt_eq_lt, word_toNat_add, word_toNat_sub, word_toNat_lt,
    word_toNat_ofNat, hn, Nat.zero_mod]
  split <;> split <;> split <;> omega

def runProgram : List Instr → State → Option State
  | [], s => some s
  | op :: ops, s => (runInstr op s).bind (runProgram ops)

/-- Exactly the eleven original instructions at physical PCs 4894 through 4904. -/
def oldProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩),
   .op .SUB, .op (.Swap ⟨0, by decide⟩), .push 0 0, .op .LT, .op .ADD]

def newProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 0 0, .op .NOT, .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op .ADD, .op .SUB,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

def initial (s : State) (mm lo : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4894, stack := [mm, lo] ++ rest }

/-- Same stack peak and physical endpoint. This is bounded-state equivalence,
not an assertion about executions starting at the strict stack-overflow limit. -/
theorem run_equiv (s : State) (mm lo : UInt256) (rest : List UInt256)
    (hrest : rest.length + 4 < 1024) :
    runProgram newProgram (initial s mm lo rest) =
      runProgram oldProgram (initial s mm lo rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [runProgram, oldProgram, newProgram, initial, runInstr,
    hc1, hc2, hc3, hrest, Nat.add_assoc, List.exchange,
    literal_eq_ofNat, succ_ofNat_mod]
  exact (rounded_high mm lo).symm

/-- The existing row-mid rest bound supplies this local stack bound unchanged. -/
theorem existing_capacity (rest : List UInt256) (hrest : rest.length ≤ 1008) :
    (7 + rest.length) + 4 < 1024 := by omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Cios2RoundedCarry

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.Cios2RoundedCarry.rounded_high
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.Cios2RoundedCarry.run_equiv
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.Cios2RoundedCarry.existing_capacity
