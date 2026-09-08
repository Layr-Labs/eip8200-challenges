import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.CiosCachedRoundedCarry

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

def oldProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩),
   .op .SUB, .op (.Swap ⟨0, by decide⟩), .push 0 0, .op .LT, .op .ADD]

/-- DUP11 reads the existing all-ones cache after the initial DUP2.
No equivalence is asserted for a state lacking this cache invariant. -/
def newProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op .ADD, .op .SUB,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

def initial (s : State) (mm lo mu bi pbi paEnd pbEnd flag k dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4692
           stack := [mm, lo, mu, bi, pbi, paEnd, pbEnd, flag, k,
                     UInt256.lnot (UInt256.ofNat 0), dst, ret] ++ rest }

theorem run_equiv (s : State) (mm lo mu bi pbi paEnd pbEnd flag k dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runProgram newProgram (initial s mm lo mu bi pbi paEnd pbEnd flag k dst ret rest) =
      runProgram oldProgram (initial s mm lo mu bi pbi paEnd pbEnd flag k dst ret rest) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [runProgram, oldProgram, newProgram, initial, runInstr,
    hc11, hc12, hc13, hc14, Nat.add_assoc, List.exchange, literal_eq_ofNat, succ_ofNat_mod]
  exact (rounded_high mm lo).symm

theorem existing_capacity (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    rest.length + 14 < 1024 := by omega

end Challenge.Modexp.Submission.Proofs.Bytecode.CiosCachedRoundedCarry

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.CiosCachedRoundedCarry.rounded_high
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.CiosCachedRoundedCarry.run_equiv
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.CiosCachedRoundedCarry.existing_capacity
