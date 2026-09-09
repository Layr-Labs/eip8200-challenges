import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true

/-!
# Fixed-address terminal L2 tail

The terminal cached L2 cell stores at the same fixed address in both programs.
The old program updates two pointers that its immediate continuation discards;
the replacement preserves those pointers and reaches the same complete state
after the two common `POP`s.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFixedL2Last

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word

def runProgram : List Instr → State → Option State
  | [], s => some s
  | op :: ops, s => (runInstr op s).bind (runProgram ops)

/-- The existing ten-byte terminal L2 tail. -/
def oldTail : List Instr :=
  [.push 2 (UInt256.ofNat 8288), .op .MSTORE, .op .POP,
   .op (.Dup ⟨8, by decide⟩), .op .ADD,
   .op (.Dup ⟨8, by decide⟩), .op .JUMPDEST, .op .JUMPDEST]

/-- The same-width tail that preserves the two dead pointer words. -/
def fixedTail : List Instr :=
  [.push 8 (UInt256.ofNat 8288), .op .MSTORE]

def discardPointers : List Instr := [.op .POP, .op .POP]

def input (s : State) (pc : Nat)
    (sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [sum, pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag,
              cache, ones, dst, ret] ++ rest }

/--
After the common two-word discard, the old and fixed tails produce exactly the
same EVM state.  In particular their program counter, memory and active-word
count agree.  No address premise is required because both stores use `8288`.
-/
theorem after_discard_eq (s : State) (pc : Nat)
    (sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hcapacity : rest.length + 15 < 1024) :
    runProgram (fixedTail ++ discardPointers)
      (input s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) =
    runProgram (oldTail ++ discardPointers)
      (input s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [runProgram, fixedTail, oldTail, discardPointers, input, runInstr,
    hcapacity, hc12, hc13, hc14,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc]

#print axioms after_discard_eq

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFixedL2Last
