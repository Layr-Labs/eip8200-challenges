import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

/-!
Artifact-independent relative-depth lookup for every staged digit.
The caller supplies the proved shifted-nibble address and two live tail slots.
Concrete bytecode bindings are supplied separately.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLookup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program (slot : Nat) (hslot : slot ≤ 11) (shift : Fin 256) : List Instr :=
  [.op (.Dup ⟨slot + 2, by omega⟩), .push 1 (UInt256.ofNat shift.val),
   .op .SHR, .op (.Dup ⟨slot + 4, by omega⟩), .op .AND,
   .op .MLOAD, .op .MULMOD]

def framed (template : State) (pc : UInt256) (base modulus : UInt256)
    (stack : List UInt256) : State :=
  { template with
    pc := pc
    stack := stack
    memory := WindowTableMemory.tableMemory base modulus
    activeWords := UInt256.ofNat 16 }

/-- Consume the first staged modulus; the remaining tail is exactly preserved.
For the three positions in a group, `slot` is 11, 6 or 1 respectively. -/
theorem run_lookup (template : State) (pc base modulus accumulator exponent : UInt256)
    (tail : List UInt256) (slot : Nat) (hslot : slot ≤ 11) (shift : Fin 256)
    (index : Nat) (hindex : index < 16)
    (hexponent : tail[slot]? = some exponent)
    (hmask : tail[slot + 1]? = some (UInt256.ofNat 480))
    (haddress :
      (UInt256.land (UInt256.ofNat 480)
        (UInt256.shiftRight exponent (UInt256.ofNat shift.val))).toNat = 32 * index)
    (hcap : tail.length + 4 < 1024) :
    runInstructions (program slot hslot shift)
      (framed template pc base modulus (accumulator :: modulus :: tail)) =
    some (framed template (advancePC 8 pc) base modulus
      (UInt256.mulMod (WindowMath.tableWord base modulus index)
        accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hread := WindowTableMemory.readWord_tableMemory base modulus index hindex
  have hactive := WindowTableMemory.activeWordsAfter_lookup index hindex
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, program, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap, hcap2, hcap3, List.getElem?_cons_succ,
      hexponent, hmask, haddress, hread, hactive, State.activeWordsAfterUInt256,
      advancePC, succ_eq_add, hpush, word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLookup
