import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowCopyMemory

set_option warningAsError true

/-!
Artifact-independent lookup for every staged digit.  The table index is read from the
exponent copies the trampoline stored above the table (`WindowCopyMemory`): an
unaligned `MLOAD` at the digit's copy address, masked with the frame's `480`.
Concrete bytecode bindings are supplied separately.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLookup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program (slot : Nat) (hslot : slot ≤ 11) (laddr : Nat) : List Instr :=
  [.push 2 (UInt256.ofNat laddr), .op .MLOAD,
   .op (.Dup ⟨slot + 4, by omega⟩), .op .AND,
   .op .MLOAD, .op .MULMOD]

/-- The loop frame: memory and active-word count are explicit (table only before the
first trampoline pass, table plus exponent copies afterwards). -/
def framed (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (stack : List UInt256) : State :=
  { template with
    pc := pc
    stack := stack
    memory := mem
    activeWords := UInt256.ofNat active }

theorem activeWordsAfter_table (index : Nat) (hindex : index < 16) :
    MachineState.activeWordsAfter 19 (32 * index) 32 = 19 := by
  simp [MachineState.activeWordsAfter]
  omega

/-- Consume the first staged modulus; the remaining tail is exactly preserved.
For the three positions in a group, `slot` is 11, 6 or 1 respectively. -/
theorem run_lookup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator : UInt256)
    (tail : List UInt256) (slot : Nat) (hslot : slot ≤ 11) (laddr : Nat)
    (hladdr : laddr + 32 ≤ 608)
    (index : Nat) (hindex : index < 16)
    (hmask : tail[slot + 1]? = some (UInt256.ofNat 480))
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat = 32 * index)
    (hcap : tail.length + 4 < 1024) :
    runInstructions (program slot hslot laddr)
      (framed template pc mem 19 (accumulator :: modulus :: tail)) =
    some (framed template (advancePC 8 pc) mem 19
      (UInt256.mulMod (WindowMath.tableWord base modulus index)
        accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hl : (UInt256.ofNat laddr).toNat = laddr := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h19 : (UInt256.ofNat 19).toNat = 19 := rfl
  have hactive := activeWordsAfter_table index hindex
  have hactive' := WindowCopyMemory.activeWordsAfter_nineteen laddr hladdr
  have hpush3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, program, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap, hcap2, hcap3, List.getElem?_cons_succ, hl, h19,
      hmask, haddress, hread, hactive, hactive', State.activeWordsAfterUInt256,
      advancePC, succ_eq_add, hpush3, word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLookup
