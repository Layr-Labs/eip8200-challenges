import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatchWords

set_option warningAsError true

/-!
Literal dispatch traces for raw252f's L1 and L2 eight-copy suffixes.
Valid jump destinations remain explicit premises until the full Artifact binds.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNDispatchWords

def l1ValueProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .SUB, .push 1 5, .op .SHR, .push 1 7, .op .AND]

def l2ValueProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨1, by decide⟩), .push 2 8224,
   .op .SUB, .push 1 5, .op .SHR, .push 1 7, .op .AND]

def jumpProgram (stride base : Nat) : List Instr :=
  [.push 2 (UInt256.ofNat stride), .op .MUL,
   .push 2 (UInt256.ofNat base), .op .ADD, .op .JUMP]

def l1Program : List Instr := l1ValueProgram ++ jumpProgram 38 4089
def l2Program : List Instr := l2ValueProgram ++ jumpProgram 41 2098

theorem run_l1_value (template : State) (stack : List UInt256)
    (paj paEnd : UInt256) (hcap : stack.length + 2 < 1024)
    (hpa : stack[0]? = some paj) (hend : stack[5]? = some paEnd) :
    runInstructions l1ValueProgram (framed template (UInt256.ofNat 4070) stack) =
    some (framed template (UInt256.ofNat 4080)
      (UInt256.land (UInt256.ofNat 7)
        (UInt256.shiftRight (paEnd - paj) (UInt256.ofNat 5)) :: stack)) := by
  have hcap0 : stack.length < 1024 := by omega
  have hcap1 : stack.length + 1 < 1024 := by omega
  simp [runInstructions, l1ValueProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, hcap, hpa, hend, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l2_value (template : State) (stack : List UInt256)
    (ptj : UInt256) (hcap : stack.length + 2 < 1024)
    (hpt : stack[1]? = some ptj) :
    runInstructions l2ValueProgram (framed template (UInt256.ofNat 2077) stack) =
    some (framed template (UInt256.ofNat 2089)
      (UInt256.land (UInt256.ofNat 7)
        (UInt256.shiftRight (UInt256.ofNat 8224 - ptj) (UInt256.ofNat 5)) :: stack)) := by
  have hcap0 : stack.length < 1024 := by omega
  have hcap1 : stack.length + 1 < 1024 := by omega
  simp [runInstructions, l2ValueProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, hcap, hpt, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_jump (template : State) (pc : UInt256) (stack : List UInt256)
    (stride base slot : Nat) (hcap : stack.length + 2 < 1024)
    (htarget : Decode.isValidJumpDest template.executionEnv.code
      (UInt256.ofNat (base + stride * slot)).toNat = true) :
    runInstructions (jumpProgram stride base)
      (framed template pc (UInt256.ofNat slot :: stack)) =
    some (framed template (UInt256.ofNat (base + stride * slot)) stack) := by
  have hcap1 : stack.length + 1 < 1024 := by omega
  simp [runInstructions, jumpProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap1, hcap, ofNat_mul, Challenge.EvmProof.Word.ofNat_add_mod]
  exact htarget

theorem run_l1 (template : State) (stack : List UInt256)
    (paj paEnd : UInt256) (slot : Nat) (hcap : stack.length + 2 < 1024)
    (hpa : stack[0]? = some paj) (hend : stack[5]? = some paEnd)
    (hslot : UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight (paEnd - paj) (UInt256.ofNat 5)) = UInt256.ofNat slot)
    (htarget : Decode.isValidJumpDest template.executionEnv.code
      (UInt256.ofNat (l1PC slot)).toNat = true) :
    runInstructions l1Program (framed template (UInt256.ofNat 4070) stack) =
    some (framed template (UInt256.ofNat (l1PC slot)) stack) := by
  have hv := run_l1_value template stack paj paEnd hcap hpa hend
  rw [hslot] at hv
  exact runInstructions_append_some _ _ _ _ _ hv
    (run_jump template (UInt256.ofNat 4080) stack 38 4089 slot hcap htarget)

theorem run_l2 (template : State) (stack : List UInt256)
    (ptj : UInt256) (slot : Nat) (hcap : stack.length + 2 < 1024)
    (hpt : stack[1]? = some ptj)
    (hslot : UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight (UInt256.ofNat 8224 - ptj) (UInt256.ofNat 5)) = UInt256.ofNat slot)
    (htarget : Decode.isValidJumpDest template.executionEnv.code
      (UInt256.ofNat (l2PC slot)).toNat = true) :
    runInstructions l2Program (framed template (UInt256.ofNat 2077) stack) =
    some (framed template (UInt256.ofNat (l2PC slot)) stack) := by
  have hv := run_l2_value template stack ptj hcap hpt
  rw [hslot] at hv
  exact runInstructions_append_some _ _ _ _ _ hv
    (run_jump template (UInt256.ofNat 2089) stack 41 2098 slot hcap htarget)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatch
