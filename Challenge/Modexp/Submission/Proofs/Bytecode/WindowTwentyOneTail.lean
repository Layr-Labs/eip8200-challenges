import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def updateProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .push 1 84, .op .SHL,
   .op (.Swap ⟨1, by decide⟩), .push 1 1,
   .op (.Dup ⟨5, by decide⟩), .op .SUB, .op (.Swap ⟨4, by decide⟩)]

def jumpProgram (target : UInt256) : List Instr :=
  [.push 2 target, .op .JUMPI]

def program (target : UInt256) : List Instr := updateProgram ++ jumpProgram target

/-- The old counter is retained above the new five-slot frame for JUMPI. -/
def updated (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneLookup.framed template pc base modulus
    ([counter, accumulator, modulus,
      UInt256.shiftLeft exponent (UInt256.ofNat 84), UInt256.ofNat 480,
      counter - UInt256.ofNat 1] ++ rest)

theorem run_head (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (WindowTwentyOneGroup.state template pc base modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.state template pc.succ base modulus accumulator exponent counter 0 rest) := by
  have hcap : rest.length + 5 < 1024 := by omega
  simp [runInstructions, WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, Nat.add_assoc]

theorem run_update (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions updateProgram
      (WindowTwentyOneGroup.state template pc base modulus accumulator exponent counter 0 rest) =
    some (updated template (advancePC 10 pc) base modulus accumulator exponent counter rest) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, updateProgram, updated, WindowTwentyOneGroup.state,
    WindowTwentyOneLookup.framed, Challenge.EvmProof.Stepper.runInstr,
    hcap5, hcap6, hcap7, Nat.add_assoc, List.exchange,
    advancePC, succ_eq_add, hpush, word_add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat]

theorem run_jump (template : State)
    (pc target base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (jumpProgram target)
      (updated template pc base modulus accumulator exponent counter rest) =
    some (WindowTwentyOneGroup.state template
      (if UInt256.isTrue counter then target else advancePC 4 pc)
      base modulus accumulator (UInt256.shiftLeft exponent (UInt256.ofNat 84))
      (counter - UInt256.ofNat 1) 0 rest) := by
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hpush : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  by_cases hc : UInt256.isTrue counter <;>
    simp [runInstructions, jumpProgram, updated, WindowTwentyOneGroup.state,
      WindowTwentyOneLookup.framed, Challenge.EvmProof.Stepper.runInstr,
      hcap6, hcap7, Nat.add_assoc, htarget, hc,
      advancePC, succ_eq_add, hpush, word_add_assoc]

theorem run_tail (template : State)
    (pc target base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (program target)
      (WindowTwentyOneGroup.state template pc base modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.state template
      (if UInt256.isTrue counter then target else advancePC 14 pc)
      base modulus accumulator (UInt256.shiftLeft exponent (UInt256.ofNat 84))
      (counter - UInt256.ofNat 1) 0 rest) := by
  have hu := run_update template pc base modulus accumulator exponent counter rest hrest
  have hj := run_jump template (advancePC 10 pc) target base modulus accumulator exponent
    counter rest hrest htarget
  have both := runInstructions_append_some _ _ _ _ _ hu hj
  simpa only [program, ← advancePC_add, show 10 + 4 = 14 by decide] using both

theorem shift_twentyOne (exponent : UInt256) (processed : Nat)
    (hprocessed : processed + 21 < 64) :
    UInt256.shiftLeft (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed)))
        (UInt256.ofNat 84) =
      UInt256.shiftLeft exponent (UInt256.ofNat (4 * (processed + 21))) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [WindowTwentyOneBits.shiftLeft_toNat_mod _ 84 (by decide),
    WindowTwentyOneBits.shiftLeft_toNat_mod _ (4 * processed) (by omega),
    WindowTwentyOneBits.shiftLeft_toNat_mod _ (4 * (processed + 21)) (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add]
  congr 3

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTail
