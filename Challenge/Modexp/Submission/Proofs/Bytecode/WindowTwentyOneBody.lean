import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowCopyMemory
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- The 443-byte straight-line body after the trampoline: the first group resumes after
the trampoline's `stageHead`; each lookup reads its digit from the exponent copies. -/
def program : List Instr :=
  WindowTwentyOneGroup.restProgram (WindowCopyMemory.laddr 0) (WindowCopyMemory.laddr 1) (WindowCopyMemory.laddr 2) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr 3) (WindowCopyMemory.laddr 4) (WindowCopyMemory.laddr 5) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr 6) (WindowCopyMemory.laddr 7) (WindowCopyMemory.laddr 8) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr 9) (WindowCopyMemory.laddr 10) (WindowCopyMemory.laddr 11) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr 12) (WindowCopyMemory.laddr 13) (WindowCopyMemory.laddr 14) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr 15) (WindowCopyMemory.laddr 16) (WindowCopyMemory.laddr 17) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr 18) (WindowCopyMemory.laddr 19) (WindowCopyMemory.laddr 20)

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

private theorem laddr_bound (i : Nat) (hi : i < 21) : WindowCopyMemory.laddr i + 32 ≤ 608 := by
  unfold WindowCopyMemory.laddr
  split <;> omega

private theorem address_at (mem : ByteArray) (exponent : UInt256) (processed index : Nat)
    (hindex : index < 21) (hinside : processed + index < 64) :
    WindowTwentyOneGroup.address
      (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))))
      (WindowCopyMemory.laddr index) =
    32 * WindowTwentyOneMath.nibble exponent.toNat (processed + index) := by
  unfold WindowTwentyOneGroup.address
  rw [WindowCopyMemory.land480_laddr _ _ _ hindex, land_comm]
  exact WindowTwentyOneBits.shifted_lookupAddress exponent processed index hindex hinside

/-- The exact body for every eligible exponent position, from the trampoline's return
(`headState`) to the loop tail.  The shifted exponent and counter are preserved. -/
theorem run_twentyOne (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (processed : Nat) (hprocessed : processed + 21 ≤ 64)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program
      (WindowTwentyOneGroup.headState template pc
        (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed)))) 19
        modulus accumulator
        (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))) counter rest) =
    some (WindowTwentyOneGroup.state template (advancePC 443 pc)
      (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed)))) 19
      modulus
      (WindowTwentyOneMath.advance base modulus exponent.toNat processed 21 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))
  let cm := WindowCopyMemory.copyMem mem shifted
  let digit := fun index => WindowTwentyOneMath.nibble exponent.toNat (processed + index)
  let a1 := WindowTwentyOneGroup.accumulatorAfter base modulus accumulator (digit 0) (digit 1) (digit 2)
  let a2 := WindowTwentyOneGroup.accumulatorAfter base modulus a1 (digit 3) (digit 4) (digit 5)
  let a3 := WindowTwentyOneGroup.accumulatorAfter base modulus a2 (digit 6) (digit 7) (digit 8)
  let a4 := WindowTwentyOneGroup.accumulatorAfter base modulus a3 (digit 9) (digit 10) (digit 11)
  let a5 := WindowTwentyOneGroup.accumulatorAfter base modulus a4 (digit 12) (digit 13) (digit 14)
  let a6 := WindowTwentyOneGroup.accumulatorAfter base modulus a5 (digit 15) (digit 16) (digit 17)
  have hi (index : Nat) : digit index < 16 := WindowTwentyOneMath.nibble_lt _ _
  have ht : ∀ i, i < 16 → MachineState.readWord cm (32 * i) = WindowMath.tableWord base modulus i := by
    intro i hi16
    rw [WindowCopyMemory.readWord_copyMem_low _ _ _ (by omega)]
    exact htable i hi16
  have ha (index : Nat) (hindex : index < 21) :
      WindowTwentyOneGroup.address cm (WindowCopyMemory.laddr index) = 32 * digit index :=
    address_at mem exponent processed index hindex (by omega)
  have hb (index : Nat) (hindex : index < 21) := laddr_bound index hindex
  have h0 := WindowTwentyOneGroup.run_restGroup template pc cm
    base modulus accumulator shifted counter
    (WindowCopyMemory.laddr 0) (WindowCopyMemory.laddr 1) (WindowCopyMemory.laddr 2) (hb 0 (by decide)) (hb 1 (by decide)) (hb 2 (by decide)) ht
    (digit 0) (digit 1) (digit 2) (hi 0) (hi 1) (hi 2)
    (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) rest hrest
  have h1 := WindowTwentyOneGroup.run_group template (advancePC 59 pc) cm
    base modulus a1 shifted counter
    (WindowCopyMemory.laddr 3) (WindowCopyMemory.laddr 4) (WindowCopyMemory.laddr 5) (hb 3 (by decide)) (hb 4 (by decide)) (hb 5 (by decide)) ht
    (digit 3) (digit 4) (digit 5) (hi 3) (hi 4) (hi 5)
    (ha 3 (by decide)) (ha 4 (by decide)) (ha 5 (by decide)) rest hrest
  have h2 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 59 pc)) cm
    base modulus a2 shifted counter
    (WindowCopyMemory.laddr 6) (WindowCopyMemory.laddr 7) (WindowCopyMemory.laddr 8) (hb 6 (by decide)) (hb 7 (by decide)) (hb 8 (by decide)) ht
    (digit 6) (digit 7) (digit 8) (hi 6) (hi 7) (hi 8)
    (ha 6 (by decide)) (ha 7 (by decide)) (ha 8 (by decide)) rest hrest
  have h3 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 59 pc))) cm
    base modulus a3 shifted counter
    (WindowCopyMemory.laddr 9) (WindowCopyMemory.laddr 10) (WindowCopyMemory.laddr 11) (hb 9 (by decide)) (hb 10 (by decide)) (hb 11 (by decide)) ht
    (digit 9) (digit 10) (digit 11) (hi 9) (hi 10) (hi 11)
    (ha 9 (by decide)) (ha 10 (by decide)) (ha 11 (by decide)) rest hrest
  have h4 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc)))) cm
    base modulus a4 shifted counter
    (WindowCopyMemory.laddr 12) (WindowCopyMemory.laddr 13) (WindowCopyMemory.laddr 14) (hb 12 (by decide)) (hb 13 (by decide)) (hb 14 (by decide)) ht
    (digit 12) (digit 13) (digit 14) (hi 12) (hi 13) (hi 14)
    (ha 12 (by decide)) (ha 13 (by decide)) (ha 14 (by decide)) rest hrest
  have h5 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc))))) cm
    base modulus a5 shifted counter
    (WindowCopyMemory.laddr 15) (WindowCopyMemory.laddr 16) (WindowCopyMemory.laddr 17) (hb 15 (by decide)) (hb 16 (by decide)) (hb 17 (by decide)) ht
    (digit 15) (digit 16) (digit 17) (hi 15) (hi 16) (hi 17)
    (ha 15 (by decide)) (ha 16 (by decide)) (ha 17 (by decide)) rest hrest
  have h6 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc)))))) cm
    base modulus a6 shifted counter
    (WindowCopyMemory.laddr 18) (WindowCopyMemory.laddr 19) (WindowCopyMemory.laddr 20) (hb 18 (by decide)) (hb 19 (by decide)) (hb 20 (by decide)) ht
    (digit 18) (digit 19) (digit 20) (hi 18) (hi 19) (hi 20)
    (ha 18 (by decide)) (ha 19 (by decide)) (ha 20 (by decide)) rest hrest
  have hall1 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall2 := runInstructions_append_some _ _ _ _ _ hall1 h2
  have hall3 := runInstructions_append_some _ _ _ _ _ hall2 h3
  have hall4 := runInstructions_append_some _ _ _ _ _ hall3 h4
  have hall5 := runInstructions_append_some _ _ _ _ _ hall4 h5
  have hall6 := runInstructions_append_some _ _ _ _ _ hall5 h6
  simpa only [program, shifted, cm, a1, a2, a3, a4, a5, a6, digit, WindowTwentyOneGroup.accumulatorAfter,
    WindowTwentyOneMath.advance, Nat.add_zero, ← advancePC_add,
    show 59 + 64 + 64 + 64 + 64 + 64 + 64 = 443 by decide] using hall6

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody
