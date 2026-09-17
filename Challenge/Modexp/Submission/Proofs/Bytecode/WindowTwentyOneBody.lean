import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowCopyMemory
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- The 443-byte straight-line body of one pass: twenty-one nibbles read from ONE stored
exponent pair at offsets `off .. off+20`.  The pass index no longer shifts the exponent --
`WindowCopyMemory.laddr` reaches all sixty-two addressed digits from a single store. -/
def program (off : Nat) : List Instr :=
  WindowTwentyOneGroup.restProgram (WindowCopyMemory.laddr (off + 0)) (WindowCopyMemory.laddr (off + 1)) (WindowCopyMemory.laddr (off + 2)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 3)) (WindowCopyMemory.laddr (off + 4)) (WindowCopyMemory.laddr (off + 5)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 6)) (WindowCopyMemory.laddr (off + 7)) (WindowCopyMemory.laddr (off + 8)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 9)) (WindowCopyMemory.laddr (off + 10)) (WindowCopyMemory.laddr (off + 11)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 12)) (WindowCopyMemory.laddr (off + 13)) (WindowCopyMemory.laddr (off + 14)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 15)) (WindowCopyMemory.laddr (off + 16)) (WindowCopyMemory.laddr (off + 17)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 18)) (WindowCopyMemory.laddr (off + 19)) (WindowCopyMemory.laddr (off + 20))

/-- The final pass: digits 42..62 of the ladder.  Digit 62 is nibble 0 of the exponent, the
one digit no address reaches, so the last group is `WindowTwentyOneGroup.programLast`. -/
def programLastPass (off : Nat) : List Instr :=
  WindowTwentyOneGroup.restProgram (WindowCopyMemory.laddr (off + 0)) (WindowCopyMemory.laddr (off + 1)) (WindowCopyMemory.laddr (off + 2)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 3)) (WindowCopyMemory.laddr (off + 4)) (WindowCopyMemory.laddr (off + 5)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 6)) (WindowCopyMemory.laddr (off + 7)) (WindowCopyMemory.laddr (off + 8)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 9)) (WindowCopyMemory.laddr (off + 10)) (WindowCopyMemory.laddr (off + 11)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 12)) (WindowCopyMemory.laddr (off + 13)) (WindowCopyMemory.laddr (off + 14)) ++
    WindowTwentyOneGroup.program (WindowCopyMemory.laddr (off + 15)) (WindowCopyMemory.laddr (off + 16)) (WindowCopyMemory.laddr (off + 17)) ++
    WindowTwentyOneGroup.programLast (WindowCopyMemory.laddr (off + 18)) (WindowCopyMemory.laddr (off + 19))

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

private theorem laddr_bound (i : Nat) (hi : i < 62) : WindowCopyMemory.laddr i + 32 ≤ 576 := by
  unfold WindowCopyMemory.laddr
  split <;> omega

private theorem address_at (mem : ByteArray) (exponent : UInt256) (index : Nat)
    (hindex : index < 62) :
    WindowTwentyOneGroup.address
      (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat 1)))
      (WindowCopyMemory.laddr index) =
    32 * WindowTwentyOneMath.nibble exponent.toNat (1 + index) := by
  unfold WindowTwentyOneGroup.address
  rw [WindowCopyMemory.land480_laddr _ _ _ hindex, land_comm]
  exact WindowTwentyOneBits.shifted_lookupAddress exponent 1 index (by omega) hindex (by omega)

private theorem address_at_last (exponent : UInt256) :
    (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft (UInt256.shiftLeft exponent (UInt256.ofNat 1)) 4)).toNat =
    32 * WindowTwentyOneMath.nibble exponent.toNat 63 := by
  rw [WindowTwentyOneBits.shifted_lookupAddressLast, WindowTwentyOneMath.nibble]
  norm_num

/-- One pass of twenty-one addressed digits, all from a SINGLE stored exponent pair. -/
theorem run_twentyOne (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (off : Nat) (hoff : off + 21 ≤ 62)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (program off)
      (WindowTwentyOneGroup.headState template pc
        (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat 1))) 18
        modulus accumulator
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter rest) =
    some (WindowTwentyOneGroup.state template (advancePC 443 pc)
      (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat 1))) 18
      modulus
      (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 21 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := WindowCopyMemory.copyMem mem shifted
  let digit := fun index => WindowTwentyOneMath.nibble exponent.toNat (1 + off + index)
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
  have ha (index : Nat) (hindex : off + index < 62) :
      WindowTwentyOneGroup.address cm (WindowCopyMemory.laddr (off + index)) = 32 * digit index := by
    have h := address_at mem exponent (off + index) hindex
    rw [show 1 + (off + index) = 1 + off + index from (Nat.add_assoc 1 off index).symm] at h
    exact h
  have hb (index : Nat) (hindex : off + index < 62) := laddr_bound (off + index) hindex
  have h0 := WindowTwentyOneGroup.run_restGroup template pc cm base modulus accumulator shifted counter
    (WindowCopyMemory.laddr (off + 0)) (WindowCopyMemory.laddr (off + 1)) (WindowCopyMemory.laddr (off + 2))
    (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega)) ht
    (digit 0) (digit 1) (digit 2) (hi 0) (hi 1) (hi 2)
    (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega)) rest hrest
  have h1 := WindowTwentyOneGroup.run_group template (advancePC 59 pc) cm base modulus a1 shifted counter
    (WindowCopyMemory.laddr (off + 3)) (WindowCopyMemory.laddr (off + 4)) (WindowCopyMemory.laddr (off + 5))
    (hb 3 (by omega)) (hb 4 (by omega)) (hb 5 (by omega)) ht
    (digit 3) (digit 4) (digit 5) (hi 3) (hi 4) (hi 5)
    (ha 3 (by omega)) (ha 4 (by omega)) (ha 5 (by omega)) rest hrest
  have h2 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 59 pc)) cm base modulus a2 shifted counter
    (WindowCopyMemory.laddr (off + 6)) (WindowCopyMemory.laddr (off + 7)) (WindowCopyMemory.laddr (off + 8))
    (hb 6 (by omega)) (hb 7 (by omega)) (hb 8 (by omega)) ht
    (digit 6) (digit 7) (digit 8) (hi 6) (hi 7) (hi 8)
    (ha 6 (by omega)) (ha 7 (by omega)) (ha 8 (by omega)) rest hrest
  have h3 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 59 pc))) cm base modulus a3 shifted counter
    (WindowCopyMemory.laddr (off + 9)) (WindowCopyMemory.laddr (off + 10)) (WindowCopyMemory.laddr (off + 11))
    (hb 9 (by omega)) (hb 10 (by omega)) (hb 11 (by omega)) ht
    (digit 9) (digit 10) (digit 11) (hi 9) (hi 10) (hi 11)
    (ha 9 (by omega)) (ha 10 (by omega)) (ha 11 (by omega)) rest hrest
  have h4 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc)))) cm base modulus a4 shifted counter
    (WindowCopyMemory.laddr (off + 12)) (WindowCopyMemory.laddr (off + 13)) (WindowCopyMemory.laddr (off + 14))
    (hb 12 (by omega)) (hb 13 (by omega)) (hb 14 (by omega)) ht
    (digit 12) (digit 13) (digit 14) (hi 12) (hi 13) (hi 14)
    (ha 12 (by omega)) (ha 13 (by omega)) (ha 14 (by omega)) rest hrest
  have h5 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc))))) cm base modulus a5 shifted counter
    (WindowCopyMemory.laddr (off + 15)) (WindowCopyMemory.laddr (off + 16)) (WindowCopyMemory.laddr (off + 17))
    (hb 15 (by omega)) (hb 16 (by omega)) (hb 17 (by omega)) ht
    (digit 15) (digit 16) (digit 17) (hi 15) (hi 16) (hi 17)
    (ha 15 (by omega)) (ha 16 (by omega)) (ha 17 (by omega)) rest hrest
  have h6 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc)))))) cm base modulus a6 shifted counter
    (WindowCopyMemory.laddr (off + 18)) (WindowCopyMemory.laddr (off + 19)) (WindowCopyMemory.laddr (off + 20))
    (hb 18 (by omega)) (hb 19 (by omega)) (hb 20 (by omega)) ht
    (digit 18) (digit 19) (digit 20) (hi 18) (hi 19) (hi 20)
    (ha 18 (by omega)) (ha 19 (by omega)) (ha 20 (by omega)) rest hrest
  have hall1 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall2 := runInstructions_append_some _ _ _ _ _ hall1 h2
  have hall3 := runInstructions_append_some _ _ _ _ _ hall2 h3
  have hall4 := runInstructions_append_some _ _ _ _ _ hall3 h4
  have hall5 := runInstructions_append_some _ _ _ _ _ hall4 h5
  have hall6 := runInstructions_append_some _ _ _ _ _ hall5 h6
  simpa only [program, programLastPass, shifted, cm, a1, a2, a3, a4, a5, a6, digit,
    WindowTwentyOneGroup.accumulatorAfter, WindowTwentyOneMath.advance, Nat.add_zero,
    ← advancePC_add, show 59 + 64 + 64 + 64 + 64 + 64 + 64 = 443 by decide] using hall6

/-- The final pass.  Its last digit is nibble 0, read off the frame's shifted exponent. -/
theorem run_twentyOneLast (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (off : Nat) (hoff : off = 42)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (programLastPass off)
      (WindowTwentyOneGroup.headState template pc
        (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat 1))) 18
        modulus accumulator
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter rest) =
    some (WindowTwentyOneGroup.state template (advancePC 443 pc)
      (WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat 1))) 18
      modulus
      (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 21 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := WindowCopyMemory.copyMem mem shifted
  let digit := fun index => WindowTwentyOneMath.nibble exponent.toNat (1 + off + index)
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
  have ha (index : Nat) (hindex : off + index < 62) :
      WindowTwentyOneGroup.address cm (WindowCopyMemory.laddr (off + index)) = 32 * digit index := by
    have h := address_at mem exponent (off + index) hindex
    rw [show 1 + (off + index) = 1 + off + index from (Nat.add_assoc 1 off index).symm] at h
    exact h
  have hb (index : Nat) (hindex : off + index < 62) := laddr_bound (off + index) hindex
  have halast : (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft shifted 4)).toNat = 32 * digit 20 := by
    show (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft (UInt256.shiftLeft exponent (UInt256.ofNat 1)) 4)).toNat =
      32 * WindowTwentyOneMath.nibble exponent.toNat (1 + off + 20)
    rw [show 1 + off + 20 = 63 by omega]
    exact address_at_last exponent
  have h0 := WindowTwentyOneGroup.run_restGroup template pc cm base modulus accumulator shifted counter
    (WindowCopyMemory.laddr (off + 0)) (WindowCopyMemory.laddr (off + 1)) (WindowCopyMemory.laddr (off + 2))
    (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega)) ht
    (digit 0) (digit 1) (digit 2) (hi 0) (hi 1) (hi 2)
    (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega)) rest hrest
  have h1 := WindowTwentyOneGroup.run_group template (advancePC 59 pc) cm base modulus a1 shifted counter
    (WindowCopyMemory.laddr (off + 3)) (WindowCopyMemory.laddr (off + 4)) (WindowCopyMemory.laddr (off + 5))
    (hb 3 (by omega)) (hb 4 (by omega)) (hb 5 (by omega)) ht
    (digit 3) (digit 4) (digit 5) (hi 3) (hi 4) (hi 5)
    (ha 3 (by omega)) (ha 4 (by omega)) (ha 5 (by omega)) rest hrest
  have h2 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 59 pc)) cm base modulus a2 shifted counter
    (WindowCopyMemory.laddr (off + 6)) (WindowCopyMemory.laddr (off + 7)) (WindowCopyMemory.laddr (off + 8))
    (hb 6 (by omega)) (hb 7 (by omega)) (hb 8 (by omega)) ht
    (digit 6) (digit 7) (digit 8) (hi 6) (hi 7) (hi 8)
    (ha 6 (by omega)) (ha 7 (by omega)) (ha 8 (by omega)) rest hrest
  have h3 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 59 pc))) cm base modulus a3 shifted counter
    (WindowCopyMemory.laddr (off + 9)) (WindowCopyMemory.laddr (off + 10)) (WindowCopyMemory.laddr (off + 11))
    (hb 9 (by omega)) (hb 10 (by omega)) (hb 11 (by omega)) ht
    (digit 9) (digit 10) (digit 11) (hi 9) (hi 10) (hi 11)
    (ha 9 (by omega)) (ha 10 (by omega)) (ha 11 (by omega)) rest hrest
  have h4 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc)))) cm base modulus a4 shifted counter
    (WindowCopyMemory.laddr (off + 12)) (WindowCopyMemory.laddr (off + 13)) (WindowCopyMemory.laddr (off + 14))
    (hb 12 (by omega)) (hb 13 (by omega)) (hb 14 (by omega)) ht
    (digit 12) (digit 13) (digit 14) (hi 12) (hi 13) (hi 14)
    (ha 12 (by omega)) (ha 13 (by omega)) (ha 14 (by omega)) rest hrest
  have h5 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc))))) cm base modulus a5 shifted counter
    (WindowCopyMemory.laddr (off + 15)) (WindowCopyMemory.laddr (off + 16)) (WindowCopyMemory.laddr (off + 17))
    (hb 15 (by omega)) (hb 16 (by omega)) (hb 17 (by omega)) ht
    (digit 15) (digit 16) (digit 17) (hi 15) (hi 16) (hi 17)
    (ha 15 (by omega)) (ha 16 (by omega)) (ha 17 (by omega)) rest hrest
  have h6 := WindowTwentyOneGroup.run_groupLast template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 59 pc)))))) cm base modulus a6 shifted counter
    (WindowCopyMemory.laddr (off + 18)) (WindowCopyMemory.laddr (off + 19))
    (hb 18 (by omega)) (hb 19 (by omega)) ht
    (digit 18) (digit 19) (digit 20) (hi 18) (hi 19) (hi 20)
    (ha 18 (by omega)) (ha 19 (by omega)) halast rest hrest
  have hall1 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall2 := runInstructions_append_some _ _ _ _ _ hall1 h2
  have hall3 := runInstructions_append_some _ _ _ _ _ hall2 h3
  have hall4 := runInstructions_append_some _ _ _ _ _ hall3 h4
  have hall5 := runInstructions_append_some _ _ _ _ _ hall4 h5
  have hall6 := runInstructions_append_some _ _ _ _ _ hall5 h6
  simpa only [program, programLastPass, shifted, cm, a1, a2, a3, a4, a5, a6, digit,
    WindowTwentyOneGroup.accumulatorAfter, WindowTwentyOneMath.advance, Nat.add_zero,
    ← advancePC_add, show 59 + 64 + 64 + 64 + 64 + 64 + 64 = 443 by decide] using hall6

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody
