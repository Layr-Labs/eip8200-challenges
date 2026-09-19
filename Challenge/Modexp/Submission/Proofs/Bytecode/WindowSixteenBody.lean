import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenLast

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def programLast (off : Nat) : List Instr :=
  WindowSixteenBlock.Block.program80Prefix off ++
    WindowSixteenLast.program (WindowCopyMemory.laddr (off + 12))
      (WindowCopyMemory.laddr (off + 13))

theorem run_last (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (programLast 48)
      (WindowTwentyOneGroup.state template pc
        (WindowSixteenBlock.Block.blockMemory mem exponent) 18 modulus accumulator
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneLastGroup.outState template (advancePC 327 pc)
      (WindowSixteenBlock.Block.blockMemory mem exponent) 18
      (WindowTwentyOneMath.advance base modulus exponent.toNat 49 15 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := WindowSixteenBlock.Block.blockMemory mem exponent
  let a12 := WindowTwentyOneMath.advance base modulus exponent.toNat 49 12 accumulator
  have hp := WindowSixteenBlock.Block.run_program80Prefix template pc mem
    base modulus exponent accumulator counter 48 (by decide) htable rest hrest
  have ht (i : Nat) (hi : i < 16) :=
    WindowSixteenBlock.Block.block_table mem exponent base modulus i hi htable
  have ha0 := WindowSixteenBlock.Block.block_address mem exponent 48 12 (by decide)
  have ha1 := WindowSixteenBlock.Block.block_address mem exponent 48 13 (by decide)
  have ha2 :
      (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft shifted 4)).toNat =
        32 * WindowTwentyOneMath.nibble exponent.toNat 63 := by
    dsimp only [shifted]
    rw [WindowTwentyOneBits.shifted_lookupAddressLast, WindowTwentyOneMath.nibble]
    norm_num
  have tailRun := WindowSixteenLast.run_tail template (advancePC 276 pc) cm
    base modulus a12 shifted counter
    (WindowCopyMemory.laddr 60) (WindowCopyMemory.laddr 61)
    (WindowSixteenBlock.Block.laddr_bound 60 (by decide))
    (WindowSixteenBlock.Block.laddr_bound 61 (by decide)) ht
    (WindowTwentyOneMath.nibble exponent.toNat 61)
    (WindowTwentyOneMath.nibble exponent.toNat 62)
    (WindowTwentyOneMath.nibble exponent.toNat 63)
    (WindowTwentyOneMath.nibble_lt _ _) (WindowTwentyOneMath.nibble_lt _ _)
    (WindowTwentyOneMath.nibble_lt _ _) ha0 ha1 ha2 rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hp tailRun
  have ha : WindowTwentyOneGroup.accumulatorAfter base modulus a12
      (WindowTwentyOneMath.nibble exponent.toNat 61)
      (WindowTwentyOneMath.nibble exponent.toNat 62)
      (WindowTwentyOneMath.nibble exponent.toNat 63) =
    WindowTwentyOneMath.advance base modulus exponent.toNat 49 15 accumulator := by
    rfl
  simpa only [programLast, cm, shifted, ha, ← advancePC_add,
    show 276 + 51 = 327 by decide] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBody
