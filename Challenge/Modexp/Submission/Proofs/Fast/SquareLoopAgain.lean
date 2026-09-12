import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# `again` (4737): the next square's row-0 state

The loop's staging block, in two halves so that neither elaboration is large:

* `againStageProgram` (13 instructions, pc 4755 -> 4777) re-stages the operand
  (`MCOPY 0x800 -> 0x2300`) and re-zeroes the accumulator block
  (`CALLDATACOPY` from the end of calldata at 0x2000), producing exactly the memory
  `Cios2Dispatch.gasSteps_commonSetupInput` produces, `mpZeroed s (stage mem 2048 n) n`;
* `againFixProgram` (9 instructions, pc 4777 -> falls into `sq_row` 4788) resets the
  frame's pointer, entry and previous-limb slots.

The two are composed with `runInstructions_append_some`, mirroring the crown's own
`run_zero` / `run_pointersJump` split of the setup block.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-- `PUSH0` pushes the raw zero word. -/
private theorem push0_eq : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide

/-! ## `again`: the next square's row-0 state -/

private theorem ptr_wrap (base n : Nat) :
    UInt256.ofNat (ptrAt base n) + UInt256.ofNat (32 * n) = UInt256.ofNat base := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hpow : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  have h : ptrAt base n + 32 * n = base + 2 ^ 256 * n := by
    simp only [ptrAt, hpow]; omega
  rw [h, Nat.add_mul_mod_self_left]

/-- The retained reduction-chain entry lies 299 bytes past the first product-chain entry
for both admitted widths, so the next square's entry is read back from it. -/
private theorem l2_back (n : Nat) (hn : n = 4 ∨ n = 8) :
    l2Target n - UInt256.ofNat 299 = UInt256.ofNat (sqEnt n 0) := by
  rcases hn with rfl | rfl <;> decide

/-! ## The two halves of `again` -/

/-- The staging half: `MCOPY` the operand and `CALLDATACOPY`-zero the accumulator. -/
def againStageProgram : List Instr := againProgram.take 13

/-- The frame-fixing half: reset the pointer, entry and previous-limb slots. -/
def againFixProgram : List Instr := againProgram.drop 13

/-- Between the two halves (pc 4777): the width word sits above the untouched frame and
the memory is already the next square's input. -/
def againMidState (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4912
           stack := UInt256.ofNat (32 * n) ::
             frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mpZeroed s (StagedOperand.stage mem 2048 n) n }

/-- The staging half (13 instructions): the memory becomes the next square's input and the
width word is left on top of the frame. -/
theorem run_againStage (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    runInstructions againStageProgram
      (frameAt pcAgain s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (againMidState s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hn8 : n ≤ 8 := by omega
  have hnpos : 0 < n := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt (by
    have : (2 : Nat) ^ 256 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num
    omega)
  have hactS := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC := activeWords_fix s 8192 (64 + 32 * n) (by omega) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat 8960 (32 * n) (by omega) (by omega) hact
  have hactA := activeWordsAfter_fix s.activeWords.toNat 2048 (32 * n) (by omega) (by omega) hact
  have hactN : s.activeWords.toNat %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.activeWords.toNat := Nat.mod_eq_of_lt s.activeWords.val.isLt
  have hszN : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n := Nat.mod_eq_of_lt (by omega)
  have hsizeN : (64 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h8960 : (8960 : UInt256).toNat = 8960 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h2048 : (2048 : UInt256).toNat = 2048 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have hsum : UInt256.ofNat (32 * n) + UInt256.ofNat 64 = UInt256.ofNat (64 + 32 * n) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    exact congrArg UInt256.ofNat (by omega)
  simp (config := { maxSteps := 200000 })
    [againStageProgram, againProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      frameAt, frameStack, pcAgain, againMidState, StagedOperand.stage, mpZeroed, hs32,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      hactS, hactC, hactD, hactA, hactN, h9344, h8960, h8192, h2048, h64,
      hcdsN, hszN, hsizeN, hsum, hc16', hc17, hc18, hc19, hc20, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The frame-fixing half (9 instructions): the pointer slot goes back to
`2048 + 32 * n - 32`, the entry slot back to `sqEnt n 0`, and slot 14 is cleared. -/
theorem run_againFix (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hn : n = 4 ∨ n = 8)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4923 = true) :
    runInstructions againFixProgram
      (againMidState s mem n (UInt256.ofNat (ptrAt (2048 + 32 * n - 32) n))
        (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (outState s (mpZeroed s (StagedOperand.stage mem 2048 n) n) 2048 n 0
      (UInt256.ofNat 4923) (UInt256.ofNat (sqEnt n 0)) inv m0
      (tl :: m96 :: m64 :: m32 :: UInt256.ofNat 0 :: pdst :: ret :: rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hptr := ptr_wrap (2048 + 32 * n - 32) n
  have hl2 := l2_back n hn
  have hptr' : UInt256.ofNat (32 * n + ptrAt (2048 + 32 * n - 32) n) =
      UInt256.ofNat (2048 + 32 * n - 32) := by
    rw [Nat.add_comm (32 * n) (ptrAt (2048 + 32 * n - 32) n),
      ← Challenge.EvmProof.Word.ofNat_add_mod]
    exact hptr
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4923 = true := by
    rw [hcode]; exact hhd
  simp (config := { maxSteps := 200000 })
    [againFixProgram, againProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      againMidState, frameStack, outState, hptr, hptr', hl2, hjd, ptrAt_zero, push0_eq,
      hc16', hc17, hc18, hc19, hc20, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- `again` (4737): the loop's next row-0 state, with the operand re-staged, the
accumulator re-zeroed, the pointer and entry slots reset and slot 14 cleared. -/
theorem run_again (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4923 = true) :
    runInstructions againProgram
      (frameAt pcAgain s mem n (UInt256.ofNat (ptrAt (2048 + 32 * n - 32) n))
        (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (outState s (mpZeroed s (StagedOperand.stage mem 2048 n) n) 2048 n 0
      (UInt256.ofNat 4923) (UInt256.ofNat (sqEnt n 0)) inv m0
      (tl :: m96 :: m64 :: m32 :: UInt256.ofNat 0 :: pdst :: ret :: rest)) := by
  change runInstructions (againStageProgram ++ againFixProgram) _ = _
  exact runInstructions_append_some _ _ _ _ _
    (run_againStage s mem n (UInt256.ofNat (ptrAt (2048 + 32 * n - 32) n))
      (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hact hn hcds
      hs32)
    (run_againFix s mem n tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hn hhd)

/-- `again`: the next square's row-0 head. -/
def gasSteps_again (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4923 = true) :
    Challenge.EvmProof.GasSteps
      (frameAt pcAgain s mem n (UInt256.ofNat (ptrAt (2048 + 32 * n - 32) n))
        (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (outState s (mpZeroed s (StagedOperand.stage mem 2048 n) n) 2048 n 0
        (UInt256.ofNat 4923) (UInt256.ofNat (sqEnt n 0)) inv m0
        (tl :: m96 :: m64 :: m32 :: UInt256.ofNat 0 :: pdst :: ret :: rest)) :=
  againBlock.steps
    (environment (frameAt pcAgain s mem n (UInt256.ofNat (ptrAt (2048 + 32 * n - 32) n))
      (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_again s mem n tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hact hn hcds hs32 hhd)

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
