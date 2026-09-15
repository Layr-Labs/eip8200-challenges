import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# `again`: stage the next eight-limb square and enter its specialized first row

The first two instructions, at PCs 4214 and 4217, reload the width word.  The
remaining eight instructions reset the operand pointer and computed chain entry,
then jump to the row-zero entry at 5090.  The accumulator is no longer cleared
here: the new first row overwrites every word of `T` before reading it, so the
memory handed to it is the previous round's memory unchanged.  The previous-limb
slot is preserved: the new entry overwrites it with the first operand limb before
ordinary rows can observe it.
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

private theorem entry_from_reduction (n : Nat) (hn : n = 4 ∨ n = 8) :
    l2Target n - UInt256.ofNat 288 = UInt256.ofNat (sqEnt n 0) := by
  rcases hn with rfl | rfl <;> decide

/-! ## The two halves of `again` -/

/-- The staging half: reload the width word. -/
def againStageProgram : List Instr := againProgram.take 2

/-- Reset the pointer and chain entry, preserve the previous-limb slot, and branch. -/
def againFixProgram : List Instr := againProgram.drop 2

/-- Between the two halves (pc 4218): the width word sits above the untouched frame and
the memory is untouched. -/
def againMidState (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4222
           stack := UInt256.ofNat (32 * n) ::
             frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- The staging half (two instructions): the width word is left on top of the frame and
the memory is unchanged. -/
theorem run_againStage (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n)) :
    runInstructions againStageProgram
      (frameAt pcAgain s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (againMidState s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have _hcds := hcds
  have hn8 : n ≤ 8 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hactS := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactN : s.activeWords.toNat %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.activeWords.toNat := Nat.mod_eq_of_lt s.activeWords.val.isLt
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  simp (config := { maxSteps := 200000 })
    [againStageProgram, againProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      frameAt, frameStack, pcAgain, againMidState, hs32,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      hactS, hactN, h9344, hn8, hc16', hc17, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The frame-fixing half (eight instructions) resets the pointer and chain entry,
preserves slot 14, and branches to the specialized first row. -/
theorem run_againFix (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hn : n = 4 ∨ n = 8)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5091 = true) :
    runInstructions againFixProgram
      (againMidState s mem n (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n))
        (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some { outState s mem 2368 n 0
      (UInt256.ofNat 4234) (UInt256.ofNat (sqEnt n 0)) m64 m32 (m0 :: tl :: m96 :: negative32 :: inv :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 5091 } := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hptr : UInt256.ofNat (32 * n) +
      UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n) =
      UInt256.ofNat (2368 + 32 * n - 32) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact ptr_wrap (2368 + 32 * n - 32) n
  have hent := entry_from_reduction n hn
  have hjd : Decode.isValidJumpDest s.executionEnv.code 5091 = true := by
    rw [hcode]; exact hhd
  simp (config := { maxSteps := 200000 })
    [againFixProgram, againProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      againMidState, frameStack, outState, hptr, hent, hjd, ptrAt_zero, push0_eq,
      hc16', hc17, hc18, hc19, hc20, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The loop's next row-zero state: memory untouched (the first row overwrites `T`),
the pointer and entry slots reset, and the previous-limb slot preserved. -/
theorem run_again (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5091 = true) :
    runInstructions againProgram
      (frameAt pcAgain s mem n (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n))
        (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some { outState s mem 2368 n 0
      (UInt256.ofNat 4234) (UInt256.ofNat (sqEnt n 0)) m64 m32 (m0 :: tl :: m96 :: negative32 :: inv :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 5091 } := by
  change runInstructions (againStageProgram ++ againFixProgram) _ = _
  exact runInstructions_append_some _ _ _ _ _
    (run_againStage s mem n (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n))
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
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5091 = true) :
    Challenge.EvmProof.GasSteps
      (frameAt pcAgain s mem n (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n))
        (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest)
      { outState s mem 2368 n 0
        (UInt256.ofNat 4234) (UInt256.ofNat (sqEnt n 0)) m64 m32 (m0 :: tl :: m96 :: negative32 :: inv :: aprev :: pdst :: ret :: rest) with pc := UInt256.ofNat 5091 } :=
  againBlock.steps
    (environment (frameAt pcAgain s mem n (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) n))
      (UInt256.ofNat (sqEnt n n)) tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_again s mem n tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hact hn hcds hs32 hhd)

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
