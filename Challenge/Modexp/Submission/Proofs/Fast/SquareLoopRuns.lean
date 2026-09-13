import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Run lemmas of the R0 squaring loop: `sq_exit`, `last`, `more`, and the exit

The four short blocks of the loop (`sq_exit` 4908, `last` 4925, `more` 2400) as
`runInstructions` lemmas and gas steps, plus the last square's exit (`nx` 4851, the 14
`POP`s and the jump to the CSUB guard) and the final conditional subtraction on an abstract
memory.  `again` (4984), the only memory-heavy block, lives in `SquareLoopAgain`; splitting
it off keeps every single file's elaboration small.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-! ## Run lemmas -/

private theorem sub_one (c : Nat) (hc : c + 1 < 2 ^ 256) :
    UInt256.ofNat (c + 1) - UInt256.ofNat 1 = UInt256.ofNat c := by
  simpa using Challenge.EvmProof.Word.ofNat_sub_ofNat (a := c + 1) (b := 1) (by omega) hc

private theorem activeWords9280 (s : State) (hact : 88 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2624 32) =
      s.activeWords := by
  have hnat : MachineState.activeWordsAfter s.activeWords.toNat 2624 32 =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    simp only [show (32 : Nat) ≠ 0 by decide, if_false]
    exact Nat.max_eq_left (by omega)
  rw [hnat]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-- The `last` entry: the retained frame under the unused CSUB call pair `[pdst, again]`. -/
def lastAt (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcLast
           stack := [UInt256.ofNat 2368, UInt256.ofNat pcH2] ++
             frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `sq_exit` with a counter above one: store `c` and call the CSUB guard as a subroutine
with `[pdst, again]` on top of the retained frame. -/
theorem run_sqExit_more (s : State) (mem : ByteArray) (n c : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat (c + 1)) :
    runInstructions sqExitProgram
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (mpCsubState s (countMem mem c) (UInt256.ofNat 2368) (UInt256.ofNat 4392)
      (frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc15 : c ≤ 15 := by omega
  have hdec : allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := by
    interval_cases c <;> decide
  have hcNat : (UInt256.ofNat c).toNat = c := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htrue : UInt256.isTrue (UInt256.ofNat c) := by
    show (UInt256.ofNat c).toNat ≠ 0
    rw [hcNat]; omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4316 = true := by
    rw [hcode]; exact jumpDest4683
  have h9280 : (2624 : UInt256).toNat = 2624 := by decide
  simp [sqExitProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcSqExit, mpCsubState, countMem, hcount, hdec, hcNat, htrue, hjd, h9280,
    State.activeWordsAfterUInt256, activeWords9280 s hact,
    hc16', hc17, hc18, hc19, hc20, hc21, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- `sq_exit` with the counter at one: store zero and fall through to `last`. -/
theorem run_sqExit_last (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat 1) :
    runInstructions sqExitProgram
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lastAt s (countMem mem 0) n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have h9280 : (2624 : UInt256).toNat = 2624 := by decide
  have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
  simp [sqExitProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, lastAt, pcSqExit, pcLast, pcAgain, pcH2, countMem, hcount, hdec, hzero,
    hfalse, h9280,
    State.activeWordsAfterUInt256, activeWords9280 s hact,
    hc16', hc17, hc18, hc19, hc20, hc21, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- `last`: drop the unused call pair, then call the CSUB guard as a subroutine with
`[pdst, after]` on top of the retained frame. -/
theorem run_last (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions lastProgram
      (lastAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (mpCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3647)
      (frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4316 = true := by
    rw [hcode]; exact jumpDest4683
  simp [lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, lastAt, pcLast, mpCsubState, hjd, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The loop's blocks as gas steps -/

/-- `sq_exit` with a counter above one: straight into the CSUB guard. -/
def gasSteps_sqExitMore (s : State) (mem : ByteArray) (n c : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat (c + 1)) :
    Challenge.EvmProof.GasSteps
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (mpCsubState s (countMem mem c) (UInt256.ofNat 2368) (UInt256.ofNat 4392)
        (frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  sqExitBlock.steps
    (environment (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_sqExit_more s mem n c pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode
      hact hcpos hc16 hcount)

/-- `sq_exit` with the counter at one. -/
def gasSteps_sqExitLast (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lastAt s (countMem mem 0) n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) :=
  sqExitBlock.steps
    (environment (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_sqExit_last s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hact hcount)

/-- `last`: drop the call pair, rewrite the frame's `ret` slot to `after_sq` and jump to
`nx`. -/
def gasSteps_last (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (lastAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (mpCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3647)
        (frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  lastBlock.steps
    (environment (lastAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_last s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode)

/-- The last square's exit: the `nx` `JUMPDEST`, the 14 `POP`s and the jump to the CSUB
guard, on an abstract memory (so the defeq work happens once, off the deep memory terms). -/
def gasSteps_nxExit (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (frameAt pcNx s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (mpCsubState s mem pdst ret rest) :=
  (CarryRowGas.gasSteps_nxJd s mem pbi 2368 n (UInt256.ofNat 4427) ent inv m0
    (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp).trans
  (CarryRowBlocks.exitBlock.steps
    (CarryRowBlocks.environment (CiosCachedTailDefs.nxState s mem pbi 2368 n
      (UInt256.ofNat 4427) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosReadonly.run_exit { s with memory := mem } pbi (UInt256.ofNat 4427)
      (UInt256.ofNat (2368 - 32)) ent (l2Target n) tl inv m0 aprev m96 m64 m32 pdst ret rest
      hcap))

/-- The final conditional subtraction on an abstract memory: `[2048, ret]` above `tail`. -/
def gasSteps_csubAt (s : State) (X : ByteArray) (n dst : Nat) (ret : UInt256)
    (tail : List UInt256) (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8) (hdst : dst + 32 * n ≤ 2816)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hml : MachineState.readWord X 2752 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord X 2784 = UInt256.ofNat (2080 + 32 * n))
    (hs32 : MachineState.readWord (Csub.csStep X n n).memory 2688 = UInt256.ofNat (32 * n))
    (htn : (MachineState.readWord (Csub.csStep X n n).memory 2080).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps
      (mpCsubState s X (UInt256.ofNat dst) ret tail)
      { s with pc := ret, stack := tail, memory := Csub.csResultMemory X n dst } := by
  have g := Csub.gasSteps_csub s X n (UInt256.ofNat dst) ret tail hcap hcode hfork hrun hnp
    hact hn hn32 hjump hml htl hs32
    (by rw [show (UInt256.ofNat dst).toNat = dst from by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]; omega) htn
  refine g.cast rfl ?_
  rw [show Csub.csReturnedState s X n n (UInt256.ofNat dst) ret tail =
      { s with pc := ret, stack := tail,
               memory := Csub.csResultMemory X n (UInt256.ofNat dst).toNat } from rfl,
    show (UInt256.ofNat dst).toNat = dst from by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
