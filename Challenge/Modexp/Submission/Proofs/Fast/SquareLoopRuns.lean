import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
import Challenge.Modexp.Submission.Proofs.Fast.LazyCsubTrace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Run lemmas of the R0 squaring loop: `sq_exit`, `last`, `more`, and the exit

The four short blocks of the loop (`sq_exit` 4940, `last` 4957, `more` 2400) as
`runInstructions` lemmas and gas steps, plus the last square's exit (`nx` 4855, the 14
`POP`s and the jump to the CSUB guard) and the final conditional subtraction on an abstract
memory.  `again` (5016), the only memory-heavy block, lives in `SquareLoopAgain`; splitting
it off keeps every single file's elaboration small.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-! ## Run lemmas -/

/-- `allOnes + (c + 1) = c` for the counter range. -/
private theorem dec_succ (c : Nat) (hc : c ≤ 14) :
    allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := by
  interval_cases c <;> decide

/-- The `last` entry: the retained frame under the unused CSUB call pair `[pdst, again]`. -/
def lazyCsubState (s : State) (mem : ByteArray) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  LazyGate.atState s mem 4551 dst ret rest

def lastAt (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcLast
           stack := [UInt256.ofNat 2368, UInt256.ofNat pcH2] ++
             frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- The four-limb counter's fall-through: the `last` trampoline with the call pair on top. -/
def tailAt (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcTail
           stack := [UInt256.ofNat 2368, UInt256.ofNat pcH2] ++
             frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `e4` with the counter slot at `c + 1`: push the R4 return, leave `c` in the counter slot and
call the CSUB guard with `[2368, 4579]` on top of the frame.  Memory is unchanged. -/
theorem run_sqExit_more (s : State) (mem : ByteArray) (n c : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hc15 : c + 1 ≤ 15) :
    runInstructions e4Program
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat (c + 1)) ret rest) =
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 4610)
      (frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat c) ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := dec_succ c (by omega)
  have hcNat : (UInt256.ofNat (c + 1)).toNat = c + 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htrue : UInt256.isTrue (UInt256.ofNat (c + 1)) := by
    show (UInt256.ofNat (c + 1)).toNat ≠ 0
    rw [hcNat]; omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4551 = true := by
    rw [hcode]; exact jumpDestLazy
  simp [e4Program, TnM128SquareExit.e4Program, cProgram, TnM128SquareExit.cProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, frameAt, frameStack, pcSqExit, pcH2, lazyCsubState,
    LazyGate.atState, hdec, hcNat, htrue, hjd,
    hc16', hc17, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- `e4` with the counter slot at zero: push the R4 return, leave `allOnes` in the (dead)
counter slot and fall through to the `last` trampoline. -/
theorem run_sqExit_last (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) :
    runInstructions e4Program
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 0) ret rest) =
    some (tailAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev allOnes ret rest) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat 0 = allOnes := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
  simp [e4Program, TnM128SquareExit.e4Program, cProgram, TnM128SquareExit.cProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, frameAt, frameStack, tailAt, pcSqExit, pcTail, pcH2,
    hdec, hzero, hfalse,
    hc16', hc17, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The `last` trampoline: `PUSH2 4260 JUMP`. -/
theorem run_tail (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions e4TailProgram
      (tailAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lastAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4260 = true := by
    rw [hcode]; exact jumpDestLast
  have hl : (4260 : UInt256).toNat = 4260 := rfl
  simp [e4TailProgram, TnM128SquareExit.e4TailProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, tailAt, lastAt, frameStack, pcTail, pcLast, pcH2, hjd, hl,
    hc18, hc19,
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
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3487)
      (frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4551 = true := by
    rw [hcode]; exact jumpDestLazy
  simp [lastProgram, TnM128SquareExit.lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, lastAt, pcLast, lazyCsubState, LazyGate.atState, hjd, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The loop's blocks as gas steps -/

/-- `e4` with the counter slot above zero: straight into the CSUB guard. -/
def gasSteps_sqExitMore (s : State) (mem : ByteArray) (n c : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hc15 : c + 1 ≤ 15) :
    Challenge.EvmProof.GasSteps
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat (c + 1)) ret rest)
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 4610)
        (frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat c) ret rest)) :=
  e4Block.steps
    (environment (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev
      (UInt256.ofNat (c + 1)) ret rest) hcode hfork hrun hnp) rfl
    (run_sqExit_more s mem n c pbi ent tl inv m0 m96 m64 m32 aprev ret rest hcap hcode hc15)

/-- `e4` with the counter slot at zero, then the `last` trampoline. -/
def gasSteps_sqExitLast (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 0) ret rest)
      (lastAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev allOnes ret rest) :=
  (e4Block.steps
    (environment (frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 0)
      ret rest) hcode hfork hrun hnp) rfl
    (run_sqExit_last s mem n pbi ent tl inv m0 m96 m64 m32 aprev ret rest hcap)).trans
  (e4TailBlock.steps
    (environment (tailAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev allOnes ret rest)
      hcode hfork hrun hnp) rfl
    (run_tail s mem n pbi ent tl inv m0 m96 m64 m32 aprev allOnes ret rest hcap hcode))

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
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3487)
        (frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  lastBlock.steps
    (environment (lastAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_last s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode)

/-- The final conditional subtraction on an abstract memory: `[2048, ret]` above `tail`. -/
def gasSteps_lazyCsubAt (s : State) (X : ByteArray) (n dst : Nat) (ret : UInt256)
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
    (htn : (MachineState.readWord (Csub.csStep X n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps
      (lazyCsubState s X (UInt256.ofNat dst) ret tail)
      { s with pc := ret, stack := tail, memory := LazyCsub.resultMemory X n dst } := by
  have hdstNat : (UInt256.ofNat dst).toNat = dst := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have g := LazyCsub.gasSteps_csub_lazy s X n (UInt256.ofNat dst) ret tail
    hcap hcode hfork hrun hnp hact hn hn32 hjump hml htl hs32
    (by simpa only [hdstNat] using hdst) htn hfast
  simpa only [lazyCsubState, LazyGate.returnedState, hdstNat] using g

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
    (htn : (MachineState.readWord (Csub.csStep X n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps
      (mpCsubState s X (UInt256.ofNat dst) ret tail)
      { s with pc := ret, stack := tail, memory := Csub.csResultMemory X n dst } := by
  have g := Csub.gasSteps_csub s X n (UInt256.ofNat dst) ret tail hcap hcode hfork hrun hnp
    hact hn hn32 hjump hml htl hs32
    (by rw [show (UInt256.ofNat dst).toNat = dst from by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]; omega) htn hfast
  refine g.cast rfl ?_
  rw [show Csub.csReturnedState s X n n (UInt256.ofNat dst) ret tail =
      { s with pc := ret, stack := tail,
               memory := Csub.csResultMemory X n (UInt256.ofNat dst).toNat } from rfl,
    show (UInt256.ofNat dst).toNat = dst from by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
