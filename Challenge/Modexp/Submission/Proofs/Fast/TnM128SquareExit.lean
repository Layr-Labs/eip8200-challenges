import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

/-- Eight-limb kernel exit: carry reset, row pointer `+ 0x100`, `PUSH2 5062`, then falls into the
eight-limb counter `pcC` (no `JUMPDEST`). -/
def pcSqExit : Nat := 4222
/-- Eight-limb counter, reached only by fall-through from `pcSqExit`. -/
def pcC : Nat := 4233
/-- `last`, reached by fall-through from `pcC` (n = 8). -/
def pcLast : Nat := 4245
/-- `m4j`, the `JUMPDEST` inside `last` after its two `POP`s: the four-limb tail's exit. -/
def pcM4j : Nat := 4248
/-- Eight-limb CSUB return: the next square's row-0 head. -/
def pcH2 : Nat := 5125

def frameStack (tn m128 : UInt256) (_n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 4259, UInt256.ofNat 2336, ent, m32, allOnes,
   m128, m64, m0, tl, m96, inv, tn,
   aprev, pdst, ret] ++ rest

def frameAt (tn m128 : UInt256) (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat pc)
    (frameStack tn m128 n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)

/-- The square counter lives in the frame's `pdst` slot (dead during the square loop; pc 3471
overwrites it).  With `[r, frame]` on the stack the block reads `pdst` (`DUP16`), stores
`pdst - 1` back (`DUP8` is `allOnes`, `SWAP16`), and calls the CSUB guard with `[2368, r]`
when the old value is nonzero. -/
def cProgram : List Instr :=
  [.op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Swap ⟨15, by decide⟩), .push 2 2368, .op (.Swap ⟨0, by decide⟩),
   .push 2 4519, .op .JUMPI]

def sqExitProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op (.Swap ⟨12, by decide⟩), .op .POP,
   .push 2 256, .op .ADD, .push 2 5125] ++ cProgram

/-- The call into the lazy gate with `[2368, after_sq]`, entered at `m4j` (4248). -/
def m4jProgram : List Instr :=
  [.op .JUMPDEST, .push 2 3499, .push 2 2368, .push 2 4519, .op .JUMP]

def lastProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP] ++ m4jProgram

def sqExitBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4222 sqExitProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3302 15 4222 sqExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4245 lastProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3317 8 4245 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def m4jBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4248 m4jProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3320 5 4248 m4jProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestLast : Decode.isValidJumpDest TnM128Candidate.bytecode 4245 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3317 (by rfl)

theorem jumpDestM4j : Decode.isValidJumpDest TnM128Candidate.bytecode 4248 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3320 (by rfl)

theorem jumpDestLazy : Decode.isValidJumpDest TnM128Candidate.bytecode 4519 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3526 (by rfl)

abbrev environment := TnM128SquareSteps.environment

/-- `allOnes + (c + 1) = c` for the counter range. -/
private theorem dec_succ (c : Nat) (hc : c ≤ 14) :
    allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := by
  interval_cases c <;> decide

/-- The `last` entry: the retained frame under the unused CSUB call pair `[pdst, pcH2]`. -/
def lazyCsubState (s : State) (mem : ByteArray) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4519) (dst :: ret :: rest)

def lastAt (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcLast
           stack := [UInt256.ofNat 2368, UInt256.ofNat pcH2] ++
             frameStack tn m128 n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `sq_exit` with the counter slot at `c + 1`: reset the carry slot, advance the row pointer to
the next square's row 0, leave `c` in the counter slot and call the CSUB guard as a subroutine
with `[2368, 5062]` on top of the reset frame.  Memory is unchanged. -/
theorem run_sqExit_more (tn m128 : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hc15 : c + 1 ≤ 15) :
    runInstructions sqExitProgram
      (frameAt tn m128 pcSqExit s mem n (UInt256.ofNat 2336) ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c + 1)) ret rest) =
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 5125)
      (frameStack (UInt256.ofNat 0) m128 n (UInt256.ofNat 2592) ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat c) ret rest)) := by
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
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4519 = true := by
    rw [hcode]; exact jumpDestLazy
  have hptr : UInt256.ofNat 256 + UInt256.ofNat 2336 = UInt256.ofNat 2592 := by decide
  simp [sqExitProgram, cProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcSqExit, lazyCsubState, framed, hdec, hcNat, htrue, hjd, hptr,
    hc16', hc17, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

/-- `sq_exit` with the counter slot at zero: reset the carry slot, advance the row pointer,
leave `allOnes` in the (dead) counter slot and fall through to `last`. -/
theorem run_sqExit_last (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) :
    runInstructions sqExitProgram
      (frameAt tn m128 pcSqExit s mem n (UInt256.ofNat 2336) ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 0) ret rest) =
    some (lastAt (UInt256.ofNat 0) m128 s mem n (UInt256.ofNat 2592) ent tl inv m0 m96
      m64 m32 aprev allOnes ret rest) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat 0 = allOnes := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
  have hptr : UInt256.ofNat 256 + UInt256.ofNat 2336 = UInt256.ofNat 2592 := by decide
  simp [sqExitProgram, cProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, lastAt, pcSqExit, pcLast, pcH2, hdec, hzero,
    hfalse, hptr,
    hc16', hc17, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

/-- `last`: drop the unused call pair, then call the CSUB guard as a subroutine with
`[pdst, after]` on top of the retained frame. -/
theorem run_last (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode) :
    runInstructions lastProgram
      (lastAt tn m128 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3499)
      (frameStack tn m128 n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4519 = true := by
    rw [hcode]; exact jumpDestLazy
  simp [lastProgram, m4jProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, lastAt, pcLast, lazyCsubState, framed, hjd, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The loop's blocks as gas steps -/

/-- `sq_exit` with the counter slot above zero: straight into the CSUB guard, returning to 5062. -/
def gasSteps_sqExitMore (tn m128 : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hc15 : c + 1 ≤ 15) :
    Challenge.EvmProof.GasSteps
      (frameAt tn m128 pcSqExit s mem n (UInt256.ofNat 2336) ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c + 1)) ret rest)
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 5125)
        (frameStack (UInt256.ofNat 0) m128 n (UInt256.ofNat 2592) ent tl inv m0 m96 m64 m32 aprev
          (UInt256.ofNat c) ret rest)) :=
  sqExitBlock.steps
    (environment (frameAt tn m128 pcSqExit s mem n (UInt256.ofNat 2336) ent tl inv m0 m96 m64 m32
      aprev (UInt256.ofNat (c + 1)) ret rest) hcode hfork hrun hnp) rfl
    (run_sqExit_more tn m128 s mem n c ent tl inv m0 m96 m64 m32 aprev ret rest hcap hcode hc15)

/-- `sq_exit` with the counter slot at zero. -/
def gasSteps_sqExitLast (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (frameAt tn m128 pcSqExit s mem n (UInt256.ofNat 2336) ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 0) ret rest)
      (lastAt (UInt256.ofNat 0) m128 s mem n (UInt256.ofNat 2592) ent tl inv m0 m96 m64
        m32 aprev allOnes ret rest) :=
  sqExitBlock.steps
    (environment (frameAt tn m128 pcSqExit s mem n (UInt256.ofNat 2336) ent tl inv m0 m96 m64 m32
      aprev (UInt256.ofNat 0) ret rest) hcode hfork hrun hnp) rfl
    (run_sqExit_last tn m128 s mem n ent tl inv m0 m96 m64 m32 aprev ret rest hcap)

/-- `last`: drop the call pair, rewrite the frame's `ret` slot to `after_sq` and jump to
`nx`. -/
def gasSteps_last (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (lastAt tn m128 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3499)
        (frameStack tn m128 n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  lastBlock.steps
    (environment (lastAt tn m128 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_last tn m128 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode)


#print axioms gasSteps_sqExitMore
#print axioms gasSteps_sqExitLast
#print axioms gasSteps_last
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
