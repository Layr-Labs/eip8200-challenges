import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareFullSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareExit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

def pcSqExit : Nat := 4362
def pcLast : Nat := 4384
def pcH2 : Nat := 4409
def pcAgain : Nat := 4419

def frameStack (tn : UInt256) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 4471, UInt256.ofNat 2336, ent, tn, allOnes,
   UInt256.ofNat (TnCandidateReductionSteps.l2PC n), inv, m0, tl, m96, m64, m32,
   aprev, pdst, ret] ++ rest

def frameAt (tn : UInt256) (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat pc)
    (frameStack tn n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)

def countMem (mem : ByteArray) (c : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded c 32) 2624

def sqExitProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4409, .push 2 2368, .push 2 2624, .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .push 2 2624, .op .MSTORE, .push 2 4389, .op .JUMPI]

def lastProgram : List Instr := [.push 2 3657, .op (.Swap ⟨1, by decide⟩), .op .POP]

def sqExitBlock : Block TnCandidateArtifact.submissionArtifact .Osaka 4362 sqExitProgram :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 3313 12 4362 sqExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block TnCandidateArtifact.submissionArtifact .Osaka 4384 lastProgram :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 3325 3 4384 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestLazy : Decode.isValidJumpDest TnCandidate.bytecode 4389 = true :=
  TnCandidateArtifact.isValidJumpDest_index 3328 (by rfl)

abbrev environment := TnCandidateSquareSteps.environment

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
def lazyCsubState (s : State) (mem : ByteArray) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4389) (dst :: ret :: rest)

def lastAt (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcLast
           stack := [UInt256.ofNat 2368, UInt256.ofNat pcH2] ++
             frameStack tn n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `sq_exit` with a counter above one: store `c` and call the CSUB guard as a subroutine
with `[pdst, again]` on top of the retained frame. -/
theorem run_sqExit_more (tn : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnCandidate.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat (c + 1)) :
    runInstructions sqExitProgram
      (frameAt tn pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lazyCsubState s (countMem mem c) (UInt256.ofNat 2368) (UInt256.ofNat 4409)
      (frameStack tn n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
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
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4389 = true := by
    rw [hcode]; exact jumpDestLazy
  have h9280 : (2624 : UInt256).toNat = 2624 := by decide
  simp [sqExitProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcSqExit, lazyCsubState, framed, countMem, hcount, hdec, hcNat, htrue, hjd, h9280,
    State.activeWordsAfterUInt256, activeWords9280 s hact,
    hc16', hc17, hc18, hc19, hc20, hc21, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- `sq_exit` with the counter at one: store zero and fall through to `last`. -/
theorem run_sqExit_last (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat 1) :
    runInstructions sqExitProgram
      (frameAt tn pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lastAt tn s (countMem mem 0) n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
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
    frameAt, framed, frameStack, lastAt, pcSqExit, pcLast, pcAgain, pcH2, countMem, hcount, hdec, hzero,
    hfalse, h9280,
    State.activeWordsAfterUInt256, activeWords9280 s hact,
    hc16', hc17, hc18, hc19, hc20, hc21, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- `last`: drop the unused call pair, then call the CSUB guard as a subroutine with
`[pdst, after]` on top of the retained frame. -/
theorem run_last (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnCandidate.bytecode) :
    runInstructions lastProgram
      (lastAt tn s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3657)
      (frameStack tn n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4389 = true := by
    rw [hcode]; exact jumpDestLazy
  simp [lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, lastAt, pcLast, lazyCsubState, framed, hjd, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The loop's blocks as gas steps -/

/-- `sq_exit` with a counter above one: straight into the CSUB guard. -/
def gasSteps_sqExitMore (tn : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnCandidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat (c + 1)) :
    Challenge.EvmProof.GasSteps
      (frameAt tn pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lazyCsubState s (countMem mem c) (UInt256.ofNat 2368) (UInt256.ofNat 4409)
        (frameStack tn n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  sqExitBlock.steps
    (environment (frameAt tn pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_sqExit_more tn s mem n c pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode
      hact hcpos hc16 hcount)

/-- `sq_exit` with the counter at one. -/
def gasSteps_sqExitLast (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnCandidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcount : MachineState.readWord mem 2624 = UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps
      (frameAt tn pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lastAt tn s (countMem mem 0) n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) :=
  sqExitBlock.steps
    (environment (frameAt tn pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_sqExit_last tn s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hact hcount)

/-- `last`: drop the call pair, rewrite the frame's `ret` slot to `after_sq` and jump to
`nx`. -/
def gasSteps_last (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnCandidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (lastAt tn s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3657)
        (frameStack tn n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  lastBlock.steps
    (environment (lastAt tn s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_last tn s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode)


#print axioms gasSteps_sqExitMore
#print axioms gasSteps_sqExitLast
#print axioms gasSteps_last
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareExit
