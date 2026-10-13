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
def pcSqExit : Nat := 4236
/-- Eight-limb counter, reached only by fall-through from `pcSqExit`. -/
def pcC : Nat := 4248
/-- `last`, reached by fall-through from `pcC` (n = 8) or from the four-limb tail jump (n = 4). -/
def pcLast : Nat := 4260
/-- Eight-limb CSUB return: the next square's row-0 head. -/
def pcH2 : Nat := 5092
/-- Four-limb kernel exit: push the R4 return 4579, then the same stack counter. -/
def pcE4 : Nat := 4273
/-- Four-limb `last` trampoline. -/
def pcE4Tail : Nat := 4289

def frameStack (tn m128 : UInt256) (_n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 4293, w3, ent, m32, allOnes,
   m128, m64, m0, tl, m96, inv, tn,
   aprev, pdst, ret] ++ rest

def frameAt (tn m128 : UInt256) (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat pc)
    (frameStack tn m128 n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)

/-- The square counter lives in the frame's `pdst` slot (dead during the square loop; pc 3471
overwrites it).  With `[r, frame]` on the stack the block reads `pdst` (`DUP16`), stores
`pdst - 1` back (`DUP8` is `allOnes`, `SWAP16`), and calls the CSUB guard with `[2368, r]`
when the old value is nonzero. -/
def cProgram : List Instr :=
  [.op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Swap ⟨15, by decide⟩), .push 2 2368, .op (.Swap ⟨0, by decide⟩),
   .push 2 4551, .op .JUMPI]

/-- n8g: tn test (`SWAP12` also clears the carry slot, the row pointer being zero), then for
`tn = 0` the `t -> a` copy, the counter and the next square's row 0 (5092) or the product
setup (3487). -/
def n8aProgram : List Instr :=
  [.op .JUMPDEST, .op (.Swap ⟨11, by decide⟩), .push 2 4236, .op .JUMPI]

def n8bProgram : List Instr :=
  [.push 2 256, .op (.Dup ⟨0, by decide⟩), .push 2 2112, .push 2 2368, .op .MCOPY,
   .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨14, by decide⟩),
   .push 2 5092, .op .JUMPI]

def n8cProgram : List Instr := [.push 2 3487, .op .JUMP]

/-- rarej/st8: the carry continuation (`tn ≠ 0`) stores the (nonzero) row head word at `0x820`
for the subtraction's select, rebuilds the frame and calls the eight-limb subtraction `s8`
(4374) directly with `[2368, 5092]`, or falls into `last`. -/
def rareProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .push 2 2080, .op .MSTORE,
   .push 2 256, .push 2 5092,
   .op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Swap ⟨15, by decide⟩), .push 2 2368, .op (.Swap ⟨0, by decide⟩),
   .push 2 4374, .op .JUMPI]

def e4Program : List Instr :=
  [.op .JUMPDEST, .push 2 4610] ++ cProgram

def e4TailProgram : List Instr :=
  [.push 2 4260, .op .JUMP]

def lastProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP, .push 2 3487, .push 2 2368, .push 2 4551, .op .JUMP]

def n8aBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4207 n8aProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3283 4 4207 n8aProgram
    (by decide) (by rfl) (by rfl) (by decide)

def n8bBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4213 n8bProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3287 11 4213 n8bProgram
    (by decide) (by rfl) (by rfl) (by decide)

def n8cBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4232 n8cProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3298 2 4232 n8cProgram
    (by decide) (by rfl) (by rfl) (by decide)

def rareBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4236 rareProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3300 14 4236 rareProgram
    (by decide) (by rfl) (by rfl) (by decide)

def e4Block : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4273 e4Program :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3321 10 4273 e4Program
    (by decide) (by rfl) (by rfl) (by decide)

def e4TailBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4289 e4TailProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3331 2 4289 e4TailProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4260 lastProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3314 7 4260 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestLast : Decode.isValidJumpDest TnM128Candidate.bytecode 4260 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3314 (by rfl)

theorem jumpDestE4 : Decode.isValidJumpDest TnM128Candidate.bytecode 4273 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3321 (by rfl)

theorem jumpDestLazy : Decode.isValidJumpDest TnM128Candidate.bytecode 4551 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3530 (by rfl)

abbrev environment := TnM128SquareSteps.environment

/-- `allOnes + (c + 1) = c` for the counter range. -/
private theorem dec_succ (c : Nat) (hc : c ≤ 14) :
    allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := by
  interval_cases c <;> decide

/-- The `last` entry: the retained frame under the unused CSUB call pair `[pdst, pcH2]`. -/
def lazyCsubState (s : State) (mem : ByteArray) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4551) (dst :: ret :: rest)

def lastAt (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcLast
           stack := [UInt256.ofNat 2368, UInt256.ofNat pcH2] ++
             frameStack tn m128 n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `last`: drop the unused call pair, then call the CSUB guard as a subroutine with
`[pdst, after]` on top of the retained frame. -/
theorem run_last (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode) :
    runInstructions lastProgram
      (lastAt tn m128 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3487)
      (frameStack tn m128 n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4551 = true := by
    rw [hcode]; exact jumpDestLazy
  simp [lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, lastAt, pcLast, lazyCsubState, framed, hjd, hcap15, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem jumpDestRare : Decode.isValidJumpDest TnM128Candidate.bytecode 4236 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3300 (by rfl)

theorem jumpDestH2 : Decode.isValidJumpDest TnM128Candidate.bytecode 5092 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3996 (by rfl)

theorem jumpDestSetup : Decode.isValidJumpDest TnM128Candidate.bytecode 3487 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 2716 (by rfl)

theorem jumpDestS8 : Decode.isValidJumpDest TnM128Candidate.bytecode 4374 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3398 (by rfl)

/-- The frame without its row pointer, as `n8`'s tn test leaves it. -/
def dropAt (tn m128 : UInt256) (pc : Nat) (s : State) (mem : ByteArray) (_n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat pc)
    ([UInt256.ofNat 4293, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, tn,
      aprev, pdst, ret] ++ rest)

/-- The eight-limb `t → a` copy done inline by `n8` (v9's lazy copy for `n = 8`, `dst = 2368`). -/
def copyMem (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded mem 2112 256) 2368

theorem run_n8a_zero (m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) :
    runInstructions n8aProgram
      (frameAt (UInt256.ofNat 0) m128 4207 s mem n (UInt256.ofNat 0) w3 ent tl inv m0 m96 m64 m32
        aprev pdst ret rest) =
    some (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev pdst ret
      rest) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp [n8aProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, dropAt, hfalse, hcap15, hc16', hc17, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_n8a_rare (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode) (htn : UInt256.isTrue tn) :
    runInstructions n8aProgram
      (frameAt tn m128 4207 s mem n (UInt256.ofNat 0) w3 ent tl inv m0 m96 m64 m32
        aprev pdst ret rest) =
    some (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev pdst ret
      rest) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4236 = true := by
    rw [hcode]; exact jumpDestRare
  simp [n8aProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, dropAt, htn, hjd, hcap15, hc16', hc17, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_n8b_more (m128 : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode) (hc15 : c + 1 ≤ 15) :
    runInstructions n8bProgram
      (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c + 1)) ret rest) =
    some (frameAt (UInt256.ofNat 0) m128 5092 s (copyMem mem) n (UInt256.ofNat 256) w3 ent tl inv
      m0 m96 m64 m32 aprev (UInt256.ofNat c) ret rest) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := dec_succ c (by omega)
  have hcNat : (UInt256.ofNat (c + 1)).toNat = c + 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htrue : UInt256.isTrue (UInt256.ofNat (c + 1)) := by
    show (UInt256.ofNat (c + 1)).toNat ≠ 0
    rw [hcNat]; omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 5092 = true := by
    rw [hcode]; exact jumpDestH2
  have hactD := Csub.activeWordsAfter_fix s.activeWords.toNat 2368 256 (by omega) (by omega) hact
  have hactT := Csub.activeWords_fix s 2112 256 (by omega) (by omega) hact
  simp [n8bProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, dropAt, copyMem, hdec, hcNat, htrue, hjd,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactD, hactT,
    hcap15, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_n8b_last (m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions n8bProgram
      (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 0) ret rest) =
    some (frameAt (UInt256.ofNat 0) m128 4232 s (copyMem mem) n (UInt256.ofNat 256) w3 ent tl inv
      m0 m96 m64 m32 aprev allOnes ret rest) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat 0 = allOnes := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
  have hactD := Csub.activeWordsAfter_fix s.activeWords.toNat 2368 256 (by omega) (by omega) hact
  have hactT := Csub.activeWords_fix s 2112 256 (by omega) (by omega) hact
  simp [n8bProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, dropAt, copyMem, hdec, hfalse, hzero,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactD, hactT,
    hcap15, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_n8c (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode) :
    runInstructions n8cProgram
      (frameAt tn m128 4232 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt tn m128 3487 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 3487 = true := by
    rw [hcode]; exact jumpDestSetup
  simp [n8cProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, hjd, hcap15, hc16', hc17,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The rare path's entry into the eight-limb subtraction `s8` with `[2368, 5092]`. -/
def s8At (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4374) ([UInt256.ofNat 2368, ret] ++ rest)

theorem run_rare_more (m128 : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode) (hc15 : c + 1 ≤ 15) :
    runInstructions rareProgram
      (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c + 1)) ret rest) =
    some (s8At s (TnCacheMemory.lift mem (UInt256.ofNat 4293)) (UInt256.ofNat 5092)
      (frameStack (UInt256.ofNat 0) m128 n (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat c) ret rest)) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat (c + 1) = UInt256.ofNat c := dec_succ c (by omega)
  have hcNat : (UInt256.ofNat (c + 1)).toNat = c + 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htrue : UInt256.isTrue (UInt256.ofNat (c + 1)) := by
    show (UInt256.ofNat (c + 1)).toNat ≠ 0
    rw [hcNat]; omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4374 = true := by
    rw [hcode]; exact jumpDestS8
  have hactF := Csub.activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hlt1004 : rest.length < 1004 := by omega
  simp [rareProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, dropAt, s8At, TnCacheMemory.lift, hdec, hcNat, htrue, hjd,
    State.activeWordsAfterUInt256, hactF, hlt1004, hcap15, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_rare_last (m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions rareProgram
      (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 0) ret rest) =
    some (lastAt (UInt256.ofNat 0) m128 s (TnCacheMemory.lift mem (UInt256.ofNat 4293)) n
      (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64 m32 aprev allOnes ret rest) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hc16' : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hdec : allOnes + UInt256.ofNat 0 = allOnes := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
  have hactF := Csub.activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hlt1004 : rest.length < 1004 := by omega
  simp [rareProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, framed, frameStack, dropAt, lastAt, pcLast, pcH2, TnCacheMemory.lift, hdec, hfalse,
    hzero, State.activeWordsAfterUInt256, hactF, hlt1004, hcap15, hc16', hc17, hc18, hc19, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The loop's blocks as gas steps -/

/-- `last`: drop the call pair, rewrite the frame's `ret` slot to `after_sq` and jump to
`nx`. -/
def gasSteps_last (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (lastAt tn m128 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3487)
        (frameStack tn m128 n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  lastBlock.steps
    (environment (lastAt tn m128 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_last tn m128 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode)


def gasSteps_n8aZero (m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (frameAt (UInt256.ofNat 0) m128 4207 s mem n (UInt256.ofNat 0) w3 ent tl inv m0 m96 m64 m32
        aprev pdst ret rest)
      (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) :=
  n8aBlock.steps
    (environment (frameAt (UInt256.ofNat 0) m128 4207 s mem n (UInt256.ofNat 0) w3 ent tl inv m0 m96
      m64 m32 aprev pdst ret rest) hcode hfork hrun hnp) rfl
    (run_n8a_zero m128 s mem n w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap)

def gasSteps_n8aRare (tn m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (htn : UInt256.isTrue tn) :
    Challenge.EvmProof.GasSteps
      (frameAt tn m128 4207 s mem n (UInt256.ofNat 0) w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) :=
  n8aBlock.steps
    (environment (frameAt tn m128 4207 s mem n (UInt256.ofNat 0) w3 ent tl inv m0 m96 m64 m32
      aprev pdst ret rest) hcode hfork hrun hnp) rfl
    (run_n8a_rare tn m128 s mem n w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode htn)

def gasSteps_n8bMore (m128 : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hc15 : c + 1 ≤ 15) :
    Challenge.EvmProof.GasSteps
      (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c + 1)) ret rest)
      (frameAt (UInt256.ofNat 0) m128 5092 s (copyMem mem) n (UInt256.ofNat 256) w3 ent tl inv
        m0 m96 m64 m32 aprev (UInt256.ofNat c) ret rest) :=
  n8bBlock.steps
    (environment (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
      (UInt256.ofNat (c + 1)) ret rest) hcode hfork hrun hnp) rfl
    (run_n8b_more m128 s mem n c w3 ent tl inv m0 m96 m64 m32 aprev ret rest hcap hact hcode hc15)

def gasSteps_n8bLast (m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 0) ret rest)
      (frameAt (UInt256.ofNat 0) m128 3487 s (copyMem mem) n (UInt256.ofNat 256) w3 ent tl inv
        m0 m96 m64 m32 aprev allOnes ret rest) :=
  (n8bBlock.steps
    (environment (dropAt (UInt256.ofNat 0) m128 4213 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
      (UInt256.ofNat 0) ret rest) hcode hfork hrun hnp) rfl
    (run_n8b_last m128 s mem n w3 ent tl inv m0 m96 m64 m32 aprev ret rest hcap hact)).trans
  (n8cBlock.steps
    (environment (frameAt (UInt256.ofNat 0) m128 4232 s (copyMem mem) n (UInt256.ofNat 256) w3 ent
      tl inv m0 m96 m64 m32 aprev allOnes ret rest) hcode hfork hrun hnp) rfl
    (run_n8c (UInt256.ofNat 0) m128 s (copyMem mem) n (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64
      m32 aprev allOnes ret rest hcap hcode))

def gasSteps_rareMore (m128 : UInt256) (s : State) (mem : ByteArray) (n c : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hc15 : c + 1 ≤ 15) :
    Challenge.EvmProof.GasSteps
      (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat (c + 1)) ret rest)
      (s8At s (TnCacheMemory.lift mem (UInt256.ofNat 4293)) (UInt256.ofNat 5092)
        (frameStack (UInt256.ofNat 0) m128 n (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64 m32 aprev
          (UInt256.ofNat c) ret rest)) :=
  rareBlock.steps
    (environment (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
      (UInt256.ofNat (c + 1)) ret rest) hcode hfork hrun hnp) rfl
    (run_rare_more m128 s mem n c w3 ent tl inv m0 m96 m64 m32 aprev ret rest hcap hact hcode hc15)

def gasSteps_rareLast (m128 : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
        (UInt256.ofNat 0) ret rest)
      (lazyCsubState s (TnCacheMemory.lift mem (UInt256.ofNat 4293)) (UInt256.ofNat 2368)
        (UInt256.ofNat 3487)
        (frameStack (UInt256.ofNat 0) m128 n (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64 m32 aprev
          allOnes ret rest)) :=
  (rareBlock.steps
    (environment (dropAt (UInt256.ofNat 0) m128 4236 s mem n w3 ent tl inv m0 m96 m64 m32 aprev
      (UInt256.ofNat 0) ret rest) hcode hfork hrun hnp) rfl
    (run_rare_last m128 s mem n w3 ent tl inv m0 m96 m64 m32 aprev ret rest hcap hact)).trans
  (gasSteps_last (UInt256.ofNat 0) m128 s (TnCacheMemory.lift mem (UInt256.ofNat 4293)) n
    (UInt256.ofNat 256) w3 ent tl inv m0 m96 m64 m32 aprev allOnes ret rest hcap hrun hcode hfork hnp)


#print axioms gasSteps_last
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
