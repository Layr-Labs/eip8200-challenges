import Challenge.Modexp.Submission.Proofs.Fast.TnM128InitialMultiply
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
import Challenge.Modexp.Submission.Proofs.Fast.CapDispatch
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128FusedEntry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore

/-- The product setup after the square loop (pc 3487, TL/p2/zloop/msplit): clear the carry slot,
`aEnd := mem[0xae0] + 0x100` (the staged operand's last limb), drop the row pointer, `q := 0x920 - aEnd`
(zneg2: `= -32·n`), the width's row head `hd := 3313 + 2036·[aEnd = 0x9a0]` (5349 for four limbs),
`dst := 256`, `ret := 772`. -/
def prefixHead : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op (.Swap ⟨12, by decide⟩), .op .POP,
   .push 2 2784, .op .MLOAD, .push 2 256, .op .ADD, .op (.Swap ⟨13, by decide⟩), .op .POP,
   .op .POP,
   .op (.Dup ⟨12, by decide⟩), .push 2 2336, .op .SUB]

/-- The four-limb test of the 97bb cut (leech1996, submission 97bb2bc5, site B):
`PUSH2 0x09a0 DUP15 EQ JUMPDEST` replaces `PUSH1 0x80 DUP15 AND PUSH0 LT`.  The word is
`aEnd = 0x9a0 + 0x80·[n = 8]`, so `[aEnd = 0x9a0]` is the old bit-7 test on both widths. -/
def selTop (x : UInt256) : UInt256 := UInt256.eq x (UInt256.ofNat 2464)

/-- The width's row head from `aEnd` (msplit, 97bb site B). -/
def prefixSelect : List Instr :=
  [.push 2 2464, .op (.Dup ⟨14, by decide⟩), .op .EQ,
   .push 2 2039, .op .MUL, .push 2 3313, .op .ADD, .op (.Swap ⟨1, by decide⟩), .op .POP]

def prefixTail : List Instr :=
  [.push 2 256, .op (.Swap ⟨14, by decide⟩), .op .POP,
   .push 2 690, .op (.Swap ⟨15, by decide⟩), .op .POP]

def prefixProgram : List Instr := (prefixHead ++ prefixSelect) ++ prefixTail

/-- Zero the product scratch `[2048, 2048 + 64 + 32·n)` (`aEnd - 0x8e0` bytes) and jump to the
row head. -/
def clearProgram : List Instr :=
  [.push 2 2272, .op (.Dup ⟨14, by decide⟩), .op .SUB,
   .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY, .op (.Dup ⟨1, by decide⟩), .op .JUMP]

def prefixBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 3256 prefixProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 2533 29 3256 prefixProgram
    (by decide) (by rfl) (by rfl) (by decide)
def clearBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 3301 clearProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 2562 8 3301 clearProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first multiply row, the operand block at 2368 and the product scratch cleared. -/
def rowReady (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  TnM128RowsSteps.rowState s ⟨mem, UInt256.ofNat 0⟩ n 0 w3 ent tl inv m0
    (UInt256.ofNat (2368+32*n-32)) m96 m64 m32 (UInt256.ofNat 256) (UInt256.ofNat 690) rest

def prefixState (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 3301)
    (TnCacheFrameOps.frame (TnCacheRowPointers.qptr n 0) (UInt256.ofNat (TnM128RowSteps.headPC n))
      w3 ent m32 (MachineState.readWord mem 128) m64
      (m0 :: tl :: m96 :: inv :: UInt256.ofNat 0 :: UInt256.ofNat (2368+32*n-32) ::
        UInt256.ofNat 256 :: UInt256.ofNat 690 :: rest))

theorem run_prefixHead (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (htlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*n))
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prefixHead
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
      some (framed {s with memory := mem} (UInt256.ofNat 3276)
        ([UInt256.ofNat (2^256 - 32*n), UInt256.ofNat 5297, w3, ent, m32, allOnes,
          MachineState.readWord mem 128, m64, m0, tl, m96, inv, UInt256.ofNat 0,
          UInt256.ofNat (2368+32*n-32), pdst, ret] ++ rest)) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := activeWords_fix s 2784 32 (by decide) (by decide) hact
  have h2784 : (2784 : UInt256).toNat = 2784 := by decide
  rcases hn with rfl | rfl <;>
  · simp [prefixHead, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      TnM128SquareExit.frameAt, TnM128SquareExit.frameStack, framed,
      State.activeWordsAfterUInt256, hactT, htlw, h2784,
      hc13, hc14, hc15, hc16, hc17, hc18, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
    all_goals decide

theorem run_prefixSelect (s : State) (q hd w3 ent m32 m128 m64 m0 tl m96 inv z aEnd pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions prefixSelect
      (framed s (UInt256.ofNat 3276)
        ([q, hd, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, z, aEnd, pdst, ret] ++ rest)) =
      some (framed s (UInt256.ofNat 3291)
        ([q, UInt256.ofNat 3313 + UInt256.ofNat 2039 * selTop aEnd, w3, ent, m32,
          allOnes, m128, m64, m0, tl, m96, inv, z, aEnd, pdst, ret] ++ rest)) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  simp [prefixSelect, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    List.exchange, hc16, hc17, hc18,
    selTop,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prefixTail (s : State) (q hd w3 ent m32 m128 m64 m0 tl m96 inv z aEnd pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions prefixTail
      (framed s (UInt256.ofNat 3291)
        ([q, hd, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, z, aEnd, pdst, ret] ++ rest)) =
      some (framed s (UInt256.ofNat 3301)
        ([q, hd, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, z, aEnd,
          UInt256.ofNat 256, UInt256.ofNat 690] ++ rest)) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  simp [prefixTail, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    List.exchange, hc16, hc17,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem headPC_select (n : Nat) (hn : n = 4 ∨ n = 8) :
    UInt256.ofNat 3313 + UInt256.ofNat 2039 * selTop (UInt256.ofNat (2368+32*n-32)) =
      UInt256.ofNat (TnM128RowSteps.headPC n) := by
  rcases hn with rfl | rfl <;> decide

theorem run_prefix (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (htlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*n))
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prefixProgram
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
      some (prefixState s mem n w3 ent tl inv m0 m96 m64 m32 rest) := by
  have h1 := run_prefixHead tn s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hn
    htlw hact
  have h2 := run_prefixSelect {s with memory := mem} (UInt256.ofNat (2^256 - 32*n)) (UInt256.ofNat 5297) w3
    ent m32 (MachineState.readWord mem 128) m64 m0 tl m96 inv (UInt256.ofNat 0)
    (UInt256.ofNat (2368+32*n-32)) pdst ret rest hcap
  have h3 := run_prefixTail {s with memory := mem} (UInt256.ofNat (2^256 - 32*n))
    (UInt256.ofNat 3313 + UInt256.ofNat 2039 * selTop (UInt256.ofNat (2368+32*n-32)))
    w3 ent m32 (MachineState.readWord mem 128) m64 m0 tl m96 inv (UInt256.ofNat 0)
    (UInt256.ofNat (2368+32*n-32)) pdst ret rest hcap
  have hq : UInt256.ofNat (2^256 - 32*n) = TnCacheRowPointers.qptr n 0 := by
    simp only [TnCacheRowPointers.qptr, Nat.sub_zero]
  have h := runInstructions_append_some _ _ _ _ _ (runInstructions_append_some _ _ _ _ _ h1 h2) h3
  rw [headPC_select n hn, hq] at h
  exact h

theorem run_clear (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hjd : Decode.isValidJumpDest s.executionEnv.code (TnM128RowSteps.headPC n) = true) :
    runInstructions clearProgram (prefixState s mem n w3 ent tl inv m0 m96 m64 m32 rest) =
      some (rowReady s (mpZeroed s mem n) n w3 ent tl inv m0 m96 m64 m32 rest) := by
  have hn8 : n ≤ 8 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hsub : UInt256.ofNat (2368+32*n-32) - UInt256.ofNat 2272 = UInt256.ofNat (64+32*n) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  have hactC := activeWords_fix s 2048 (64+32*n) (by omega) (by omega) hact
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt hcds
  have hsizeN : (64+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64+32*n := Nat.mod_eq_of_lt (by omega)
  have h2048 : (2048 : UInt256).toNat = 2048 := by decide
  have hhd : (UInt256.ofNat (TnM128RowSteps.headPC n)).toNat = TnM128RowSteps.headPC n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    rcases hn with rfl | rfl <;> decide
  simp only [prefixState, rowReady, TnM128RowsSteps.rowState,
    Monpro.readWord_mpZeroed s mem n 128 hn8 (Or.inl (by decide))]
  simp [clearProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    TnCacheFrameOps.frame, framed, mpZeroed, hsub, hactC, hcdsN, hsizeN, h2048, hhd, hjd,
    State.activeWordsAfterUInt256, hc13, hc14, hc15, hc16, hc17, hc18, hc19, show 0 < n from by omega,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def gasSteps_entry (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (htlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*n)) :
    Challenge.EvmProof.GasSteps
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (rowReady s (mpZeroed s mem n) n w3 ent tl inv m0 m96 m64 m32 rest) :=
  (prefixBlock.steps (TnM128SquareSteps.environment
    (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) hcode hfork hrun hnp) rfl
    (run_prefix tn s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hn htlw hact)).trans
  (clearBlock.steps (TnM128SquareSteps.environment
    (prefixState s mem n w3 ent tl inv m0 m96 m64 m32 rest) hcode hfork hrun hnp) rfl
    (run_clear s mem n w3 ent tl inv m0 m96 m64 m32 rest hcap hn hact hcds
      (by
        have h := TnM128RowSteps.head_jump n hn
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by rcases hn with rfl | rfl <;> decide)] at h
        rw [hcode]; exact h)))

#print axioms gasSteps_entry
end Challenge.Modexp.Submission.Proofs.Fast.TnM128FusedEntry
