import Challenge.Modexp.Submission.Proofs.CycleGlobal.EarlyCsubInstructions
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128InitialMultiply
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128SquareExit
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleSubmission.Global.Fast.TnM128FusedEntry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

def prefixHead : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op (.Swap ⟨12, by decide⟩), .op .POP,
   .push 2 2784, .op .MLOAD, .push 2 256, .op .ADD, .op (.Swap ⟨13, by decide⟩), .op .POP,
   .op .POP]
def prefixSelect : List Instr :=
  [.push 1 127, .op .NOT, .push 2 3775, .op (.Swap ⟨1, by decide⟩), .op .POP]
def prefixTail : List Instr :=
  [.push 2 256, .op (.Swap ⟨14, by decide⟩), .op .POP,
   .push 2 690, .op (.Swap ⟨15, by decide⟩), .op .POP]
def prefixProgram : List Instr := (prefixHead ++ prefixSelect) ++ prefixTail
def clearProgram : List Instr :=
  [.push 1 192, .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY, .op (.Dup ⟨1, by decide⟩), .op .JUMP]
def prefixBlock : Block CycleSubmission.Artifact.artifact .Osaka 3256 prefixProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2531 22 3256 prefixProgram
    (by decide) (by rfl) (by rfl) (by decide)
def clearBlock : Block CycleSubmission.Artifact.artifact .Osaka 3289 clearProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2553 6 3289 clearProgram
    (by decide) (by rfl) (by rfl) (by decide)
def rowReady (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  TnM128RowsSteps.rowState s ⟨mem, UInt256.ofNat 0⟩ n 0 w3 ent tl inv m0
    (UInt256.ofNat (2368+32*n-32)) m96 m64 m32 (UInt256.ofNat 256) (UInt256.ofNat 690) rest

def prefixState (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 3289)
    (TnCacheFrameOps.frame (TnCacheRowPointers.qptr n 0) (UInt256.ofNat (TnM128RowSteps.headPC n))
      w3 ent m32 (MachineState.readWord mem 128) m64
      (m0 :: tl :: m96 :: inv :: UInt256.ofNat 0 :: UInt256.ofNat (2368+32*n-32) ::
        UInt256.ofNat 256 :: UInt256.ofNat 690 :: rest))

theorem run_prefixHead (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4)
    (htlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*n))
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prefixHead
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
      some (framed {s with memory := mem} (UInt256.ofNat 3271)
        ([UInt256.ofNat 5297, w3, ent, m32, allOnes,
          MachineState.readWord mem 128, m64, m0, tl, m96, inv, UInt256.ofNat 0,
          UInt256.ofNat (2368+32*n-32), pdst, ret] ++ rest)) := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := activeWords_fix s 2784 32 (by decide) (by decide) hact
  have h2784 : (2784 : UInt256).toNat = 2784 := by decide
  rcases hn with rfl
  · simp [prefixHead, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      TnM128SquareExit.frameAt, TnM128SquareExit.frameStack, framed,
      State.activeWordsAfterUInt256, hactT, htlw, h2784,
      capacity, Nat.add_assoc, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
    all_goals decide

theorem run_prefixSelect (s : State) (hd w3 ent m32 m128 m64 m0 tl m96 inv z aEnd pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions prefixSelect
      (framed s (UInt256.ofNat 3271)
        ([hd, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, z, aEnd, pdst, ret] ++ rest)) =
      some (framed s (UInt256.ofNat 3279)
        ([UInt256.ofNat (2^256-128), UInt256.ofNat 3775, w3, ent, m32,
          allOnes, m128, m64, m0, tl, m96, inv, z, aEnd, pdst, ret] ++ rest)) := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [prefixSelect, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    List.exchange, capacity, Nat.add_assoc,

    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals decide

theorem run_prefixTail (s : State) (q hd w3 ent m32 m128 m64 m0 tl m96 inv z aEnd pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions prefixTail
      (framed s (UInt256.ofNat 3279)
        ([q, hd, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, z, aEnd, pdst, ret] ++ rest)) =
      some (framed s (UInt256.ofNat 3289)
        ([q, hd, w3, ent, m32, allOnes, m128, m64, m0, tl, m96, inv, z, aEnd,
          UInt256.ofNat 256, UInt256.ofNat 690] ++ rest)) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  simp [prefixTail, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    List.exchange, hc16, hc17,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prefix (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4)
    (htlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*n))
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prefixProgram
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
      some (prefixState s mem n w3 ent tl inv m0 m96 m64 m32 rest) := by
  subst n
  have h1 := run_prefixHead tn s mem 4 pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap rfl
    htlw hact
  have h2 := run_prefixSelect {s with memory := mem} (UInt256.ofNat 5297) w3
    ent m32 (MachineState.readWord mem 128) m64 m0 tl m96 inv (UInt256.ofNat 0)
    (UInt256.ofNat (2368+32*4-32)) pdst ret rest hcap
  have h3 := run_prefixTail {s with memory := mem} (UInt256.ofNat (2^256 - 32*4))
    (UInt256.ofNat 3775)
    w3 ent m32 (MachineState.readWord mem 128) m64 m0 tl m96 inv (UInt256.ofNat 0)
    (UInt256.ofNat (2368+32*4-32)) pdst ret rest hcap
  have hq : UInt256.ofNat (2^256 - 32*4) = TnCacheRowPointers.qptr 4 0 := by
    simp only [TnCacheRowPointers.qptr, Nat.sub_zero]
  have h := runInstructions_append_some _ _ _ _ _ (runInstructions_append_some _ _ _ _ _ h1 h2) h3
  rw [hq] at h
  exact h

theorem run_clear (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hjd : Decode.isValidJumpDest s.executionEnv.code (TnM128RowSteps.headPC n) = true) :
    runInstructions clearProgram (prefixState s mem n w3 ent tl inv m0 m96 m64 m32 rest) =
      some (rowReady s (mpZeroed s mem n) n w3 ent tl inv m0 m96 m64 m32 rest) := by
  subst n
  have hn8 : 4 ≤ 8 := by omega
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have hsub : UInt256.ofNat (2368+32*4-32) - UInt256.ofNat 2272 = UInt256.ofNat (64+32*4) := by
    decide
  have hactC := activeWords_fix s 2048 (64+32*4) (by omega) (by omega) hact
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt hcds
  have hsizeN : (64+32*4) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64+32*4 := Nat.mod_eq_of_lt (by omega)
  have h2048 : (2048 : UInt256).toNat = 2048 := by decide
  have hhd : (UInt256.ofNat (TnM128RowSteps.headPC 4)).toNat = TnM128RowSteps.headPC 4 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    decide
  simp only [prefixState, rowReady, TnM128RowsSteps.rowState,
    Monpro.readWord_mpZeroed s mem 4 128 hn8 (Or.inl (by decide))]
  simp [clearProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    TnCacheFrameOps.frame, framed, mpZeroed, hsub, hactC, hcdsN, hsizeN, h2048, hhd, hjd,
    State.activeWordsAfterUInt256, capacity, Nat.add_assoc, show 0 < 4 from by omega,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def gasSteps_entry (tn : UInt256) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (htlw : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*n)) :
    Challenge.EvmProof.GasSteps
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (rowReady s (mpZeroed s mem n) n w3 ent tl inv m0 m96 m64 m32 rest) :=
  (prefixBlock.steps (CycleSubmission.Global.Fast.EarlyCsub.environment
    (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest) hcode hfork hrun hnp) rfl
    (run_prefix tn s mem n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hn htlw hact)).trans
  (clearBlock.steps (CycleSubmission.Global.Fast.EarlyCsub.environment
    (prefixState s mem n w3 ent tl inv m0 m96 m64 m32 rest) hcode hfork hrun hnp) rfl
    (run_clear s mem n w3 ent tl inv m0 m96 m64 m32 rest hcap hn hact hcds
      (by
        have h := TnM128RowSteps.head_jump n hn
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by subst n; decide)] at h
        rw [hcode]; exact h)))

end CycleSubmission.Global.Fast.TnM128FusedEntry
