import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Width dispatch before the first square and after conditional subtraction.
The tenth frame word is TL: 2208 selects the dedicated R4 routine, 2336
selects the eight-limb path. H1 jumps to the overwrite-first row; H2 falls
through to the cached-carry reset in `TnM128Again`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Hooks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareLoopBlocks

def pcH1 : Nat := 4576
def pcH1Fall : Nat := 4585
def pcR4 : Nat := 4589

/-- 判别块。 -/
def hookProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨9, by decide⟩), .push 2 2208, .op .EQ, .push 2 4589, .op .JUMPI]

def h1Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .push 2 2208, .op .EQ, .push 2 4589, .op .JUMPI]

def h1FallProgram : List Instr := [.push 2 5072, .op .JUMP]

def h1Block : Block Artifact.submissionArtifact .Osaka 4576 h1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3614 5 4576 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

def h1FallBlock : Block Artifact.submissionArtifact .Osaka 4585 h1FallProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3619 2 4585 h1FallProgram
    (by decide) (by rfl) (by rfl) (by decide)

def h2Block : Block Artifact.submissionArtifact .Osaka 4242 hookProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3367 6 4242 hookProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4589 = true :=
  Artifact.isValidJumpDest_index 3621 (by rfl)

theorem jumpDestH2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4242 = true :=
  Artifact.isValidJumpDest_index 3367 (by rfl)

theorem jumpDestRow : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4268 = true :=
  Artifact.isValidJumpDest_index 3383 (by rfl)

theorem cond_four : UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2208)) := by decide

theorem cond_eight : ¬ UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2336)) := by decide

theorem cond_four' : UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2208)) := by decide

theorem cond_eight' : ¬ UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2336)) := by decide

/-! ## 判别块的运行 -/

theorem run_hookTaken (pc0 : Nat) (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (htl : tl = UInt256.ofNat 2208) :
    runInstructions hookProgram
      (frameAt pc0 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4589 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond := cond_four
  have hcond' := cond_four'
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, htl, pcR4, hc16, hc17, hc18, hc19, hcond, hcond', hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Taken (pc0 : Nat) (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (htl : tl = UInt256.ofNat 2208) :
    runInstructions h1Program
      (frameAt pc0 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4589 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond := cond_four
  have hcond' := cond_four'
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, htl, pcR4, hc16, hc17, hc18, hc19, hcond, hcond', hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Fall (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (htl : tl = UInt256.ofNat 2336) :
    runInstructions h1Program
      (frameAt pcH1 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcH1Fall s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond := cond_eight
  have hcond' := cond_eight'
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, htl, pcH1, pcH1Fall, hc16, hc17, hc18, hc19, hcond, hcond', List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h2Fall (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (htl : tl = UInt256.ofNat 2336) :
    runInstructions hookProgram
      (frameAt pcH2 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcAgain s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond := cond_eight
  have hcond' := cond_eight'
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, htl, pcH2, pcAgain, hc16, hc17, hc18, hc19, hcond, hcond', List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1FallJump (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1FallProgram
      (frameAt pcH1Fall s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt 5072 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 5072 = true := by
    rw [hcode]; exact Artifact.isValidJumpDest_index 4052 (by rfl)
  simp [h1FallProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH1Fall, hc16, hc17, hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## 作为 gas 步 -/

section
variable (s : State) (mem : ByteArray)
  (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
  (hcap : rest.length ≤ 1004) (hrun : s.halt = .Running)
  (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
  (hfork : s.fork = .Osaka)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)

/-- H1，`n = 4`：跳进 R4。 -/
def gasSteps_h1Taken (n : Nat) (hn : n = 4) (htl : tl = UInt256.ofNat 2208) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Taken pcH1 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode htl) rfl
    hcode hfork hrun hnp

/-- H2，`n = 4`：CSUB 返回后直接进下一轮 R4。 -/
def gasSteps_h2Taken (n : Nat) (hn : n = 4) (htl : tl = UInt256.ofNat 2208) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH2 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h2Block
    (run_hookTaken pcH2 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode htl) rfl
    hcode hfork hrun hnp

/-- H1，`n = 8`：落空并跳回行头。 -/
def gasSteps_h1Fall (n : Nat) (hn : n = 8) (htl : tl = UInt256.ofNat 2336) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt 5072 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact (SquareRow.stepsOf h1Block
    (run_h1Fall s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap htl) rfl
    hcode hfork hrun hnp).trans
    (SquareRow.stepsOf h1FallBlock
      (run_h1FallJump s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
      hcode hfork hrun hnp)

/-- H2，`n = 8`：落空进 `again`。 -/
def gasSteps_h2Fall (n : Nat) (hn : n = 8) (htl : tl = UInt256.ofNat 2336) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH2 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcAgain s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h2Block
    (run_h2Fall s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap htl) rfl
    hcode hfork hrun hnp

end

end Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
