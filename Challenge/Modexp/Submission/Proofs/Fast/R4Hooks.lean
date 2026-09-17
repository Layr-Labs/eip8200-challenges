import Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# R4 的两个挂钩点

两处判别块 `DUP7 PUSH2 l2Target(4) EQ PUSH2 r4 JUMPI`（H2 前有 `JUMPDEST`）：帧的第 7 槽是
`l2Target n`，`n = 4` 时跳进 R4，`n = 8` 时落空。

* H1（staged-entry 之后）：落空后 `PUSH2 sq_row JUMP` 回到行头；
* H2（CSUB 返回点）：落空后紧接 `again`。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Hooks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareLoopBlocks

def pcH1 : Nat := 4381
def pcH1Fall : Nat := 4390
def pcR4 : Nat := 4394

/-- 判别块。 -/
def hookProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .push 2 5460, .op .EQ, .push 2 4394, .op .JUMPI]

def h1Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .push 2 5460, .op .EQ, .push 2 4394, .op .JUMPI]

def h1FallProgram : List Instr := [.push 2 4889, .op .JUMP]

def h1Block : Block Artifact.submissionArtifact .Osaka 4381 h1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3284 5 4381 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

def h1FallBlock : Block Artifact.submissionArtifact .Osaka 4390 h1FallProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3289 2 4390 h1FallProgram
    (by decide) (by rfl) (by rfl) (by decide)

def h2Block : Block Artifact.submissionArtifact .Osaka 4039 hookProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3037 6 4039 hookProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4394 = true :=
  Artifact.isValidJumpDest_index 3293 (by rfl)

theorem jumpDestH2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4039 = true :=
  Artifact.isValidJumpDest_index 3039 (by rfl)

theorem jumpDestRow : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4065 = true :=
  Artifact.isValidJumpDest_index 3055 (by rfl)

theorem cond_four : UInt256.isTrue ((UInt256.ofNat 5460).eq (l2Target 4)) := by decide

theorem cond_eight : ¬ UInt256.isTrue ((UInt256.ofNat 5460).eq (l2Target 8)) := by decide

theorem cond_four' : UInt256.isTrue ((UInt256.ofNat 5460).eq (UInt256.ofNat 5460)) := by decide

theorem cond_eight' : ¬ UInt256.isTrue ((UInt256.ofNat 5460).eq (UInt256.ofNat 3668)) := by decide

/-! ## 判别块的运行 -/

theorem run_hookTaken (pc0 : Nat) (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions hookProgram
      (frameAt pc0 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4394 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond := cond_four
  have hcond' := cond_four'
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcR4, hc16, hc17, hc18, hc19, hcond, hcond', hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Taken (pc0 : Nat) (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1Program
      (frameAt pc0 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4394 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond := cond_four
  have hcond' := cond_four'
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcR4, hc16, hc17, hc18, hc19, hcond, hcond', hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Fall (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) :
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
    frameAt, frameStack, pcH1, pcH1Fall, hc16, hc17, hc18, hc19, hcond, hcond', List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h2Fall (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) :
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
    frameAt, frameStack, pcH2, pcAgain, hc16, hc17, hc18, hc19, hcond, hcond', List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1FallJump (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1FallProgram
      (frameAt pcH1Fall s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt 4889 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4889 = true := by
    rw [hcode]; exact R8RowZero.jumpDest
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
def gasSteps_h1Taken (n : Nat) (hn : n = 4) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Taken pcH1 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
    hcode hfork hrun hnp

/-- H2，`n = 4`：CSUB 返回后直接进下一轮 R4。 -/
def gasSteps_h2Taken (n : Nat) (hn : n = 4) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH2 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h2Block
    (run_hookTaken pcH2 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
    hcode hfork hrun hnp

/-- H1，`n = 8`：落空并跳回行头。 -/
def gasSteps_h1Fall (n : Nat) (hn : n = 8) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt 4889 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact (SquareRow.stepsOf h1Block
    (run_h1Fall s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap) rfl
    hcode hfork hrun hnp).trans
    (SquareRow.stepsOf h1FallBlock
      (run_h1FallJump s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
      hcode hfork hrun hnp)

/-- H2，`n = 8`：落空进 `again`。 -/
def gasSteps_h2Fall (n : Nat) (hn : n = 8) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH2 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcAgain s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h2Block
    (run_h2Fall s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap) rfl
    hcode hfork hrun hnp

end

end Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
