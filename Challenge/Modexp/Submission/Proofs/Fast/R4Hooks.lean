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

def pcH1 : Nat := 4503
def pcH1Fall : Nat := 4512
def pcR4 : Nat := 4516

/-- The width test (E5 at 4162 with its `JUMPDEST`, E7 at 4503): `DUP4 PUSH2 0x1000 LT
PUSH2 r4 JUMPI` reads the first-loop register `ent` (frame slot 4) and jumps into R4 iff
`4096 < ent` — the four-limb register (`l1Target 4 = 5302`) is above 4096, every
eight-limb value (`3510 + 37 i`) below.  The cell (slot 7) is no longer read here. -/
def hookProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨3, by decide⟩), .push 2 4096, .op .LT, .push 2 4516, .op .JUMPI]

def h1Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .push 2 4096, .op .LT, .push 2 4516, .op .JUMPI]

/-- The register value that takes the hook. -/
def WideEnt (ent : UInt256) : Prop := UInt256.isTrue (UInt256.lt (UInt256.ofNat 4096) ent)

instance decWideEnt (ent : UInt256) : Decidable (WideEnt ent) :=
  inferInstanceAs (Decidable (UInt256.isTrue (UInt256.lt (UInt256.ofNat 4096) ent)))

def h1FallProgram : List Instr := [.push 2 5013, .op .JUMP]

def h1Block : Block Artifact.submissionArtifact .Osaka 4503 h1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3561 5 4503 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

def h1FallBlock : Block Artifact.submissionArtifact .Osaka 4512 h1FallProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3566 2 4512 h1FallProgram
    (by decide) (by rfl) (by rfl) (by decide)

def h2Block : Block Artifact.submissionArtifact .Osaka 4162 hookProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3315 6 4162 hookProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4516 = true :=
  Artifact.isValidJumpDest_index 3568 (by rfl)

theorem jumpDestH2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4162 = true :=
  Artifact.isValidJumpDest_index 3315 (by rfl)

theorem jumpDestRow : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4190 = true :=
  Artifact.isValidJumpDest_index 3331 (by rfl)

theorem wideEnt_l1Target_four : WideEnt (l1Target 4) := by decide

theorem wideEnt_5302 : WideEnt (UInt256.ofNat 5302) := by decide

theorem not_wideEnt_l1Target_eight : ¬ WideEnt (l1Target 8) := by decide

theorem not_wideEnt_3510 : ¬ WideEnt (UInt256.ofNat 3510) := by decide

theorem not_wideEnt_3806 : ¬ WideEnt (UInt256.ofNat 3806) := by decide

/-! ## 判别块的运行 -/

theorem run_hookTaken (pc0 : Nat) (s : State) (mem : ByteArray)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hent : WideEnt ent) :
    runInstructions hookProgram
      (frameAt pc0 s mem 4 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4516 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond : UInt256.isTrue (UInt256.lt (UInt256.ofNat 4096) ent) := hent
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcR4, hc16, hc17, hc18, hc19, hcond, hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Taken (pc0 : Nat) (s : State) (mem : ByteArray)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hent : WideEnt ent) :
    runInstructions h1Program
      (frameAt pc0 s mem 4 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4516 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond : UInt256.isTrue (UInt256.lt (UInt256.ofNat 4096) ent) := hent
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcR4, hc16, hc17, hc18, hc19, hcond, hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Fall (s : State) (mem : ByteArray)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hent : ¬ WideEnt ent) :
    runInstructions h1Program
      (frameAt pcH1 s mem 8 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcH1Fall s mem 8 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond : ¬ UInt256.isTrue (UInt256.lt (UInt256.ofNat 4096) ent) := hent
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH1, pcH1Fall, hc16, hc17, hc18, hc19, hcond, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h2Fall (s : State) (mem : ByteArray)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hent : ¬ WideEnt ent) :
    runInstructions hookProgram
      (frameAt pcH2 s mem 8 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcAgain s mem 8 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond : ¬ UInt256.isTrue (UInt256.lt (UInt256.ofNat 4096) ent) := hent
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH2, pcAgain, hc16, hc17, hc18, hc19, hcond, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1FallJump (s : State) (mem : ByteArray)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1FallProgram
      (frameAt pcH1Fall s mem 8 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt 5013 s mem 8 pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 5013 = true := by
    rw [hcode]; exact R8RowZero.jumpDest
  simp [h1FallProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH1Fall, hc16, hc17, hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## 作为 gas 步 -/

section
variable (s : State) (mem : ByteArray)
  (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
  (hcap : rest.length ≤ 1004) (hrun : s.halt = .Running)
  (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
  (hfork : s.fork = .Osaka)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)

/-- H1，`n = 4`：跳进 R4。 -/
def gasSteps_h1Taken (n : Nat) (hn : n = 4) (hent : WideEnt ent) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Taken pcH1 s mem pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hent) rfl
    hcode hfork hrun hnp

/-- H2，`n = 4`：CSUB 返回后直接进下一轮 R4。 -/
def gasSteps_h2Taken (n : Nat) (hn : n = 4) (hent : WideEnt ent) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH2 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h2Block
    (run_hookTaken pcH2 s mem pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hent) rfl
    hcode hfork hrun hnp

/-- H1，`n = 8`：落空并跳回行头。 -/
def gasSteps_h1Fall (n : Nat) (hn : n = 8) (hent : ¬ WideEnt ent) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt 5013 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact (SquareRow.stepsOf h1Block
    (run_h1Fall s mem pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hent) rfl
    hcode hfork hrun hnp).trans
    (SquareRow.stepsOf h1FallBlock
      (run_h1FallJump s mem pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
      hcode hfork hrun hnp)

/-- H2，`n = 8`：落空进 `again`。 -/
def gasSteps_h2Fall (n : Nat) (hn : n = 8) (hent : ¬ WideEnt ent) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH2 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcAgain s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h2Block
    (run_h2Fall s mem pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hent) rfl
    hcode hfork hrun hnp

end

end Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
