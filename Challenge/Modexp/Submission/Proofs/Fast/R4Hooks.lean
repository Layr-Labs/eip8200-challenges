import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Width dispatch before the first square. The entry leaves the row pointer word on top (zneg2):
`-0x100` jumps to the eight-limb row 0 (`q + 0x80 ≠ 0`), the R4 marker `-0x80` falls through to
the jump into the dedicated R4 routine. The repeat
path needs no dispatch: each kernel exit pushes its own CSUB return
(4610 for R4, 5092 for the eight-limb row-0 head).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Hooks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareLoopBlocks

def pcH1 : Nat := 4283
def pcH1Fall : Nat := 4291
def pcR4 : Nat := 4295

def h1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .push 2 4839, .op .JUMPI]

def h1FallProgram : List Instr := [.push 2 4295, .op .JUMP]

def h1Block : Block Artifact.submissionArtifact .Osaka 4283 h1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3339 5 4283 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

def h1FallBlock : Block Artifact.submissionArtifact .Osaka 4291 h1FallProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3344 2 4291 h1FallProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4295 = true :=
  Artifact.isValidJumpDest_index 3346 (by rfl)

theorem jumpDestRow : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5320 = true :=
  Artifact.isValidJumpDest_index 4244 (by rfl)

theorem cond_four : ¬ UInt256.isTrue (UInt256.ofNat 128 + UInt256.ofNat (2^256 - 128)) := by decide

theorem cond_eight : UInt256.isTrue (UInt256.ofNat 128 + UInt256.ofNat (2^256 - 256)) := by decide

/-- `cond_four` after `simp` folds the sum: `ofNat (2^256)` as a literal (it is `0`). -/
theorem cond_four_lit : ¬ UInt256.isTrue (UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639936) := by decide

/-- `cond_eight` after `simp` folds the sum: `ofNat (2^256 - 128)` as a literal. -/
theorem cond_eight_lit : UInt256.isTrue (UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639808) := by decide

/-! ## 判别块的运行 -/

theorem run_h1Four (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hq : pbi = UInt256.ofNat (2^256 - 128)) :
    runInstructions h1Program
      (frameAt pcH1 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcH1Fall s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond := cond_four
  have hcondL := cond_four_lit
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, hq, pcH1, pcH1Fall, hc16, hc17, hc18, hc19, hcond, hcondL, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1FallJump (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1FallProgram
      (frameAt pcH1Fall s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4295 = true := by
    rw [hcode]; exact jumpDestR4
  simp [h1FallProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH1Fall, pcR4, hc16, hc17, hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Eight (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hq : pbi = UInt256.ofNat (2^256 - 256)) :
    runInstructions h1Program
      (frameAt pcH1 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt 4839 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4839 = true := by
    rw [hcode]; exact Artifact.isValidJumpDest_index 3832 (by rfl)
  have hcond := cond_eight
  have hcondL := cond_eight_lit
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, hq, pcH1, hc16, hc17, hc18, hc19, hcond, hcondL, hjd, List.exchange,
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

/-- H1, `n = 4`: `q + 0x80 = 0` falls through to the jump into R4. -/
def gasSteps_h1Taken (n : Nat) (hn : n = 4) (hq : pbi = UInt256.ofNat (2^256 - 128)) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcR4 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact (SquareRow.stepsOf h1Block
    (run_h1Four s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hq) rfl
    hcode hfork hrun hnp).trans
    (SquareRow.stepsOf h1FallBlock
      (run_h1FallJump s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
      hcode hfork hrun hnp)

/-- H1, `n = 8`: `q + 0x80 ≠ 0` jumps to the eight-limb row 0. -/
def gasSteps_h1Fall (n : Nat) (hn : n = 8) (hq : pbi = UInt256.ofNat (2^256 - 256)) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt 4839 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Eight s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hq) rfl
    hcode hfork hrun hnp

end

end Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
