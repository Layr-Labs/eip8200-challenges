import Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Square-width dispatch at the initial and repeated entries

H1 uses XOR against the four-limb reduction entry: four limbs fall through to
R4, while eight limbs branch directly to the relocated row-zero helper.
H2 retains its EQ test: four limbs branch to R4 and eight limbs fall through
to the repeated staging block. Both preserve the complete square frame.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Hooks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareLoopBlocks

def pcH1 : Nat := 4797
def pcR4 : Nat := 4810

/-- 判别块。 -/
def hookProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .push 2 4183, .op .EQ, .push 2 4810, .op .JUMPI]

def h1Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .push 2 4183, .op .XOR, .push 6 4453, .op .JUMPI]

def h1Block : Block Artifact.submissionArtifact .Osaka 4797 h1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3625 5 4797 h1Program
    (by decide) (by rfl) (by rfl) (by decide)



def h2Block : Block Artifact.submissionArtifact .Osaka 4422 hookProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3340 6 4422 hookProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4810 = true :=
  Artifact.isValidJumpDest_index 3630 (by rfl)

theorem jumpDestH2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4422 = true :=
  Artifact.isValidJumpDest_index 3340 (by rfl)

theorem jumpDestRow : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4483 = true :=
  Artifact.isValidJumpDest_index 3388 (by rfl)

theorem cond_four : UInt256.isTrue ((UInt256.ofNat 4183).eq (l2Target 4)) := by decide

theorem cond_eight : ¬ UInt256.isTrue ((UInt256.ofNat 4183).eq (l2Target 8)) := by decide

theorem cond_four' : UInt256.isTrue ((UInt256.ofNat 4183).eq (UInt256.ofNat 4183)) := by decide

theorem cond_eight' : ¬ UInt256.isTrue ((UInt256.ofNat 4183).eq (UInt256.ofNat 4035)) := by decide

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
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4810 = true := by
    rw [hcode]; exact jumpDestR4
  have hcond := cond_four
  have hcond' := cond_four'
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcR4, hc16, hc17, hc18, hc19, hcond, hcond', hjd, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Taken (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1Program
      (frameAt pcH1 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcR4 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond : ¬ UInt256.isTrue ((UInt256.ofNat 4183).xor (l2Target 4)) := by decide
  have hcond' : ¬ UInt256.isTrue ((UInt256.ofNat 4183).xor (UInt256.ofNat 4183)) := by decide
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH1, pcR4, hc16, hc17, hc18, hc19, hcond, hcond', List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_h1Fall (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions h1Program
      (frameAt pcH1 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt 4453 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hcond : UInt256.isTrue ((UInt256.ofNat 4183).xor (l2Target 8)) := by decide
  have hcond' : UInt256.isTrue ((UInt256.ofNat 4183).xor (UInt256.ofNat 4035)) := by decide
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4453 = true := by
    rw [hcode]; exact R8RowZero.jumpDest
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, pcH1, hc16, hc17, hc18, hc19, hcond, hcond', hjd, List.exchange,
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
    (run_h1Taken s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
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
      (frameAt 4453 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Fall s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode) rfl
    hcode hfork hrun hnp

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
