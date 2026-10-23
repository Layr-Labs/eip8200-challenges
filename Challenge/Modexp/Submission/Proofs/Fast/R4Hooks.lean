import Challenge.Modexp.Submission.Proofs.Fast.R4InlineTrace
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
import Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Width dispatch before the first square. The entry leaves the row pointer word on top (zneg2):
`-0x100` jumps to the eight-limb row 0 (`q + 0x80 ≠ 0`). The R4 marker `-0x80`
falls through to one-time initialization at4557, which clears carry and retains
constants until the loop finishes. Repeated R4 rounds resume at4569.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Hooks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareLoopBlocks
open Challenge.EvmProof

def pcH1 : Nat := 4260
def pcH1Fall : Nat := 4268
def pcR4 : Nat := 8998

def h1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .push 2 5615, .op .JUMPI]

def h1Block : Block Artifact.submissionArtifact .Osaka 4260 h1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3313 5 4260 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8998 = true :=
  R4InlineBlocks.validJump5615

theorem jumpDestRow : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5297 = true :=
  Artifact.isValidJumpDest_index 4220 (by rfl)

theorem jumpDestCRT : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5615 = true :=
  Artifact.isValidJumpDest_index 4488 (by rfl)

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

theorem run_h1Eight (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hq : pbi = UInt256.ofNat (2^256 - 256)) :
    runInstructions h1Program
      (frameAt pcH1 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt 5615 s mem 8 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 5615 = true := by
    rw [hcode]; exact jumpDestCRT
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

/-- H1, `n = 4`: `q + 0x80 = 0` falls through to the one-time R4 initializer. -/
def gasSteps_h1Taken (n : Nat) (hn : n = 4) (hq : pbi = UInt256.ofNat (2^256 - 128)) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcH1Fall s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Four s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hq) rfl
    hcode hfork hrun hnp

/-- H1, `n = 8`: `q + 0x80 ≠ 0` jumps to the eight-limb row 0. -/
def gasSteps_h1Fall (n : Nat) (hn : n = 8) (hq : pbi = UInt256.ofNat (2^256 - 256)) :
    Challenge.EvmProof.GasSteps
      (frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt 5615 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Eight s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode hq) rfl
    hcode hfork hrun hnp

end

def entryProgram : List Instr :=
  [.op (.Swap ⟨13, by decide⟩), .op (.Dup ⟨11, by decide⟩), .push 0 0, .op (.Dup ⟨0, by decide⟩), .push 2 2080, .op .MSTORE, .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨12, by decide⟩)]

theorem run_entry (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 n3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999)
    (hn3 : MachineState.readWord s.memory 0 = n3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram
      { s with pc := UInt256.ofNat 4268, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4280, memory := R4RetainedMemory.initMemory s.memory, stack := x8 :: x7 :: x4 :: n3 :: x11 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0 :: x15 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hread : MachineState.readWord (R4RetainedMemory.initMemory s.memory) 0 = n3 := by
    rw [R4RetainedMemory.initMemory, Memory.readWord_writeBytes_disjoint _ _ 0 2080 (Or.inl (by decide))]
    exact hn3
  have hstore : State.activeWordsAfterUInt256 s 2080 32 = s.activeWords :=
    Monpro.activeWords_fix s 2080 32 (by decide) (by norm_num) hact
  have hl0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [entryProgram, runInstructions, Stepper.runInstr, List.exchange,
    R4RetainedMemory.initMemory, hread, hstore, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hl0, hn3,
    Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23]
  constructor
  · rw [Monpro.activeWordsAfter_fix _ 2080 32 (by decide) (by norm_num) hact]
    rw [Nat.mod_eq_of_lt (show s.activeWords.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 from s.activeWords.val.isLt)]
    exact Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  · exact hread

def resumeProgram : List Instr := [.op .JUMPDEST]
theorem run_resume (s : State) (rest : List UInt256) (hcap : rest.length < 1024) :
    runInstructions resumeProgram { s with pc := UInt256.ofNat 4280, stack := rest } =
    some { s with pc := UInt256.ofNat 4281, stack := rest } := by
  simp [resumeProgram, runInstructions, Stepper.runInstr, Word.succ_ofNat_mod, hcap]


def entryBlock : Block Artifact.submissionArtifact .Osaka 4268 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3318 10 4268 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def resumeBlock : Block Artifact.submissionArtifact .Osaka 4280 resumeProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3328 1 4280 resumeProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- Initialize the carry word once and retain the six reduction constants on the stack. -/
def gasSteps_entry (s : State)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 n3 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 999)
    (hn3 : MachineState.readWord s.memory 0 = n3) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      { s with pc := UInt256.ofNat 4268, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest }
      { s with pc := UInt256.ofNat 8998, memory := R4RetainedMemory.initMemory s.memory, stack := x8 :: x7 :: x4 :: n3 :: x11 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0 :: x15 :: rest } := by
  have ge := SquareRow.stepsOf entryBlock
    (run_entry s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 n3 rest hcap hn3 hact)
    rfl hcode hfork hrun hnp

  refine ge.trans ?_
  exact R4InlineTrace.gasSteps_entryBridge
    { s with memory := R4RetainedMemory.initMemory s.memory }
    (x8 :: x7 :: x4 :: n3 :: x11 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0 :: x15 :: rest)
    (by simp only [List.length_cons]; omega) hcode hfork hrun hnp

/-- The common first/repeated-row marker preserves the retained frame. -/
def gasSteps_resume (s : State) (rest : List UInt256) (hcap : rest.length < 1024)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps { s with pc := UInt256.ofNat 4280, stack := rest }
      { s with pc := UInt256.ofNat 4281, stack := rest } := by
  exact SquareRow.stepsOf resumeBlock (run_resume s rest hcap) rfl hcode hfork hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
