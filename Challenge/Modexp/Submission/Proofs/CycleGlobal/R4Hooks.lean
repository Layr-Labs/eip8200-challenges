import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineTrace
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareRow
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareLoopBlocks
import Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory

noncomputable section
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

namespace CycleSubmission.Global.Fast.R4Hooks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached
open Challenge.EvmProof

def pcH1 : Nat := 3743
def pcH1Fall : Nat := 3751
def pcR4 : Nat := 4037

def h1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .push 2 3768, .op .JUMPI]

def h1Block : Block CycleSubmission.Artifact.artifact .Osaka 3743 h1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2880 5 3743 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestR4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4037 = true :=
  R4InlineBlocks.validJump5615

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
      (CycleSubmission.Global.Fast.SquareLoopBlocks.frameAt pcH1 s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (CycleSubmission.Global.Fast.SquareLoopBlocks.frameAt pcH1Fall s mem 4 pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have hcond := cond_four
  have hcondL := cond_four_lit
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    CycleSubmission.Global.Fast.SquareLoopBlocks.frameAt, CycleSubmission.Global.Fast.SquareLoopBlocks.frameStack, hq, pcH1, pcH1Fall, capacity, Nat.add_assoc, hcond, hcondL, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## 作为 gas 步 -/

section
variable (s : State) (mem : ByteArray)
  (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
  (hcap : rest.length ≤ 1004) (hrun : s.halt = .Running)
  (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
  (hfork : s.fork = .Osaka)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)

/-- H1, `n = 4`: `q + 0x80 = 0` falls through to the one-time R4 initializer. -/
def gasSteps_h1Taken (n : Nat) (hn : n = 4) (hq : pbi = UInt256.ofNat (2^256 - 128)) :
    Challenge.EvmProof.GasSteps
      (CycleSubmission.Global.Fast.SquareLoopBlocks.frameAt pcH1 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (CycleSubmission.Global.Fast.SquareLoopBlocks.frameAt pcH1Fall s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  subst hn
  exact SquareRow.stepsOf h1Block
    (run_h1Four s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hq) rfl
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
      { s with pc := UInt256.ofNat 3751, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 3763, memory := R4RetainedMemory.initMemory s.memory, stack := x8 :: x7 :: x4 :: n3 :: x11 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  have hread : MachineState.readWord (R4RetainedMemory.initMemory s.memory) 0 = n3 := by
    rw [R4RetainedMemory.initMemory, Memory.readWord_writeBytes_disjoint _ _ 0 2080 (Or.inl (by decide))]
    exact hn3
  have hstore : State.activeWordsAfterUInt256 s 2080 32 = s.activeWords :=
    Monpro.activeWords_fix s 2080 32 (by decide) (by norm_num) hact
  have hl0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [entryProgram, runInstructions, Stepper.runInstr, List.exchange,
    R4RetainedMemory.initMemory, hread, hstore, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hl0, hn3,
    Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact, capacity, Nat.add_assoc]
  constructor
  · rw [Monpro.activeWordsAfter_fix _ 2080 32 (by decide) (by norm_num) hact]
    rw [Nat.mod_eq_of_lt (show s.activeWords.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 from s.activeWords.val.isLt)]
    exact Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  · exact hread

def resumeProgram : List Instr := [.op .JUMPDEST]
theorem run_resume (s : State) (rest : List UInt256) (hcap : rest.length < 1024) :
    runInstructions resumeProgram { s with pc := UInt256.ofNat 3763, stack := rest } =
    some { s with pc := UInt256.ofNat 3764, stack := rest } := by
  simp [resumeProgram, runInstructions, Stepper.runInstr, Word.succ_ofNat_mod, hcap]


def entryBlock : Block CycleSubmission.Artifact.artifact .Osaka 3751 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2885 10 3751 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def resumeBlock : Block CycleSubmission.Artifact.artifact .Osaka 3763 resumeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2895 1 3763 resumeProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- Initialize the carry word once and retain the six reduction constants on the stack. -/
def gasSteps_entry (s : State)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 n3 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 999)
    (hn3 : MachineState.readWord s.memory 0 = n3) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      { s with pc := UInt256.ofNat 3751, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest }
      { s with pc := UInt256.ofNat 4037, memory := R4RetainedMemory.initMemory s.memory, stack := x8 :: x7 :: x4 :: n3 :: x11 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0 :: x15 :: rest } := by
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
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps { s with pc := UInt256.ofNat 3763, stack := rest }
      { s with pc := UInt256.ofNat 3764, stack := rest } := by
  exact SquareRow.stepsOf resumeBlock (run_resume s rest hcap) rfl hcode hfork hrun hnp

end CycleSubmission.Global.Fast.R4Hooks
