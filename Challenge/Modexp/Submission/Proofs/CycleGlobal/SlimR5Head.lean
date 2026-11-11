import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareStagedEntry
import Challenge.Modexp.Submission.Proofs.CycleCaller.Blocks
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory
import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The width-4 head path, 2369 → 3751

The caller block at 2369, the common setup at 3181, the staged entry at 3728 and the width test
at 3743 are shared with width 8 and keep the leader's proofs (`Cios2Dispatch`,
`SquareStagedEntry`). The frame and the width-test block are copied from the retired
`SquareLoopBlocks`/`R4Hooks`. For width 4 the test falls through to 3751, where the r5 route
begins.
-/

namespace CycleSubmission.Global.SlimR5Head
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Monpro CiosCached StagedOperand

/-- The sixteen-word frame the shared setup leaves above `rest`. -/
def frameStack (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 3710, UInt256.ofNat 480, ent, m32, allOnes,
    MachineState.readWord mem 128, m64, m0, tl, m96, inv, UInt256.ofNat 0, aprev, pdst, ret] ++ rest

def frameAt (pc : Nat) (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat pc
    memory := mem
    stack := frameStack mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest}

def pcH1 : Nat := 3715
def pcEntry : Nat := 5197

def h1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .op .ISZERO, .push 2 5197, .op .JUMPI]

def h1Block : Block CycleSubmission.Artifact.artifact .Osaka 3715 h1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2809 6 3715 h1Program
    (by change 2809 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem cond_four : UInt256.isZero (UInt256.ofNat 128 + UInt256.ofNat (2^256 - 128)) = UInt256.ofNat 1 := by
  decide

theorem run_h1Four (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hq : pbi = UInt256.ofNat (2^256 - 128))
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5197 = true) :
    runInstructions h1Program (frameAt pcH1 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcEntry s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have hcond := cond_four
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, hq, pcH1, pcEntry, capacity, Nat.add_assoc, hcond, hvalid, UInt256.isTrue, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- Width 4: `q + 0x80 = 0`, the test jumps straight to the r5 prologue at 5334. -/
def gasSteps_h1 (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hq : pbi = UInt256.ofNat (2^256 - 128)) :
    GasSteps (frameAt pcH1 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (frameAt pcEntry s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) :=
  CycleSubmission.Global.Fast.SquareRow.stepsOf h1Block
    (run_h1Four s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hq
      (by rw [hcode]; exact CycleSubmission.CallerBlocks.valid5334)) rfl
    hcode hfork hrun hnp

def entryMemory (mem : ByteArray) : ByteArray :=
  SquarePartialClear.memory (stageW mem 2112 4)

theorem entryMemory_read (mem : ByteArray) (addr : Nat) (hd : addr + 32 ≤ 2048 ∨ 2240 ≤ addr) :
    MachineState.readWord (entryMemory mem) addr = MachineState.readWord mem addr := by
  rw [entryMemory, SquarePartialClear.readWord_outside _ addr (by omega),
    read_stageW_four_outside mem addr (by omega)]

theorem entryMemory_represents (mem : ByteArray) (a : Nat)
    (ha : Model.FastRepresents mem 2112 4 a) :
    Model.FastRepresents (entryMemory mem) 2112 4 a :=
  SquarePartialClear.fastRepresents_outside _ 2112 4 a (Or.inr (by decide))
    (represents_stageW_four mem 2112 4 a (Or.inr (Or.inr ⟨rfl, le_rfl⟩)) ha)

/-- The state at 3751 for exponent count `k`. -/
def entryState (s : State) (mem : ByteArray) (bsize esize k : Nat) : State :=
  frameAt pcEntry s (entryMemory mem) (CycleSubmission.Global.Fast.SquareStagedEntry.qWord 4) (UInt256.ofNat 3347)
    (UInt256.ofNat 0) (MachineState.readWord mem 2720)
    (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0) (UInt256.ofNat (k - 1)) (UInt256.ofNat 128)
    (CycleSubmission.Global.SlimFrames.outer mem 4 bsize esize 128)


end CycleSubmission.Global.SlimR5Head
