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

namespace CycleSubmission.Global.R5Head
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
  [pbi, UInt256.ofNat 5297, MachineState.readWord mem 192, ent, m32, allOnes,
    MachineState.readWord mem 128, m64, m0, tl, m96, inv, UInt256.ofNat 0, aprev, pdst, ret] ++ rest

def frameAt (pc : Nat) (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat pc
    memory := mem
    stack := frameStack mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest}

def pcH1 : Nat := 3743
def pcEntry : Nat := 3751

def h1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .push 2 5506, .op .JUMPI]

def h1Block : Block CycleSubmission.Artifact.artifact .Osaka 3743 h1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2876 5 3743 h1Program
    (by decide) (by rfl) (by rfl) (by decide)

theorem cond_four : ¬ UInt256.isTrue (UInt256.ofNat 128 + UInt256.ofNat (2^256 - 128)) := by decide

theorem cond_four_lit : ¬ UInt256.isTrue (UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639936) := by decide

theorem run_h1Four (s : State) (mem : ByteArray)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hq : pbi = UInt256.ofNat (2^256 - 128)) :
    runInstructions h1Program (frameAt pcH1 s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (frameAt pcEntry s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have hcond := cond_four
  have hcondL := cond_four_lit
  simp [h1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    frameAt, frameStack, hq, pcH1, pcEntry, capacity, Nat.add_assoc, hcond, hcondL, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- Width 4: `q + 0x80 = 0`, the test falls through to 3751. -/
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
    (run_h1Four s mem pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hq) rfl
    hcode hfork hrun hnp

theorem call_run (s : State) (mem : ByteArray) (bsize esize k : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3212 = true) :
    runInstructions CycleSubmission.CallerBlocks.fixedProgram
        (FixedDirectStates.special s mem 4 bsize esize 128 k) =
      some (CycleSubmission.Global.Fast.Cios2Dispatch.commonState s mem
        (UInt256.ofNat 3728) 2112 512 (UInt256.ofNat (k-1)) (UInt256.ofNat 2519)
        (UInt256.ofNat k :: Exp.outer 4 bsize esize 128)) := by
  have hdec : UInt256.ofNat k - UInt256.ofNat 1 = UInt256.ofNat (k-1) := by
    interval_cases k <;> decide
  simp [CycleSubmission.CallerBlocks.fixedProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    FixedDirectStates.special, CycleSubmission.Global.Fast.Cios2Dispatch.commonState, Exp.outer, hdec, hjump,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

/-- The memory at 3751: the operand staged at 2112 and the accumulator rows cleared. -/
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
    (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
    (MachineState.readWord mem 96) (MachineState.readWord mem 96)
    (MachineState.readWord mem 64) (MachineState.readWord mem 32)
    (UInt256.ofNat (2112 + 32 * 4 - 32)) (UInt256.ofNat (k - 1)) (UInt256.ofNat 2519)
    (UInt256.ofNat k :: Exp.outer 4 bsize esize 128)

/-- From the width-4 special state to the r5 entry at 3751. -/
def gasSteps_head (s : State) (mem : ByteArray) (bsize esize k mi : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 4 bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hmachine : ((MachineState.readWord mem 96).toNat * mi + 1) % 2^256 = 0) :
    GasSteps (FixedDirectStates.special s mem 4 bsize esize 128 k)
      (entryState s mem bsize esize k) := by
  have head := CycleSubmission.CallerBlocks.fixedBlock.steps
    (s := FixedDirectStates.special s mem 4 bsize esize 128 k)
    (env.transfer rfl rfl) rfl (call_run s mem bsize esize k hk hk16
      (by rw [env.code]; exact CycleSubmission.CallerBlocks.valid3181))
  have hmiw : (MachineState.readWord mem 2720).toNat = mi := by
    rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  have hinvW : ((MachineState.readWord mem (32 * (2 + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0 := by
    rw [hmiw]; exact hmachine
  have hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1 := by
    rw [hf.minvW]
    intro h
    apply hmi1
    have h := congrArg UInt256.toNat h
    simpa only [Exp.toNat_ofNat_self hmi, Exp.toNat_ofNat_self (by decide : 1 < 2^256)] using h
  have g1 := CycleSubmission.Global.Fast.Cios2Dispatch.gasSteps_commonSetupSq s mem
    (UInt256.ofNat 3728) 2112 512 (2 + 2) (UInt256.ofNat (k - 1)) (UInt256.ofNat 2519)
    (UInt256.ofNat k :: Exp.outer 4 bsize esize 128) (by simp [Exp.outer])
    env.running env.code env.forkEq env.noPrecompile hact (Or.inl rfl) (by omega)
    (by decide) (by omega) hcds hf.s32 hf.ml (by simp [Exp.outer]) (by simp [Exp.outer])
    CycleSubmission.Global.Fast.SquareStagedEntry.jumpDest hguard
    (CiosInverseGuard.inverse_ne_zero _ _ hinvW)
  have g2 := CycleSubmission.Global.Fast.SquareStagedEntry.gasSteps_entry s
    (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) (2 + 2)
    (UInt256.ofNat 3347) (MachineState.readWord mem 32) (MachineState.readWord mem 64)
    (MachineState.readWord mem (16 * (2 + 2) + 32))
    (MachineState.readWord mem 224 :: MachineState.readWord mem 96 :: MachineState.readWord mem 2720 ::
      UInt256.ofNat 0 :: UInt256.ofNat (2112 + 32 * (2 + 2) - 32) ::
      UInt256.ofNat (k - 1) :: UInt256.ofNat 2519 :: UInt256.ofNat k :: Exp.outer 4 bsize esize 128)
    (by simp [Exp.outer]) env.running env.code env.forkEq env.noPrecompile hact
  have g3 := gasSteps_h1 s (SquarePartialClear.memory (stageW mem 2112 (2 + 2)))
    (CycleSubmission.Global.Fast.SquareStagedEntry.qWord (2 + 2)) (UInt256.ofNat 3347)
    (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
    (MachineState.readWord mem (16 * (2 + 2) + 32)) (MachineState.readWord mem 96)
    (MachineState.readWord mem 64) (MachineState.readWord mem 32)
    (UInt256.ofNat (2112 + 32 * (2 + 2) - 32)) (UInt256.ofNat (k - 1)) (UInt256.ofNat 2519)
    (UInt256.ofNat k :: Exp.outer 4 bsize esize 128) (by simp [Exp.outer])
    env.running env.code env.forkEq env.noPrecompile CycleSubmission.Global.Fast.SquareStagedEntry.qWord_four
  exact ((head.trans g1).trans g2).trans g3

end CycleSubmission.Global.R5Head
