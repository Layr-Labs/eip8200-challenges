import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordBitsFourCore
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordStep
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.WordBitsFour
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper
open WindowTwentyOneBinding WordStep WordBitsFourCore
open WindowNibbleKernel

abbrev BoundBlock := Block CycleSubmission.Artifact.artifact .Osaka

def lift {pc : Nat} {program : List Instr} (block : BoundBlock pc program)
    (s : State) (hs : Frame s) (stack : List UInt256) (t : State)
    (hrun : runInstructions program (stW s pc stack) = some t) :
    GasSteps (stW s pc stack) t :=
  block.steps ⟨by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; decide,
    hs.code, hs.fork, hs.halt, hs.np⟩ rfl hrun

theorem lift_cost {pc : Nat} {program : List Instr} (block : BoundBlock pc program)
    (s : State) (hs : Frame s) (stack : List UInt256) (t : State)
    (hrun : runInstructions program (stW s pc stack) = some t) (work : Nat)
    (hfree : ∀ located ∈ block.path, Meter.CopyFree located.instruction)
    (hcost : Meter.runLocatedBlockStaticCost block.path = work)
    (hactive : s.activeWords = t.activeWords) :
    (lift block s hs stack t hrun).cost = work := by
  have hraw : runInstructions (block.path.map Located.instruction) (stW s pc stack) = some t := by
    rw [block.instructions_eq]; exact hrun
  have hsize : CycleSubmission.Artifact.artifact.code.size < 2^256 := by
    change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; decide
  have hresult := WindowTwentyOneLocated.run_linear block.path _ (stW s pc stack) t
    hsize block.layout rfl hs.halt hraw
  unfold lift Block.steps
  rw [runLocatedBlock_sound_cost]
  exact blockCostW block.path work hresult hs.fork hfree hcost hactive

/-- The single bit body at pc 2454 (instruction indices 1948 to 1966). -/
def bodyBlock : BoundBlock 3998 (bodyProgram 7) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3090 19 3998 (bodyProgram 7) (by decide) (by rfl) (by rfl) (by rfl)

/-- The body head `JUMPDEST` at pc 2453 (index 1947), the target of the loop control. -/
def startBlock : BoundBlock 3997 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3089 1 3997 ([.op .JUMPDEST]) (by decide) (by rfl) (by rfl) (by rfl)

/-- The loop control at pc 2476 (indices 1967 to 1974). -/
def controlBlock : BoundBlock 4020 (controlProgram) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3109 8 4020 (controlProgram) (by decide) (by rfl) (by rfl) (by rfl)

variable (s : State) (rest : List UInt256)
  (Bm1 byte offset outerW acc base m : UInt256) (hs : Frame s)

/-- The body with the loop counter symbolic: it selects bit `7 - counter`. -/
def body (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3998 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 4020 ([Bm1,counter,byte,offset,outerW,stepValue 7 counter Bm1 byte acc m,base,m] ++ rest)) :=
  lift bodyBlock s hs _ _ (by
    simpa only [stW, framed, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.ofNat_add_mod] using
      run_body s 3998 7 Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem body_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (body s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 68 := by
  unfold body
  apply lift_cost _ _ _ _ _ _ 68 (by decide) (by rfl) (by rfl)

def start (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3997 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3998 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) :=
  lift startBlock s hs _ _ (run_start s Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem start_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (start s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 1 := by
  unfold start
  apply lift_cost _ _ _ _ _ _ 1 (by decide) (by rfl) (by rfl)

/-- The loop control with the counter at `c < 8`: back to the body head for
`c < 7`, otherwise on to the exit at 2413; the counter becomes `c + 1`. -/
def control (hrest : rest.length < 1000) (c : Nat) (hc : c < 8) :
    GasSteps (stW s 4020 ([Bm1,UInt256.ofNat c,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s (if c < 7 then 3997 else 4032)
        ([Bm1,UInt256.ofNat (c+1),byte,offset,outerW,acc,base,m] ++ rest)) :=
  lift controlBlock s hs _ _ (by
    have hj : Decode.isValidJumpDest s.executionEnv.code 3997 = true := by
      rw [hs.code]; exact CycleSubmission.Global.Binding.jumpDest 3089 (by rfl)
    simpa only [stW, framed, apply_ite UInt256.ofNat, Challenge.EvmProof.Word.literal_eq_ofNat] using
      run_control s Bm1 byte offset outerW acc base m rest c hc (Nat.le_of_lt hrest) hj)

@[simp] theorem control_cost (hrest : rest.length < 1000) (c : Nat) (hc : c < 8) :
    (control s rest Bm1 byte offset outerW acc base m hs hrest c hc).cost = 31 := by
  unfold control
  apply lift_cost _ _ _ _ _ _ 31 (by decide) (by rfl) (by rfl)

end CycleSubmission.Global.WordBitsFour
