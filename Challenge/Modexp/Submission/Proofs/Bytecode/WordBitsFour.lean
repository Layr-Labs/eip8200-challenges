import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFourCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFour
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper
open WindowTwentyOneBinding WordStep WordBitsFourCore
open WindowNibbleKernel

abbrev BoundBlock := Block Artifact.submissionArtifact .Osaka

def lift {pc : Nat} {program : List Instr} (block : BoundBlock pc program)
    (s : State) (hs : Frame s) (stack : List UInt256) (t : State)
    (hrun : runInstructions program (stW s pc stack) = some t) :
    GasSteps (stW s pc stack) t :=
  block.steps ⟨by change submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
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
  have hsize : Artifact.submissionArtifact.code.size < 2^256 := by
    change submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide
  have hresult := WindowTwentyOneLocated.run_linear block.path _ (stW s pc stack) t
    hsize block.layout rfl hs.halt hraw
  unfold lift Block.steps
  rw [runLocatedBlock_sound_cost]
  exact blockCostW block.path work hresult hs.fork hfree hcost hactive

def bodyBlock0 : BoundBlock 3084 (bodyProgram 7) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2335 19 3084
    (bodyProgram 7) (by decide) (by rfl) (by rfl) (by rfl)

def bodyBlock1 : BoundBlock 3106 (bodyProgram 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2354 19 3106
    (bodyProgram 6) (by decide) (by rfl) (by rfl) (by rfl)

def bodyBlock2 : BoundBlock 3128 (bodyProgram 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2373 19 3128
    (bodyProgram 5) (by decide) (by rfl) (by rfl) (by rfl)

def bodyBlock3 : BoundBlock 3150 (bodyProgram 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2392 19 3150
    (bodyProgram 4) (by decide) (by rfl) (by rfl) (by rfl)

def startBlock : BoundBlock 3083 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2334 1 3083
    ([.op .JUMPDEST]) (by decide) (by rfl) (by rfl) (by rfl)

def controlBlock : BoundBlock 3172 (controlProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2411 9 3172
    (controlProgram) (by decide) (by rfl) (by rfl) (by rfl)

def resetBlock : BoundBlock 3185 (resetProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2420 4 3185
    (resetProgram) (by decide) (by rfl) (by rfl) (by rfl)

variable (s : State) (rest : List UInt256)
  (Bm1 byte offset outerW acc base m : UInt256) (hs : Frame s)

def body0 (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3084 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3106 ([Bm1,counter,byte,offset,outerW,stepValue 7 counter Bm1 byte acc m,base,m] ++ rest)) :=
  lift bodyBlock0 s hs _ _ (by
    simpa only [stW, framed, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.ofNat_add_mod] using
      run_body s 3084 7 Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem body0_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (body0 s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 68 := by
  unfold body0
  apply lift_cost _ _ _ _ _ _ 68 (by decide) (by rfl) (by rfl)

def body1 (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3106 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3128 ([Bm1,counter,byte,offset,outerW,stepValue 6 counter Bm1 byte acc m,base,m] ++ rest)) :=
  lift bodyBlock1 s hs _ _ (by
    simpa only [stW, framed, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.ofNat_add_mod] using
      run_body s 3106 6 Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem body1_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (body1 s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 68 := by
  unfold body1
  apply lift_cost _ _ _ _ _ _ 68 (by decide) (by rfl) (by rfl)

def body2 (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3128 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3150 ([Bm1,counter,byte,offset,outerW,stepValue 5 counter Bm1 byte acc m,base,m] ++ rest)) :=
  lift bodyBlock2 s hs _ _ (by
    simpa only [stW, framed, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.ofNat_add_mod] using
      run_body s 3128 5 Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem body2_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (body2 s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 68 := by
  unfold body2
  apply lift_cost _ _ _ _ _ _ 68 (by decide) (by rfl) (by rfl)

def body3 (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3150 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3172 ([Bm1,counter,byte,offset,outerW,stepValue 4 counter Bm1 byte acc m,base,m] ++ rest)) :=
  lift bodyBlock3 s hs _ _ (by
    simpa only [stW, framed, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.ofNat_add_mod] using
      run_body s 3150 4 Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem body3_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (body3 s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 68 := by
  unfold body3
  apply lift_cost _ _ _ _ _ _ 68 (by decide) (by rfl) (by rfl)

def start (hrest : rest.length < 1000) (counter : UInt256) :
    GasSteps (stW s 3083 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3084 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) :=
  lift startBlock s hs _ _ (run_start s Bm1 counter byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem start_cost (hrest : rest.length < 1000) (counter : UInt256) :
    (start s rest Bm1 byte offset outerW acc base m hs hrest counter).cost = 1 := by
  unfold start
  apply lift_cost _ _ _ _ _ _ 1 (by decide) (by rfl) (by rfl)

def control (hrest : rest.length < 1000) (c : Nat) (hc : c = 0 ∨ c = 4) :
    GasSteps (stW s 3172 ([Bm1,UInt256.ofNat c,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s (if c = 0 then 3083 else 3185)
        ([Bm1,UInt256.ofNat (c+4),byte,offset,outerW,acc,base,m] ++ rest)) :=
  lift controlBlock s hs _ _ (by
    have hj : Decode.isValidJumpDest s.executionEnv.code 3083 = true := by
      rw [hs.code]; exact Artifact.isValidJumpDest_index 2334 (by rfl)
    simpa only [stW, framed, apply_ite UInt256.ofNat, Challenge.EvmProof.Word.literal_eq_ofNat] using
      run_control s Bm1 byte offset outerW acc base m rest c hc (Nat.le_of_lt hrest) hj)

@[simp] theorem control_cost (hrest : rest.length < 1000) (c : Nat) (hc : c = 0 ∨ c = 4) :
    (control s rest Bm1 byte offset outerW acc base m hs hrest c hc).cost = 34 := by
  unfold control
  apply lift_cost _ _ _ _ _ _ 34 (by decide) (by rfl) (by rfl)

def reset (hrest : rest.length < 1000) :
    GasSteps (stW s 3185 ([Bm1,8,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 3189 ([Bm1,0,byte,offset,outerW,acc,base,m] ++ rest)) :=
  lift resetBlock s hs _ _ (run_reset s Bm1 byte offset outerW acc base m rest (Nat.le_of_lt hrest))

@[simp] theorem reset_cost (hrest : rest.length < 1000) :
    (reset s rest Bm1 byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold reset
  apply lift_cost _ _ _ _ _ _ 10 (by decide) (by rfl) (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFour
