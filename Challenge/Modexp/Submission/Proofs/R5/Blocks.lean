import Challenge.Modexp.Submission.Proofs.Prepared.OverlapFinalReturn
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Prepared.R5CachedSuffix
import Challenge.Modexp.Submission.Proofs.R5.SquareRun
import Challenge.Modexp.Submission.Proofs.R5.ProductRun
import Challenge.Modexp.Submission.Proofs.R5.ExecNorm
import Challenge.Modexp.Submission.Proofs.Prepared.R5CachedPrologue
import Challenge.Modexp.Submission.Proofs.R5.ConstantFold
import Challenge.Modexp.Submission.Proofs.Cycle.Return
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.R5.Blocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open WindowTwentyOneBinding WindowTwentyOneSlice
open CycleSubmission
def squareBlock : Block Artifact.artifact .Osaka 8814 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6635 471 8814 SquareRun.sqProgram
    (by change 6635+471 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg0Block : Block Artifact.artifact .Osaka 9437 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7108 67 9437 ProductRun.prSeg0Program
    (by change 7108+67 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg1Block : Block Artifact.artifact .Osaka 9512 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7175 155 9512 ProductRun.prSeg1Program
    (by change 7175+155 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg2Block : Block Artifact.artifact .Osaka 9685 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7330 110 9685 ProductRun.prSeg2Program
    (by change 7330+110 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg3Block : Block Artifact.artifact .Osaka 9808 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7440 265 9808 ProductRun.prSeg3Program
    (by change 7440+265 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def proSegBlock : Block Artifact.artifact .Osaka 8600 R5CachePrefixNew.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6530 83 8600 R5CachePrefixNew.program
    (by change 6530+83 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl4712Program : List Instr := [
  .push 2 8814,
   .op .JUMPI]
def ctl4712Block : Block Artifact.artifact .Osaka 9433 ctl4712Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7106 2 9433 ctl4712Program
    (by change 7106+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl4800Program : List Instr := [
  ]
def ctl4800Block : Block Artifact.artifact .Osaka 9512 ctl4800Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7175 0 9512 ctl4800Program
    (by change 7175+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl3433Program : List Instr := [
  ]
def ctl3433Block : Block Artifact.artifact .Osaka 9685 ctl3433Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7330 0 9685 ctl3433Program
    (by change 7330+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl3901Program : List Instr := [
  ]
def ctl3901Block : Block Artifact.artifact .Osaka 9808 ctl3901Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7440 0 9808 ctl3901Program
    (by change 7440+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normBlock : Block Artifact.artifact .Osaka 10191 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7705 4 10191 ExecNorm.normProgram
    (by change 7705+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5188Program : List Instr := [
  .push 2 10279,
   .op .JUMPI]
def ctl5188Block : Block Artifact.artifact .Osaka 10195 ctl5188Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7709 2 10195 ctl5188Program
    (by change 7709+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def blk5192Block : Block Artifact.artifact .Osaka 10199 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7711 51 10199 ExecNorm.blk5192Program
    (by change 7711+51 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5261Program : List Instr := [
  .push 2 10273,
   .op .JUMPI]
def ctl5261Block : Block Artifact.artifact .Osaka 10255 ctl5261Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7762 2 10255 ctl5261Program
    (by change 7762+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def blk5265Block : Block Artifact.artifact .Osaka 10259 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7764 10 10259 ExecNorm.blk5265Program
    (by change 7764+10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5275Program : List Instr := [
  .push 2 10191,
   .op .JUMP]
def ctl5275Block : Block Artifact.artifact .Osaka 10269 ctl5275Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7774 2 10269 ctl5275Program
    (by change 7774+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def negBlock : Block Artifact.artifact .Osaka 10273 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7776 6 10273 ExecNorm.negProgram
    (by change 7776+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def doneBlock : Block Artifact.artifact .Osaka 10279 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7782 11 10279 ExecNorm.doneProgram
    (by change 7782+11 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5330Program : List Instr := OverlapFinalReturn.program5
def ctl5330Block : Block Artifact.artifact .Osaka 10294 ctl5330Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7793 3 10294 ctl5330Program
    (by change 7793+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5464Program : List Instr := [
  .push 1 207,
   .op .JUMPI]
def ctl5464Block : Block Artifact.artifact .Osaka 8781 ctl5464Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6613 2 8781 ctl5464Program
    (by change 6613+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def blk5467Block : Block Artifact.artifact .Osaka 8784 R5CachedSuffix.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6615 20 8784 R5CachedSuffix.program
    (by change 6615+20 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5502Program : List Instr := [
  ]
def ctl5502Block : Block Artifact.artifact .Osaka 8814 ctl5502Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6635 0 8814 ctl5502Program
    (by change 6635+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 134 (by rfl)
theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 9512 = true :=
  CycleSubmission.Global.Binding.jumpDest 7175 (by rfl)
theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 8814 = true :=
  CycleSubmission.Global.Binding.jumpDest 6635 (by rfl)
theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 10191 = true :=
  CycleSubmission.Global.Binding.jumpDest 7705 (by rfl)
theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 10273 = true :=
  CycleSubmission.Global.Binding.jumpDest 7776 (by rfl)
theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 10279 = true :=
  CycleSubmission.Global.Binding.jumpDest 7782 (by rfl)
theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 8600 = true :=
  CycleSubmission.Global.Binding.jumpDest 6530 (by rfl)
theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8814 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 9433,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 9437 else UInt256.ofNat 8814),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9433,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 9437 else UInt256.ofNat 8814),stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 9433,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))
theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (_hvalid : Decode.isValidJumpDest s.executionEnv.code 9512 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 9512,stack := rest} =
      some {s with pc := UInt256.ofNat 9512,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,_hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9512,stack := rest} {s with pc := UInt256.ofNat 9512,stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 9512,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))
theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 9685,stack := rest} =
      some {s with pc := UInt256.ofNat 9685,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9685,stack := rest} {s with pc := UInt256.ofNat 9685,stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 9685,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap)
theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 9808,stack := rest} =
      some {s with pc := UInt256.ofNat 9808,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9808,stack := rest} {s with pc := UInt256.ofNat 9808,stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 9808,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap)
theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10279 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 10195,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 10199 else UInt256.ofNat 10279),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10195,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 10199 else UInt256.ofNat 10279),stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 10195,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))
theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10273 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 10255,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 10259 else UInt256.ofNat 10273),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10255,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 10259 else UInt256.ofNat 10273),stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 10255,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))
theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10191 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 10269,stack := rest} =
      some {s with pc := UInt256.ofNat 10191,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10269,stack := rest} {s with pc := UInt256.ofNat 10191,stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 10269,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))
def ctl5330_result (s : State) (rest : List UInt256) : State := OverlapFinalReturn.result5 s rest
theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
 (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions ctl5330Program {s with pc := UInt256.ofNat 10294,stack := rest} =
 some (ctl5330_result s rest) := OverlapFinalReturn.run5 s rest (by omega) hact
noncomputable def ctl5330_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10294,stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 10294,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)
theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 8781,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 8784 else UInt256.ofNat 207),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 8781,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 8784 else UInt256.ofNat 207),stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 8781,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))
theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (_hvalid : Decode.isValidJumpDest s.executionEnv.code 8814 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 8814,stack := rest} =
      some {s with pc := UInt256.ofNat 8814,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,_hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 8814,stack := rest} {s with pc := UInt256.ofNat 8814,stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 8814,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))
end CycleSubmission.R5.Blocks
