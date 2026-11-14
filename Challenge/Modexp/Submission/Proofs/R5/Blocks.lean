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
def squareBlock : Block Artifact.artifact .Osaka 8811 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6693 471 8811 SquareRun.sqProgram
    (by change 6693+471 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg0Block : Block Artifact.artifact .Osaka 9434 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7166 67 9434 ProductRun.prSeg0Program
    (by change 7166+67 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg1Block : Block Artifact.artifact .Osaka 9509 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7233 155 9509 ProductRun.prSeg1Program
    (by change 7233+155 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg2Block : Block Artifact.artifact .Osaka 9682 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7388 110 9682 ProductRun.prSeg2Program
    (by change 7388+110 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def productSeg3Block : Block Artifact.artifact .Osaka 9805 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7498 268 9805 ProductRun.prSeg3Program
    (by change 7498+268 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def proSegBlock : Block Artifact.artifact .Osaka 8651 R5CachePrefixNew.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6582 89 8651 R5CachePrefixNew.program
    (by change 6582+89 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl4712Program : List Instr := [
  .push 2 8811,
   .op .JUMPI]
def ctl4712Block : Block Artifact.artifact .Osaka 9430 ctl4712Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7164 2 9430 ctl4712Program
    (by change 7164+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl4800Program : List Instr := [
  ]
def ctl4800Block : Block Artifact.artifact .Osaka 9509 ctl4800Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7233 0 9509 ctl4800Program
    (by change 7233+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl3433Program : List Instr := [
  ]
def ctl3433Block : Block Artifact.artifact .Osaka 9682 ctl3433Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7388 0 9682 ctl3433Program
    (by change 7388+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl3901Program : List Instr := [
  ]
def ctl3901Block : Block Artifact.artifact .Osaka 9805 ctl3901Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7498 0 9805 ctl3901Program
    (by change 7498+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normBlock : Block Artifact.artifact .Osaka 10104 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7766 4 10104 ExecNorm.normProgram
    (by change 7766+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5188Program : List Instr := [
  .push 2 10192,
   .op .JUMPI]
def ctl5188Block : Block Artifact.artifact .Osaka 10108 ctl5188Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7770 2 10108 ctl5188Program
    (by change 7770+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def blk5192Block : Block Artifact.artifact .Osaka 10112 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7772 51 10112 ExecNorm.blk5192Program
    (by change 7772+51 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5261Program : List Instr := [
  .push 2 10186,
   .op .JUMPI]
def ctl5261Block : Block Artifact.artifact .Osaka 10168 ctl5261Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7823 2 10168 ctl5261Program
    (by change 7823+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def blk5265Block : Block Artifact.artifact .Osaka 10172 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7825 10 10172 ExecNorm.blk5265Program
    (by change 7825+10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5275Program : List Instr := [
  .push 2 10104,
   .op .JUMP]
def ctl5275Block : Block Artifact.artifact .Osaka 10182 ctl5275Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7835 2 10182 ctl5275Program
    (by change 7835+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def negBlock : Block Artifact.artifact .Osaka 10186 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7837 6 10186 ExecNorm.negProgram
    (by change 7837+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def doneBlock : Block Artifact.artifact .Osaka 10192 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7843 35 10192 ExecNorm.doneProgram
    (by change 7843+35 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5330Program : List Instr := [
  .push 1 128,
   .push 0 0,
   .op .RETURN]
def ctl5330Block : Block Artifact.artifact .Osaka 10237 ctl5330Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7878 3 10237 ctl5330Program
    (by change 7878+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5464Program : List Instr := [
  .push 1 207,
   .op .JUMPI]
def ctl5464Block : Block Artifact.artifact .Osaka 8778 ctl5464Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6671 2 8778 ctl5464Program
    (by change 6671+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def blk5467Block : Block Artifact.artifact .Osaka 8781 R5CachedSuffix.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6673 20 8781 R5CachedSuffix.program
    (by change 6673+20 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def ctl5502Program : List Instr := [
  ]
def ctl5502Block : Block Artifact.artifact .Osaka 8811 ctl5502Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6693 0 8811 ctl5502Program
    (by change 6693+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 134 (by rfl)
theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 9509 = true :=
  CycleSubmission.Global.Binding.jumpDest 7233 (by rfl)
theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 8811 = true :=
  CycleSubmission.Global.Binding.jumpDest 6693 (by rfl)
theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 10104 = true :=
  CycleSubmission.Global.Binding.jumpDest 7766 (by rfl)
theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 10186 = true :=
  CycleSubmission.Global.Binding.jumpDest 7837 (by rfl)
theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 10192 = true :=
  CycleSubmission.Global.Binding.jumpDest 7843 (by rfl)
theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 8651 = true :=
  CycleSubmission.Global.Binding.jumpDest 6582 (by rfl)
theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8811 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 9430,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 9434 else UInt256.ofNat 8811),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9430,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 9434 else UInt256.ofNat 8811),stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 9430,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))
theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (_hvalid : Decode.isValidJumpDest s.executionEnv.code 9509 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 9509,stack := rest} =
      some {s with pc := UInt256.ofNat 9509,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,_hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9509,stack := rest} {s with pc := UInt256.ofNat 9509,stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 9509,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))
theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 9682,stack := rest} =
      some {s with pc := UInt256.ofNat 9682,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9682,stack := rest} {s with pc := UInt256.ofNat 9682,stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 9682,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap)
theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 9805,stack := rest} =
      some {s with pc := UInt256.ofNat 9805,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9805,stack := rest} {s with pc := UInt256.ofNat 9805,stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 9805,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap)
theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10192 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 10108,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 10112 else UInt256.ofNat 10192),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10108,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 10112 else UInt256.ofNat 10192),stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 10108,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))
theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10186 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 10168,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 10172 else UInt256.ofNat 10186),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10168,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 10172 else UInt256.ofNat 10186),stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 10168,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))
theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10104 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 10182,stack := rest} =
      some {s with pc := UInt256.ofNat 10104,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10182,stack := rest} {s with pc := UInt256.ofNat 10104,stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 10182,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))
def ctl5330_result (s : State) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10240
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 128}
theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions ctl5330Program {s with pc := UInt256.ofNat 10237,stack := rest} =
      some (ctl5330_result s rest) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hf := Challenge.Modexp.Submission.Proofs.Fast.Exp.activeWords_fix s 0 128 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 1 128)
      {s with pc := UInt256.ofNat 10237,stack := rest} =
      some {s with pc := UInt256.ofNat 10239,stack := UInt256.ofNat 128::rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr,h0,ite_true]
    rfl
  have hP0 : Challenge.EvmProof.Stepper.runInstr (.push 0 0)
      {s with pc := UInt256.ofNat 10239,stack := UInt256.ofNat 128::rest} =
      some {s with pc := UInt256.ofNat 10240,stack := UInt256.ofNat 0::UInt256.ofNat 128::rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr,List.length_cons,h1,ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 10240,stack := UInt256.ofNat 0::UInt256.ofNat 128::rest} =
      some (ctl5330_result s rest) := by
    simp only [Challenge.EvmProof.Stepper.runInstr,List.length_cons,
      show rest.length+1+1 = rest.length+2 by omega,h2,ite_true]
    change some {s with
      pc := UInt256.ofNat 10240
      stack := rest
      halt := .Returned
      hReturn := MachineState.readPadded s.memory 0 128
      activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 128)} = _
    rw [hf]
    rfl
  exact CycleSubmission.Return.cons_run _ _ _ _ _ hP1 (CycleSubmission.Return.cons_run _ _ _ _ _ hP0
    (CycleSubmission.Return.cons_run _ _ _ _ _ hRet rfl))
noncomputable def ctl5330_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10237,stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 10237,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)
theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 8778,stack := c::rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 8781 else UInt256.ofNat 207),stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,h2,hvalid,hz,
    UInt256.isTrue,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 8778,stack := c::rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 8781 else UInt256.ofNat 207),stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 8778,stack := c::rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))
theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (_hvalid : Decode.isValidJumpDest s.executionEnv.code 8811 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 8811,stack := rest} =
      some {s with pc := UInt256.ofNat 8811,stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program,runInstructions,Challenge.EvmProof.Stepper.runInstr,h0,h1,_hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 8811,stack := rest} {s with pc := UInt256.ofNat 8811,stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 8811,stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))
end CycleSubmission.R5.Blocks
