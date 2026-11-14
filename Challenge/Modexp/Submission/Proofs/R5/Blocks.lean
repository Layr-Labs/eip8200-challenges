import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.R5.SquareRun
import Challenge.Modexp.Submission.Proofs.R5.ProductRun
import Challenge.Modexp.Submission.Proofs.R5.ExecNorm
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

def squareBlock : Block Artifact.artifact .Osaka 8607 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6690 473 8607 SquareRun.sqProgram
    (by change 6690+473 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg0Block : Block Artifact.artifact .Osaka 9234 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7165 69 9234 ProductRun.prSeg0Program
    (by change 7165+69 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg1Block : Block Artifact.artifact .Osaka 9313 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7234 155 9313 ProductRun.prSeg1Program
    (by change 7234+155 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg2Block : Block Artifact.artifact .Osaka 9583 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7460 111 9583 ProductRun.prSeg2Program
    (by change 7460+111 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg3Block : Block Artifact.artifact .Osaka 9879 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7701 269 9879 ProductRun.prSeg3Program
    (by change 7701+269 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def proSegBlock : Block Artifact.artifact .Osaka 8456 ConstantFold5349.foldedPrologueProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6586 82 8456 ConstantFold5349.foldedPrologueProgram
    (by change 6586+82 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4712Program : List Instr := [
  .push 2 8607,
   .op .JUMPI]

def ctl4712Block : Block Artifact.artifact .Osaka 9230 ctl4712Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7163 2 9230 ctl4712Program
    (by change 7163+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4800Program : List Instr := [
  ]

def ctl4800Block : Block Artifact.artifact .Osaka 9313 ctl4800Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7234 0 9313 ctl4800Program
    (by change 7234+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3433Program : List Instr := [
  .push 2 9583,
   .op .JUMP]

def ctl3433Block : Block Artifact.artifact .Osaka 9486 ctl3433Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7389 2 9486 ctl3433Program
    (by change 7389+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3901Program : List Instr := [
  .push 2 9879,
   .op .JUMP]

def ctl3901Block : Block Artifact.artifact .Osaka 9707 ctl3901Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7571 2 9707 ctl3901Program
    (by change 7571+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def normBlock : Block Artifact.artifact .Osaka 10179 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7970 4 10179 ExecNorm.normProgram
    (by change 7970+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5188Program : List Instr := [
  .push 2 10269,
   .op .JUMPI]

def ctl5188Block : Block Artifact.artifact .Osaka 10183 ctl5188Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7974 2 10183 ctl5188Program
    (by change 7974+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5192Block : Block Artifact.artifact .Osaka 10187 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7976 52 10187 ExecNorm.blk5192Program
    (by change 7976+52 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5261Program : List Instr := [
  .push 2 10263,
   .op .JUMPI]

def ctl5261Block : Block Artifact.artifact .Osaka 10245 ctl5261Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8028 2 10245 ctl5261Program
    (by change 8028+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5265Block : Block Artifact.artifact .Osaka 10249 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8030 10 10249 ExecNorm.blk5265Program
    (by change 8030+10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5275Program : List Instr := [
  .push 2 10179,
   .op .JUMP]

def ctl5275Block : Block Artifact.artifact .Osaka 10259 ctl5275Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8040 2 10259 ctl5275Program
    (by change 8040+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def negBlock : Block Artifact.artifact .Osaka 10263 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8042 6 10263 ExecNorm.negProgram
    (by change 8042+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def doneBlock : Block Artifact.artifact .Osaka 10269 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8048 35 10269 ExecNorm.doneProgram
    (by change 8048+35 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5330Program : List Instr := [
  .push 1 128,
   .push 0 0,
   .op .RETURN]

def ctl5330Block : Block Artifact.artifact .Osaka 10314 ctl5330Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8083 3 10314 ctl5330Program
    (by change 8083+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5464Program : List Instr := [
  .push 1 207,
   .op .JUMPI]

def ctl5464Block : Block Artifact.artifact .Osaka 8574 ctl5464Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6668 2 8574 ctl5464Program
    (by change 6668+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5467Block : Block Artifact.artifact .Osaka 8577 ExecPrologue.blk5467Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6670 20 8577 ExecPrologue.blk5467Program
    (by change 6670+20 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5502Program : List Instr := [
  ]

def ctl5502Block : Block Artifact.artifact .Osaka 8607 ctl5502Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6690 0 8607 ctl5502Program
    (by change 6690+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 134 (by rfl)

theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 9313 = true :=
  CycleSubmission.Global.Binding.jumpDest 7234 (by rfl)

theorem jumpDest3775 : Decode.isValidJumpDest Artifact.bytecode 9583 = true :=
  CycleSubmission.Global.Binding.jumpDest 7460 (by rfl)

theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 8607 = true :=
  CycleSubmission.Global.Binding.jumpDest 6690 (by rfl)

theorem jumpDest4857 : Decode.isValidJumpDest Artifact.bytecode 9879 = true :=
  CycleSubmission.Global.Binding.jumpDest 7701 (by rfl)

theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 10179 = true :=
  CycleSubmission.Global.Binding.jumpDest 7970 (by rfl)

theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 10263 = true :=
  CycleSubmission.Global.Binding.jumpDest 8042 (by rfl)

theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 10269 = true :=
  CycleSubmission.Global.Binding.jumpDest 8048 (by rfl)

theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 8456 = true :=
  CycleSubmission.Global.Binding.jumpDest 6586 (by rfl)

theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8607 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 9230, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 9234 else UInt256.ofNat 8607), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9230, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 9234 else UInt256.ofNat 8607), stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 9230, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))

theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (_hvalid : Decode.isValidJumpDest s.executionEnv.code 9313 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 9313, stack := rest} =
      some {s with pc := UInt256.ofNat 9313, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, _hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9313, stack := rest} {s with pc := UInt256.ofNat 9313, stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 9313, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))

theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 9583 = true) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 9486, stack := rest} =
      some {s with pc := UInt256.ofNat 9583, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9486, stack := rest} {s with pc := UInt256.ofNat 9583, stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 9486, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap (by rw [env.code]; exact jumpDest3775))

theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 9879 = true) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 9707, stack := rest} =
      some {s with pc := UInt256.ofNat 9879, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 9707, stack := rest} {s with pc := UInt256.ofNat 9879, stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 9707, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap (by rw [env.code]; exact jumpDest4857))

theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10269 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 10183, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 10187 else UInt256.ofNat 10269), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10183, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 10187 else UInt256.ofNat 10269), stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 10183, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))

theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10263 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 10245, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 10249 else UInt256.ofNat 10263), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10245, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 10249 else UInt256.ofNat 10263), stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 10245, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))

theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10179 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 10259, stack := rest} =
      some {s with pc := UInt256.ofNat 10179, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 10259, stack := rest} {s with pc := UInt256.ofNat 10179, stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 10259, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))

def ctl5330_result (s : State) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10317
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 128}

theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions ctl5330Program {s with pc := UInt256.ofNat 10314, stack := rest} =
      some (ctl5330_result s rest) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hf := Challenge.Modexp.Submission.Proofs.Fast.Exp.activeWords_fix s 0 128 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 1 128)
      {s with pc := UInt256.ofNat 10314, stack := rest} =
      some {s with pc := UInt256.ofNat 10316, stack := UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, h0, ite_true]
    rfl
  have hP0 : Challenge.EvmProof.Stepper.runInstr (.push 0 0)
      {s with pc := UInt256.ofNat 10316, stack := UInt256.ofNat 128 :: rest} =
      some {s with pc := UInt256.ofNat 10317, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons, h1, ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 10317, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} =
      some (ctl5330_result s rest) := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons,
      show rest.length+1+1 = rest.length+2 by omega, h2, ite_true]
    change some {s with
      pc := UInt256.ofNat 10317
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
    GasSteps {s with pc := UInt256.ofNat 10314, stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 10314, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)

theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 8574, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 8577 else UInt256.ofNat 207), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 8574, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 8577 else UInt256.ofNat 207), stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 8574, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))

theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (_hvalid : Decode.isValidJumpDest s.executionEnv.code 8607 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 8607, stack := rest} =
      some {s with pc := UInt256.ofNat 8607, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, _hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 8607, stack := rest} {s with pc := UInt256.ofNat 8607, stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 8607, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))

end CycleSubmission.R5.Blocks
