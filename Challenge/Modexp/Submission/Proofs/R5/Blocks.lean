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

def squareBlock : Block Artifact.artifact .Osaka 4018 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3092 473 4018 SquareRun.sqProgram
    (by change 3092 + 473 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg0Block : Block Artifact.artifact .Osaka 4645 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3567 69 4645 ProductRun.prSeg0Program
    (by change 3567 + 69 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg1Block : Block Artifact.artifact .Osaka 3239 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2476 155 3239 ProductRun.prSeg1Program
    (by change 2476 + 155 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg2Block : Block Artifact.artifact .Osaka 3747 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2872 111 3747 ProductRun.prSeg2Program
    (by change 2872 + 111 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg3Block : Block Artifact.artifact .Osaka 4765 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3668 269 4765 ProductRun.prSeg3Program
    (by change 3668 + 269 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def proSegBlock : Block Artifact.artifact .Osaka 5204 ConstantFold5349.foldedPrologueProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4053 79 5204 ConstantFold5349.foldedPrologueProgram
    (by change 4053 + 79 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4712Program : List Instr := [.push 2 4018, .op .JUMPI]

def ctl4712Block : Block Artifact.artifact .Osaka 4641 ctl4712Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3565 2 4641 ctl4712Program
    (by change 3565 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4800Program : List Instr := [.push 2 3239, .op .JUMP]

def ctl4800Block : Block Artifact.artifact .Osaka 4724 ctl4800Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3636 2 4724 ctl4800Program
    (by change 3636 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3433Program : List Instr := [.push 2 3747, .op .JUMP]

def ctl3433Block : Block Artifact.artifact .Osaka 3412 ctl3433Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2631 2 3412 ctl3433Program
    (by change 2631 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3901Program : List Instr := [.push 2 4765, .op .JUMP]

def ctl3901Block : Block Artifact.artifact .Osaka 3871 ctl3901Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2983 2 3871 ctl3901Program
    (by change 2983 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def normBlock : Block Artifact.artifact .Osaka 5065 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3937 4 5065 ExecNorm.normProgram
    (by change 3937 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5188Program : List Instr := [.push 2 5155, .op .JUMPI]

def ctl5188Block : Block Artifact.artifact .Osaka 5069 ctl5188Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3941 2 5069 ctl5188Program
    (by change 3941 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5192Block : Block Artifact.artifact .Osaka 5073 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3943 52 5073 ExecNorm.blk5192Program
    (by change 3943 + 52 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5261Program : List Instr := [.push 2 5149, .op .JUMPI]

def ctl5261Block : Block Artifact.artifact .Osaka 5131 ctl5261Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3995 2 5131 ctl5261Program
    (by change 3995 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5265Block : Block Artifact.artifact .Osaka 5135 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3997 10 5135 ExecNorm.blk5265Program
    (by change 3997 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5275Program : List Instr := [.push 2 5065, .op .JUMP]

def ctl5275Block : Block Artifact.artifact .Osaka 5145 ctl5275Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4007 2 5145 ctl5275Program
    (by change 4007 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def negBlock : Block Artifact.artifact .Osaka 5149 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4009 6 5149 ExecNorm.negProgram
    (by change 4009 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def doneBlock : Block Artifact.artifact .Osaka 5155 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4015 35 5155 ExecNorm.doneProgram
    (by change 4015 + 35 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5330Program : List Instr := [.push 1 128, .push 0 0, .op .RETURN]

def ctl5330Block : Block Artifact.artifact .Osaka 5200 ctl5330Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4050 3 5200 ctl5330Program
    (by change 4050 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5464Program : List Instr := [.push 1 207, .op .JUMPI]

def ctl5464Block : Block Artifact.artifact .Osaka 5353 ctl5464Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4132 2 5353 ctl5464Program
    (by change 4132 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5467Block : Block Artifact.artifact .Osaka 5356 ExecPrologue.blk5467Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4134 20 5356 ExecPrologue.blk5467Program
    (by change 4134 + 20 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5502Program : List Instr := [.push 2 4018, .op .JUMP]

def ctl5502Block : Block Artifact.artifact .Osaka 5386 ctl5502Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4154 2 5386 ctl5502Program
    (by change 4154 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 134 (by rfl)

theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 3239 = true :=
  CycleSubmission.Global.Binding.jumpDest 2476 (by rfl)

theorem jumpDest3775 : Decode.isValidJumpDest Artifact.bytecode 3747 = true :=
  CycleSubmission.Global.Binding.jumpDest 2872 (by rfl)

theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 4018 = true :=
  CycleSubmission.Global.Binding.jumpDest 3092 (by rfl)

theorem jumpDest4857 : Decode.isValidJumpDest Artifact.bytecode 4765 = true :=
  CycleSubmission.Global.Binding.jumpDest 3668 (by rfl)

theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 5065 = true :=
  CycleSubmission.Global.Binding.jumpDest 3937 (by rfl)

theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 5149 = true :=
  CycleSubmission.Global.Binding.jumpDest 4009 (by rfl)

theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 5155 = true :=
  CycleSubmission.Global.Binding.jumpDest 4015 (by rfl)

theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 5204 = true :=
  CycleSubmission.Global.Binding.jumpDest 4053 (by rfl)

theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4018 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 4641, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 4645 else UInt256.ofNat 4018), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4641, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 4645 else UInt256.ofNat 4018), stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 4641, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))

theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3239 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 4724, stack := rest} =
      some {s with pc := UInt256.ofNat 3239, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4724, stack := rest} {s with pc := UInt256.ofNat 3239, stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 4724, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))

theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3747 = true) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 3412, stack := rest} =
      some {s with pc := UInt256.ofNat 3747, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3412, stack := rest} {s with pc := UInt256.ofNat 3747, stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 3412, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap (by rw [env.code]; exact jumpDest3775))

theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4765 = true) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 3871, stack := rest} =
      some {s with pc := UInt256.ofNat 4765, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3871, stack := rest} {s with pc := UInt256.ofNat 4765, stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 3871, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap (by rw [env.code]; exact jumpDest4857))

theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5155 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 5069, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5073 else UInt256.ofNat 5155), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5069, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5073 else UInt256.ofNat 5155), stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 5069, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))

theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 5131, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5135 else UInt256.ofNat 5149), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5131, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5135 else UInt256.ofNat 5149), stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 5131, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))

theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5065 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 5145, stack := rest} =
      some {s with pc := UInt256.ofNat 5065, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5145, stack := rest} {s with pc := UInt256.ofNat 5065, stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 5145, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))

def ctl5330_result (s : State) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 5203
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 128}

theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions ctl5330Program {s with pc := UInt256.ofNat 5200, stack := rest} =
      some (ctl5330_result s rest) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hf := Challenge.Modexp.Submission.Proofs.Fast.Exp.activeWords_fix s 0 128 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 1 128)
      {s with pc := UInt256.ofNat 5200, stack := rest} =
      some {s with pc := UInt256.ofNat 5202, stack := UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, h0, ite_true]
    rfl
  have hP0 : Challenge.EvmProof.Stepper.runInstr (.push 0 0)
      {s with pc := UInt256.ofNat 5202, stack := UInt256.ofNat 128 :: rest} =
      some {s with pc := UInt256.ofNat 5203, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons, h1, ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 5203, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} =
      some (ctl5330_result s rest) := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons,
      show rest.length+1+1 = rest.length+2 by omega, h2, ite_true]
    change some {s with
      pc := UInt256.ofNat 5203
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
    GasSteps {s with pc := UInt256.ofNat 5200, stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 5200, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)

theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 5353, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5356 else UInt256.ofNat 207), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5353, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5356 else UInt256.ofNat 207), stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 5353, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))

theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4018 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 5386, stack := rest} =
      some {s with pc := UInt256.ofNat 4018, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5386, stack := rest} {s with pc := UInt256.ofNat 4018, stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 5386, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))

end CycleSubmission.R5.Blocks
