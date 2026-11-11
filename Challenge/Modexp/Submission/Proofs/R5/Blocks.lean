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

def squareBlock : Block Artifact.artifact .Osaka 4007 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3083 473 4007 SquareRun.sqProgram
    (by change 3083 + 473 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg0Block : Block Artifact.artifact .Osaka 4634 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3558 69 4634 ProductRun.prSeg0Program
    (by change 3558 + 69 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg1Block : Block Artifact.artifact .Osaka 3251 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2472 155 3251 ProductRun.prSeg1Program
    (by change 2472 + 155 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg2Block : Block Artifact.artifact .Osaka 3747 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2854 111 3747 ProductRun.prSeg2Program
    (by change 2854 + 111 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg3Block : Block Artifact.artifact .Osaka 4758 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3666 269 4758 ProductRun.prSeg3Program
    (by change 3666 + 269 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def proSegBlock : Block Artifact.artifact .Osaka 5197 ConstantFold5349.foldedPrologueProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4051 79 5197 ConstantFold5349.foldedPrologueProgram
    (by change 4051 + 79 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4712Program : List Instr := [.push 2 4007, .op .JUMPI]

def ctl4712Block : Block Artifact.artifact .Osaka 4630 ctl4712Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3556 2 4630 ctl4712Program
    (by change 3556 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4800Program : List Instr := [.push 2 3251, .op .JUMP]

def ctl4800Block : Block Artifact.artifact .Osaka 4713 ctl4800Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3627 2 4713 ctl4800Program
    (by change 3627 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3433Program : List Instr := [.push 2 3747, .op .JUMP]

def ctl3433Block : Block Artifact.artifact .Osaka 3424 ctl3433Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2627 2 3424 ctl3433Program
    (by change 2627 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3901Program : List Instr := [.push 2 4758, .op .JUMP]

def ctl3901Block : Block Artifact.artifact .Osaka 3871 ctl3901Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2965 2 3871 ctl3901Program
    (by change 2965 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def normBlock : Block Artifact.artifact .Osaka 5058 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3935 4 5058 ExecNorm.normProgram
    (by change 3935 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5188Program : List Instr := [.push 2 5148, .op .JUMPI]

def ctl5188Block : Block Artifact.artifact .Osaka 5062 ctl5188Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3939 2 5062 ctl5188Program
    (by change 3939 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5192Block : Block Artifact.artifact .Osaka 5066 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3941 52 5066 ExecNorm.blk5192Program
    (by change 3941 + 52 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5261Program : List Instr := [.push 2 5142, .op .JUMPI]

def ctl5261Block : Block Artifact.artifact .Osaka 5124 ctl5261Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3993 2 5124 ctl5261Program
    (by change 3993 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5265Block : Block Artifact.artifact .Osaka 5128 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3995 10 5128 ExecNorm.blk5265Program
    (by change 3995 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5275Program : List Instr := [.push 2 5058, .op .JUMP]

def ctl5275Block : Block Artifact.artifact .Osaka 5138 ctl5275Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4005 2 5138 ctl5275Program
    (by change 4005 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def negBlock : Block Artifact.artifact .Osaka 5142 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4007 6 5142 ExecNorm.negProgram
    (by change 4007 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def doneBlock : Block Artifact.artifact .Osaka 5148 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4013 35 5148 ExecNorm.doneProgram
    (by change 4013 + 35 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5330Program : List Instr := [.push 1 128, .push 0 0, .op .RETURN]

def ctl5330Block : Block Artifact.artifact .Osaka 5193 ctl5330Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4048 3 5193 ctl5330Program
    (by change 4048 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5464Program : List Instr := [.push 1 207, .op .JUMPI]

def ctl5464Block : Block Artifact.artifact .Osaka 5346 ctl5464Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4130 2 5346 ctl5464Program
    (by change 4130 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5467Block : Block Artifact.artifact .Osaka 5349 ExecPrologue.blk5467Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4132 20 5349 ExecPrologue.blk5467Program
    (by change 4132 + 20 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5502Program : List Instr := [.push 2 4007, .op .JUMP]

def ctl5502Block : Block Artifact.artifact .Osaka 5379 ctl5502Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4152 2 5379 ctl5502Program
    (by change 4152 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 3251 = true :=
  CycleSubmission.Global.Binding.jumpDest 2472 (by rfl)

theorem jumpDest3775 : Decode.isValidJumpDest Artifact.bytecode 3747 = true :=
  CycleSubmission.Global.Binding.jumpDest 2854 (by rfl)

theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 4007 = true :=
  CycleSubmission.Global.Binding.jumpDest 3083 (by rfl)

theorem jumpDest4857 : Decode.isValidJumpDest Artifact.bytecode 4758 = true :=
  CycleSubmission.Global.Binding.jumpDest 3666 (by rfl)

theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 5058 = true :=
  CycleSubmission.Global.Binding.jumpDest 3935 (by rfl)

theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 5142 = true :=
  CycleSubmission.Global.Binding.jumpDest 4007 (by rfl)

theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 5148 = true :=
  CycleSubmission.Global.Binding.jumpDest 4013 (by rfl)

theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 5197 = true :=
  CycleSubmission.Global.Binding.jumpDest 4051 (by rfl)

theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4007 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 4630, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 4634 else UInt256.ofNat 4007), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4630, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 4634 else UInt256.ofNat 4007), stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 4630, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))

theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3251 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 4713, stack := rest} =
      some {s with pc := UInt256.ofNat 3251, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4713, stack := rest} {s with pc := UInt256.ofNat 3251, stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 4713, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))

theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3747 = true) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 3424, stack := rest} =
      some {s with pc := UInt256.ofNat 3747, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3424, stack := rest} {s with pc := UInt256.ofNat 3747, stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 3424, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap (by rw [env.code]; exact jumpDest3775))

theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4758 = true) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 3871, stack := rest} =
      some {s with pc := UInt256.ofNat 4758, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3871, stack := rest} {s with pc := UInt256.ofNat 4758, stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 3871, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap (by rw [env.code]; exact jumpDest4857))

theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5148 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 5062, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5066 else UInt256.ofNat 5148), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5062, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5066 else UInt256.ofNat 5148), stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 5062, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))

theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5142 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 5124, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5128 else UInt256.ofNat 5142), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5124, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5128 else UInt256.ofNat 5142), stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 5124, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))

theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5058 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 5138, stack := rest} =
      some {s with pc := UInt256.ofNat 5058, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5138, stack := rest} {s with pc := UInt256.ofNat 5058, stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 5138, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))

def ctl5330_result (s : State) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 5196
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 128}

theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions ctl5330Program {s with pc := UInt256.ofNat 5193, stack := rest} =
      some (ctl5330_result s rest) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hf := Challenge.Modexp.Submission.Proofs.Fast.Exp.activeWords_fix s 0 128 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 1 128)
      {s with pc := UInt256.ofNat 5193, stack := rest} =
      some {s with pc := UInt256.ofNat 5195, stack := UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, h0, ite_true]
    rfl
  have hP0 : Challenge.EvmProof.Stepper.runInstr (.push 0 0)
      {s with pc := UInt256.ofNat 5195, stack := UInt256.ofNat 128 :: rest} =
      some {s with pc := UInt256.ofNat 5196, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons, h1, ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 5196, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} =
      some (ctl5330_result s rest) := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons,
      show rest.length+1+1 = rest.length+2 by omega, h2, ite_true]
    change some {s with
      pc := UInt256.ofNat 5196
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
    GasSteps {s with pc := UInt256.ofNat 5193, stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 5193, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)

theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 5346, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5349 else UInt256.ofNat 207), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5346, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5349 else UInt256.ofNat 207), stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 5346, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))

theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4007 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 5379, stack := rest} =
      some {s with pc := UInt256.ofNat 4007, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5379, stack := rest} {s with pc := UInt256.ofNat 4007, stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 5379, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))

end CycleSubmission.R5.Blocks
