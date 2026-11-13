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

def squareBlock : Block Artifact.artifact .Osaka 3899 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3055 473 3899 SquareRun.sqProgram
    (by change 3055 + 473 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg0Block : Block Artifact.artifact .Osaka 4526 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3530 69 4526 ProductRun.prSeg0Program
    (by change 3530 + 69 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg1Block : Block Artifact.artifact .Osaka 3136 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2448 155 3136 ProductRun.prSeg1Program
    (by change 2448 + 155 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg2Block : Block Artifact.artifact .Osaka 3631 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2835 111 3631 ProductRun.prSeg2Program
    (by change 2835 + 111 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg3Block : Block Artifact.artifact .Osaka 4641 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3626 269 4641 ProductRun.prSeg3Program
    (by change 3626 + 269 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def proSegBlock : Block Artifact.artifact .Osaka 5080 ConstantFold5349.foldedPrologueProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4011 82 5080 ConstantFold5349.foldedPrologueProgram
    (by change 4011 + 82 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4712Program : List Instr := [.push 2 3899, .op .JUMPI]

def ctl4712Block : Block Artifact.artifact .Osaka 4522 ctl4712Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3528 2 4522 ctl4712Program
    (by change 3528 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4800Program : List Instr := [.push 2 3136, .op .JUMP]

def ctl4800Block : Block Artifact.artifact .Osaka 4605 ctl4800Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3599 2 4605 ctl4800Program
    (by change 3599 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3433Program : List Instr := [.push 2 3631, .op .JUMP]

def ctl3433Block : Block Artifact.artifact .Osaka 3309 ctl3433Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2603 2 3309 ctl3433Program
    (by change 2603 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3901Program : List Instr := [.push 2 4641, .op .JUMP]

def ctl3901Block : Block Artifact.artifact .Osaka 3755 ctl3901Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2946 2 3755 ctl3901Program
    (by change 2946 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def normBlock : Block Artifact.artifact .Osaka 4941 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3895 4 4941 ExecNorm.normProgram
    (by change 3895 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5188Program : List Instr := [.push 2 5031, .op .JUMPI]

def ctl5188Block : Block Artifact.artifact .Osaka 4945 ctl5188Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3899 2 4945 ctl5188Program
    (by change 3899 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5192Block : Block Artifact.artifact .Osaka 4949 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3901 52 4949 ExecNorm.blk5192Program
    (by change 3901 + 52 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5261Program : List Instr := [.push 2 5025, .op .JUMPI]

def ctl5261Block : Block Artifact.artifact .Osaka 5007 ctl5261Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3953 2 5007 ctl5261Program
    (by change 3953 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5265Block : Block Artifact.artifact .Osaka 5011 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3955 10 5011 ExecNorm.blk5265Program
    (by change 3955 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5275Program : List Instr := [.push 2 4941, .op .JUMP]

def ctl5275Block : Block Artifact.artifact .Osaka 5021 ctl5275Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3965 2 5021 ctl5275Program
    (by change 3965 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def negBlock : Block Artifact.artifact .Osaka 5025 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3967 6 5025 ExecNorm.negProgram
    (by change 3967 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def doneBlock : Block Artifact.artifact .Osaka 5031 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3973 35 5031 ExecNorm.doneProgram
    (by change 3973 + 35 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5330Program : List Instr := [.push 1 128, .push 0 0, .op .RETURN]

def ctl5330Block : Block Artifact.artifact .Osaka 5076 ctl5330Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4008 3 5076 ctl5330Program
    (by change 4008 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5464Program : List Instr := [.push 1 207, .op .JUMPI]

def ctl5464Block : Block Artifact.artifact .Osaka 5198 ctl5464Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4093 2 5198 ctl5464Program
    (by change 4093 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5467Block : Block Artifact.artifact .Osaka 5201 ExecPrologue.blk5467Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4095 20 5201 ExecPrologue.blk5467Program
    (by change 4095 + 20 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5502Program : List Instr := [.push 2 3899, .op .JUMP]

def ctl5502Block : Block Artifact.artifact .Osaka 5231 ctl5502Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4115 2 5231 ctl5502Program
    (by change 4115 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 134 (by rfl)

theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 3136 = true :=
  CycleSubmission.Global.Binding.jumpDest 2448 (by rfl)

theorem jumpDest3775 : Decode.isValidJumpDest Artifact.bytecode 3631 = true :=
  CycleSubmission.Global.Binding.jumpDest 2835 (by rfl)

theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 3899 = true :=
  CycleSubmission.Global.Binding.jumpDest 3055 (by rfl)

theorem jumpDest4857 : Decode.isValidJumpDest Artifact.bytecode 4641 = true :=
  CycleSubmission.Global.Binding.jumpDest 3626 (by rfl)

theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 4941 = true :=
  CycleSubmission.Global.Binding.jumpDest 3895 (by rfl)

theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 5025 = true :=
  CycleSubmission.Global.Binding.jumpDest 3967 (by rfl)

theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 5031 = true :=
  CycleSubmission.Global.Binding.jumpDest 3973 (by rfl)

theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 5080 = true :=
  CycleSubmission.Global.Binding.jumpDest 4011 (by rfl)

theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3899 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 4522, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 4526 else UInt256.ofNat 3899), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4522, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 4526 else UInt256.ofNat 3899), stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 4522, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))

theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3136 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 4605, stack := rest} =
      some {s with pc := UInt256.ofNat 3136, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4605, stack := rest} {s with pc := UInt256.ofNat 3136, stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 4605, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))

theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3631 = true) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 3309, stack := rest} =
      some {s with pc := UInt256.ofNat 3631, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3309, stack := rest} {s with pc := UInt256.ofNat 3631, stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 3309, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap (by rw [env.code]; exact jumpDest3775))

theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4641 = true) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 3755, stack := rest} =
      some {s with pc := UInt256.ofNat 4641, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3755, stack := rest} {s with pc := UInt256.ofNat 4641, stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 3755, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap (by rw [env.code]; exact jumpDest4857))

theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5031 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 4945, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 4949 else UInt256.ofNat 5031), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4945, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 4949 else UInt256.ofNat 5031), stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 4945, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))

theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5025 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 5007, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5011 else UInt256.ofNat 5025), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5007, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5011 else UInt256.ofNat 5025), stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 5007, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))

theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4941 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 5021, stack := rest} =
      some {s with pc := UInt256.ofNat 4941, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5021, stack := rest} {s with pc := UInt256.ofNat 4941, stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 5021, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))

def ctl5330_result (s : State) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 5079
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 128}

theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions ctl5330Program {s with pc := UInt256.ofNat 5076, stack := rest} =
      some (ctl5330_result s rest) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hf := Challenge.Modexp.Submission.Proofs.Fast.Exp.activeWords_fix s 0 128 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 1 128)
      {s with pc := UInt256.ofNat 5076, stack := rest} =
      some {s with pc := UInt256.ofNat 5078, stack := UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, h0, ite_true]
    rfl
  have hP0 : Challenge.EvmProof.Stepper.runInstr (.push 0 0)
      {s with pc := UInt256.ofNat 5078, stack := UInt256.ofNat 128 :: rest} =
      some {s with pc := UInt256.ofNat 5079, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons, h1, ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 5079, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} =
      some (ctl5330_result s rest) := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons,
      show rest.length+1+1 = rest.length+2 by omega, h2, ite_true]
    change some {s with
      pc := UInt256.ofNat 5079
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
    GasSteps {s with pc := UInt256.ofNat 5076, stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 5076, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)

theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 5198, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5201 else UInt256.ofNat 207), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5198, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5201 else UInt256.ofNat 207), stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 5198, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))

theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3899 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 5231, stack := rest} =
      some {s with pc := UInt256.ofNat 3899, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5231, stack := rest} {s with pc := UInt256.ofNat 3899, stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 5231, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))

end CycleSubmission.R5.Blocks
