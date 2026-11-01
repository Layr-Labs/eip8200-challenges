import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.R5.SquareRun
import Challenge.Modexp.Submission.Proofs.R5.ProductRun
import Challenge.Modexp.Submission.Proofs.R5.ExecNorm
import Challenge.Modexp.Submission.Proofs.R5.PrologueRun
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

def squareBlock : Block Artifact.artifact .Osaka 4037 SquareRun.sqProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 3122 498 4037 SquareRun.sqProgram
    (by change 3122+498 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 3122+498 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg0Block : Block Artifact.artifact .Osaka 4716 ProductRun.prSeg0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 3622 69 4716 ProductRun.prSeg0Program
    (by change 3622+69 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 3622+69 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg1Block : Block Artifact.artifact .Osaka 3256 ProductRun.prSeg1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2495 155 3256 ProductRun.prSeg1Program
    (by change 2495+155 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2495+155 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg2Block : Block Artifact.artifact .Osaka 3775 ProductRun.prSeg2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2898 111 3775 ProductRun.prSeg2Program
    (by change 2898+111 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2898+111 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def productSeg3Block : Block Artifact.artifact .Osaka 4857 ProductRun.prSeg3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 3742 275 4857 ProductRun.prSeg3Program
    (by change 3742+275 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 3742+275 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def proSegBlock : Block Artifact.artifact .Osaka 5334 PrologueRun.proSegProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4140 87 5334 PrologueRun.proSegProgram
    (by change 4140+87 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4140+87 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4712Program : List Instr := [.push 2 4037, .op .JUMPI]

def ctl4712Block : Block Artifact.artifact .Osaka 4712 ctl4712Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 3620 2 4712 ctl4712Program
    (by change 3620+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 3620+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl4800Program : List Instr := [.push 2 3256, .op .JUMP]

def ctl4800Block : Block Artifact.artifact .Osaka 4800 ctl4800Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 3691 2 4800 ctl4800Program
    (by change 3691+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 3691+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3433Program : List Instr := [.push 2 3775, .op .JUMP]

def ctl3433Block : Block Artifact.artifact .Osaka 3433 ctl3433Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2650 2 3433 ctl3433Program
    (by change 2650+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2650+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl3901Program : List Instr := [.push 2 4857, .op .JUMP]

def ctl3901Block : Block Artifact.artifact .Osaka 3901 ctl3901Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 3009 2 3901 ctl3901Program
    (by change 3009+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 3009+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def normBlock : Block Artifact.artifact .Osaka 5184 ExecNorm.normProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4017 4 5184 ExecNorm.normProgram
    (by change 4017+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4017+4 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5188Program : List Instr := [.push 2 5285, .op .JUMPI]

def ctl5188Block : Block Artifact.artifact .Osaka 5188 ctl5188Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4021 2 5188 ctl5188Program
    (by change 4021+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4021+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5192Block : Block Artifact.artifact .Osaka 5192 ExecNorm.blk5192Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4023 59 5192 ExecNorm.blk5192Program
    (by change 4023+59 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4023+59 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5261Program : List Instr := [.push 2 5279, .op .JUMPI]

def ctl5261Block : Block Artifact.artifact .Osaka 5261 ctl5261Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4082 2 5261 ctl5261Program
    (by change 4082+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4082+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5265Block : Block Artifact.artifact .Osaka 5265 ExecNorm.blk5265Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4084 10 5265 ExecNorm.blk5265Program
    (by change 4084+10 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4084+10 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5275Program : List Instr := [.push 2 5184, .op .JUMP]

def ctl5275Block : Block Artifact.artifact .Osaka 5275 ctl5275Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4094 2 5275 ctl5275Program
    (by change 4094+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4094+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def negBlock : Block Artifact.artifact .Osaka 5279 ExecNorm.negProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4096 6 5279 ExecNorm.negProgram
    (by change 4096+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4096+6 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def doneBlock : Block Artifact.artifact .Osaka 5285 ExecNorm.doneProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4102 35 5285 ExecNorm.doneProgram
    (by change 4102+35 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4102+35 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5330Program : List Instr := [.push 1 128, .push 0 0, .op .RETURN]

def ctl5330Block : Block Artifact.artifact .Osaka 5330 ctl5330Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4137 3 5330 ctl5330Program
    (by change 4137+3 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4137+3 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def proBlock : Block Artifact.artifact .Osaka 5334 ExecPrologue.proProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4140 8 5334 ExecPrologue.proProgram
    (by change 4140+8 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4140+8 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5344Block : Block Artifact.artifact .Osaka 5344 ExecPrologue.blk5344Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4148 6 5344 ExecPrologue.blk5344Program
    (by change 4148+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4148+6 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5352Block : Block Artifact.artifact .Osaka 5352 ExecPrologue.blk5352Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4154 30 5352 ExecPrologue.blk5352Program
    (by change 4154+30 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4154+30 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5393Block : Block Artifact.artifact .Osaka 5393 ExecPrologue.blk5393Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4184 7 5393 ExecPrologue.blk5393Program
    (by change 4184+7 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4184+7 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5403Block : Block Artifact.artifact .Osaka 5403 ExecPrologue.blk5403Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4191 7 5403 ExecPrologue.blk5403Program
    (by change 4191+7 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4191+7 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5414Block : Block Artifact.artifact .Osaka 5414 ExecPrologue.blk5414Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4198 7 5414 ExecPrologue.blk5414Program
    (by change 4198+7 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4198+7 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5425Block : Block Artifact.artifact .Osaka 5425 ExecPrologue.blk5425Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4205 7 5425 ExecPrologue.blk5425Program
    (by change 4205+7 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4205+7 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5436Block : Block Artifact.artifact .Osaka 5436 ExecPrologue.blk5436Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4212 6 5436 ExecPrologue.blk5436Program
    (by change 4212+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4212+6 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5446Block : Block Artifact.artifact .Osaka 5446 ExecPrologue.blk5446Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4218 9 5446 ExecPrologue.blk5446Program
    (by change 4218+9 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4218+9 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5464Program : List Instr := [.push 1 219, .op .JUMPI]

def ctl5464Block : Block Artifact.artifact .Osaka 5464 ctl5464Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4227 2 5464 ctl5464Program
    (by change 4227+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4227+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def blk5467Block : Block Artifact.artifact .Osaka 5467 ExecPrologue.blk5467Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4229 22 5467 ExecPrologue.blk5467Program
    (by change 4229+22 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4229+22 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def ctl5502Program : List Instr := [.push 2 4037, .op .JUMP]

def ctl5502Block : Block Artifact.artifact .Osaka 5502 ctl5502Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4251 2 5502 ctl5502Program
    (by change 4251+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4251+2 ≤ 8638)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem jumpDest219 : Decode.isValidJumpDest Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 146 (by rfl)

theorem jumpDest3256 : Decode.isValidJumpDest Artifact.bytecode 3256 = true :=
  CycleSubmission.Global.Binding.jumpDest 2495 (by rfl)

theorem jumpDest3775 : Decode.isValidJumpDest Artifact.bytecode 3775 = true :=
  CycleSubmission.Global.Binding.jumpDest 2898 (by rfl)

theorem jumpDest4037 : Decode.isValidJumpDest Artifact.bytecode 4037 = true :=
  CycleSubmission.Global.Binding.jumpDest 3122 (by rfl)

theorem jumpDest4857 : Decode.isValidJumpDest Artifact.bytecode 4857 = true :=
  CycleSubmission.Global.Binding.jumpDest 3742 (by rfl)

theorem jumpDest5184 : Decode.isValidJumpDest Artifact.bytecode 5184 = true :=
  CycleSubmission.Global.Binding.jumpDest 4017 (by rfl)

theorem jumpDest5279 : Decode.isValidJumpDest Artifact.bytecode 5279 = true :=
  CycleSubmission.Global.Binding.jumpDest 4096 (by rfl)

theorem jumpDest5285 : Decode.isValidJumpDest Artifact.bytecode 5285 = true :=
  CycleSubmission.Global.Binding.jumpDest 4102 (by rfl)

theorem jumpDest5334 : Decode.isValidJumpDest Artifact.bytecode 5334 = true :=
  CycleSubmission.Global.Binding.jumpDest 4140 (by rfl)

theorem ctl4712_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4037 = true) :
    runInstructions ctl4712Program {s with pc := UInt256.ofNat 4712, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 4716 else UInt256.ofNat 4037), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl4712Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4712_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4712, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 4716 else UInt256.ofNat 4037), stack := rest} :=
  ctl4712Block.steps (s := {s with pc := UInt256.ofNat 4712, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl4712_run s c rest hcap (by rw [env.code]; exact jumpDest4037))

theorem ctl4800_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3256 = true) :
    runInstructions ctl4800Program {s with pc := UInt256.ofNat 4800, stack := rest} =
      some {s with pc := UInt256.ofNat 3256, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl4800Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl4800_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 4800, stack := rest} {s with pc := UInt256.ofNat 3256, stack := rest} :=
  ctl4800Block.steps (s := {s with pc := UInt256.ofNat 4800, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl4800_run s rest hcap (by rw [env.code]; exact jumpDest3256))

theorem ctl3433_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3775 = true) :
    runInstructions ctl3433Program {s with pc := UInt256.ofNat 3433, stack := rest} =
      some {s with pc := UInt256.ofNat 3775, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3433Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3433_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3433, stack := rest} {s with pc := UInt256.ofNat 3775, stack := rest} :=
  ctl3433Block.steps (s := {s with pc := UInt256.ofNat 3433, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3433_run s rest hcap (by rw [env.code]; exact jumpDest3775))

theorem ctl3901_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4857 = true) :
    runInstructions ctl3901Program {s with pc := UInt256.ofNat 3901, stack := rest} =
      some {s with pc := UInt256.ofNat 4857, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl3901Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl3901_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 3901, stack := rest} {s with pc := UInt256.ofNat 4857, stack := rest} :=
  ctl3901Block.steps (s := {s with pc := UInt256.ofNat 3901, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl3901_run s rest hcap (by rw [env.code]; exact jumpDest4857))

theorem ctl5188_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5285 = true) :
    runInstructions ctl5188Program {s with pc := UInt256.ofNat 5188, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5192 else UInt256.ofNat 5285), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5188Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5188_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5188, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5192 else UInt256.ofNat 5285), stack := rest} :=
  ctl5188Block.steps (s := {s with pc := UInt256.ofNat 5188, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5188_run s c rest hcap (by rw [env.code]; exact jumpDest5285))

theorem ctl5261_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5279 = true) :
    runInstructions ctl5261Program {s with pc := UInt256.ofNat 5261, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5265 else UInt256.ofNat 5279), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5261Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5261_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5261, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5265 else UInt256.ofNat 5279), stack := rest} :=
  ctl5261Block.steps (s := {s with pc := UInt256.ofNat 5261, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5261_run s c rest hcap (by rw [env.code]; exact jumpDest5279))

theorem ctl5275_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5184 = true) :
    runInstructions ctl5275Program {s with pc := UInt256.ofNat 5275, stack := rest} =
      some {s with pc := UInt256.ofNat 5184, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5275Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5275_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5275, stack := rest} {s with pc := UInt256.ofNat 5184, stack := rest} :=
  ctl5275Block.steps (s := {s with pc := UInt256.ofNat 5275, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5275_run s rest hcap (by rw [env.code]; exact jumpDest5184))

def ctl5330_result (s : State) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 5333
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 128}

theorem ctl5330_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions ctl5330Program {s with pc := UInt256.ofNat 5330, stack := rest} =
      some (ctl5330_result s rest) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hf := Challenge.Modexp.Submission.Proofs.Fast.Exp.activeWords_fix s 0 128 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 1 128)
      {s with pc := UInt256.ofNat 5330, stack := rest} =
      some {s with pc := UInt256.ofNat 5332, stack := UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, h0, ite_true]
    rfl
  have hP0 : Challenge.EvmProof.Stepper.runInstr (.push 0 0)
      {s with pc := UInt256.ofNat 5332, stack := UInt256.ofNat 128 :: rest} =
      some {s with pc := UInt256.ofNat 5333, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons, h1, ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 5333, stack := UInt256.ofNat 0 :: UInt256.ofNat 128 :: rest} =
      some (ctl5330_result s rest) := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons,
      show rest.length+1+1 = rest.length+2 by omega, h2, ite_true]
    change some {s with
      pc := UInt256.ofNat 5333
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
    GasSteps {s with pc := UInt256.ofNat 5330, stack := rest} (ctl5330_result s rest) :=
  ctl5330Block.steps (s := {s with pc := UInt256.ofNat 5330, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5330_run s rest hcap hact)

theorem ctl5464_run (s : State) (c : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 219 = true) :
    runInstructions ctl5464Program {s with pc := UInt256.ofNat 5464, stack := c :: rest} =
      some {s with pc := (if c.toNat = 0 then UInt256.ofNat 5467 else UInt256.ofNat 219), stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  by_cases hz : c.toNat = 0 <;>
  simp [ctl5464Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, h2, hvalid, hz,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5464_steps (s : State) (c : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5464, stack := c :: rest}
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 5467 else UInt256.ofNat 219), stack := rest} :=
  ctl5464Block.steps (s := {s with pc := UInt256.ofNat 5464, stack := c :: rest}) (env.transfer rfl rfl) rfl
    (ctl5464_run s c rest hcap (by rw [env.code]; exact jumpDest219))

theorem ctl5502_run (s : State) (rest : List UInt256) (hcap : rest.length < 1000)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4037 = true) :
    runInstructions ctl5502Program {s with pc := UInt256.ofNat 5502, stack := rest} =
      some {s with pc := UInt256.ofNat 4037, stack := rest} := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [ctl5502Program, runInstructions, Challenge.EvmProof.Stepper.runInstr, h0, h1, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def ctl5502_steps (s : State) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length < 1000) :
    GasSteps {s with pc := UInt256.ofNat 5502, stack := rest} {s with pc := UInt256.ofNat 4037, stack := rest} :=
  ctl5502Block.steps (s := {s with pc := UInt256.ofNat 5502, stack := rest}) (env.transfer rfl rfl) rfl
    (ctl5502_run s rest hcap (by rw [env.code]; exact jumpDest4037))

end CycleSubmission.R5.Blocks
