import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineArtifactSuffix
import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineProdiag0
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR0z10
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR0z20
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR0z30
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR0e0
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedm0
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedm1
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedm2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedm3
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds10
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds11
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds12
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds13
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds20
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds21
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds22
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds23
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds30
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds31
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds32
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineReds33
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedt0
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedt1
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedt2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineRedt3
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR1h1
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR1d1
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR1c21
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR1c31
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR1e1
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR2h2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR2d2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR2c32
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR2e2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR3h3
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR3d3
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineR3e3
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
noncomputable section
set_option warningAsError true
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Fast.R4InlineBlocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open CycleSubmission.Global.Fast.R4InlineTransport

def block_prodiag_0 : Block CycleSubmission.Artifact.artifact .Osaka 4037 prodiag_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3130 21 4037 prodiag_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3130 + 21 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 0 4037 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 0 21 prodiag_0New rfl) (by decide)

def block_r0z1_0 : Block CycleSubmission.Artifact.artifact .Osaka 4060 r0z1_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3151 21 4060 r0z1_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3151 + 21 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 21 4060 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 21 21 r0z1_0New rfl) (by decide)

def block_r0z2_0 : Block CycleSubmission.Artifact.artifact .Osaka 4083 r0z2_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3172 21 4083 r0z2_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3172 + 21 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 42 4083 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 42 21 r0z2_0New rfl) (by decide)

def block_r0z3_0 : Block CycleSubmission.Artifact.artifact .Osaka 4106 r0z3_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3193 21 4106 r0z3_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3193 + 21 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 63 4106 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 63 21 r0z3_0New rfl) (by decide)

def block_r0e_0 : Block CycleSubmission.Artifact.artifact .Osaka 4129 r0e_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3214 3 4129 r0e_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3214 + 3 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 84 4129 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 84 3 r0e_0New rfl) (by decide)

def block_redm_0 : Block CycleSubmission.Artifact.artifact .Osaka 4132 redm_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3217 10 4132 redm_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3217 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 87 4132 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 87 10 redm_0New rfl) (by decide)

def block_redm_1 : Block CycleSubmission.Artifact.artifact .Osaka 4329 redm_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3406 10 4329 redm_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3406 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 276 4329 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 276 10 redm_1New rfl) (by decide)

def block_redm_2 : Block CycleSubmission.Artifact.artifact .Osaka 4497 redm_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3568 10 4497 redm_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3568 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 438 4497 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 438 10 redm_2New rfl) (by decide)

def block_redm_3 : Block CycleSubmission.Artifact.artifact .Osaka 4632 redm_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3699 10 4632 redm_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3699 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 569 4632 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 569 10 redm_3New rfl) (by decide)

def block_reds1_0 : Block CycleSubmission.Artifact.artifact .Osaka 4142 reds1_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3227 25 4142 reds1_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3227 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 97 4142 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 97 25 reds1_0New rfl) (by decide)

def block_reds1_1 : Block CycleSubmission.Artifact.artifact .Osaka 4339 reds1_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3416 25 4339 reds1_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3416 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 286 4339 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 286 25 reds1_1New rfl) (by decide)

def block_reds1_2 : Block CycleSubmission.Artifact.artifact .Osaka 4507 reds1_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3578 25 4507 reds1_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3578 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 448 4507 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 448 25 reds1_2New rfl) (by decide)

def block_reds1_3 : Block CycleSubmission.Artifact.artifact .Osaka 4642 reds1_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3709 25 4642 reds1_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3709 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 579 4642 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 579 25 reds1_3New rfl) (by decide)

def block_reds2_0 : Block CycleSubmission.Artifact.artifact .Osaka 4167 reds2_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3252 25 4167 reds2_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3252 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 122 4167 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 122 25 reds2_0New rfl) (by decide)

def block_reds2_1 : Block CycleSubmission.Artifact.artifact .Osaka 4364 reds2_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3441 25 4364 reds2_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3441 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 311 4364 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 311 25 reds2_1New rfl) (by decide)

def block_reds2_2 : Block CycleSubmission.Artifact.artifact .Osaka 4532 reds2_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3603 25 4532 reds2_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3603 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 473 4532 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 473 25 reds2_2New rfl) (by decide)

def block_reds2_3 : Block CycleSubmission.Artifact.artifact .Osaka 4667 reds2_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3734 25 4667 reds2_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3734 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 604 4667 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 604 25 reds2_3New rfl) (by decide)

def block_reds3_0 : Block CycleSubmission.Artifact.artifact .Osaka 4192 reds3_0New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3277 25 4192 reds3_0New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3277 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 147 4192 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 147 25 reds3_0New rfl) (by decide)

def block_reds3_1 : Block CycleSubmission.Artifact.artifact .Osaka 4389 reds3_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3466 25 4389 reds3_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3466 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 336 4389 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 336 25 reds3_1New rfl) (by decide)

def block_reds3_2 : Block CycleSubmission.Artifact.artifact .Osaka 4557 reds3_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3628 25 4557 reds3_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3628 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 498 4557 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 498 25 reds3_2New rfl) (by decide)

def block_reds3_3 : Block CycleSubmission.Artifact.artifact .Osaka 4692 reds3_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3759 25 4692 reds3_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3759 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 629 4692 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 629 25 reds3_3New rfl) (by decide)

def block_redt_0Zero114 : Block CycleSubmission.Artifact.artifact .Osaka 4217 redt_0Zero114 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3302 10 4217 redt_0Zero114
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3302 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 172 4217 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 172 10 redt_0Zero114 rfl) (by decide)

def block_redt_1 : Block CycleSubmission.Artifact.artifact .Osaka 4414 redt_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3491 10 4414 redt_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3491 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 361 4414 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 361 10 redt_1New rfl) (by decide)

def block_redt_2 : Block CycleSubmission.Artifact.artifact .Osaka 4582 redt_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3653 10 4582 redt_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3653 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 523 4582 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 523 10 redt_2New rfl) (by decide)

def block_redt_3 : Block CycleSubmission.Artifact.artifact .Osaka 4717 redt_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3784 10 4717 redt_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3784 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 654 4717 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 654 10 redt_3New rfl) (by decide)

def block_r1h_1 : Block CycleSubmission.Artifact.artifact .Osaka 4227 r1h_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3312 5 4227 r1h_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3312 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 182 4227 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 182 5 r1h_1New rfl) (by decide)

def block_r1d_1 : Block CycleSubmission.Artifact.artifact .Osaka 4237 r1d_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3318 28 4237 r1d_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3318 + 28 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 188 4237 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 188 28 r1d_1New rfl) (by decide)

def block_r1c2_1 : Block CycleSubmission.Artifact.artifact .Osaka 4265 r1c2_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3346 27 4265 r1c2_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3346 + 27 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 216 4265 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 216 27 r1c2_1New rfl) (by decide)

def block_r1c3_1 : Block CycleSubmission.Artifact.artifact .Osaka 4294 r1c3_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3373 28 4294 r1c3_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3373 + 28 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 243 4294 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 243 28 r1c3_1New rfl) (by decide)

def block_r1e_1 : Block CycleSubmission.Artifact.artifact .Osaka 4324 r1e_1New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3401 5 4324 r1e_1New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3401 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 271 4324 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 271 5 r1e_1New rfl) (by decide)

def block_r2h_2 : Block CycleSubmission.Artifact.artifact .Osaka 4424 r2h_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3501 5 4424 r2h_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3501 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 371 4424 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 371 5 r2h_2New rfl) (by decide)

def block_r2d_2 : Block CycleSubmission.Artifact.artifact .Osaka 4434 r2d_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3507 28 4434 r2d_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3507 + 28 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 377 4434 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 377 28 r2d_2New rfl) (by decide)

def block_r2c3_2 : Block CycleSubmission.Artifact.artifact .Osaka 4462 r2c3_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3535 28 4462 r2c3_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3535 + 28 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 405 4462 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 405 28 r2c3_2New rfl) (by decide)

def block_r2e_2 : Block CycleSubmission.Artifact.artifact .Osaka 4492 r2e_2New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3563 5 4492 r2e_2New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3563 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 433 4492 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 433 5 r2e_2New rfl) (by decide)

def block_r3h_3 : Block CycleSubmission.Artifact.artifact .Osaka 4592 r3h_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3663 5 4592 r3h_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3663 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 533 4592 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 533 5 r3h_3New rfl) (by decide)

def block_r3d_3 : Block CycleSubmission.Artifact.artifact .Osaka 4602 r3d_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3669 25 4602 r3d_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3669 + 25 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 539 4602 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 539 25 r3d_3New rfl) (by decide)

def block_r3e_3 : Block CycleSubmission.Artifact.artifact .Osaka 4627 r3e_3New :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3694 5 4627 r3e_3New
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3694 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 564 4627 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 564 5 r3e_3New rfl) (by decide)

def entryProgram : List Instr := [.op .JUMPDEST, .push 2 4037, .op .JUMP]
def block_entry : Block CycleSubmission.Artifact.artifact .Osaka 3763 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2905 3 3763 entryProgram
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 2905 + 3 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)


theorem validJump5615 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4037 = true :=
  CycleSubmission.Global.Binding.jumpDest 3130 (by rfl)

end CycleSubmission.Global.Fast.R4InlineBlocks
