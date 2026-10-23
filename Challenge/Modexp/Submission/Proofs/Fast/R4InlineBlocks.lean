import Challenge.Modexp.Submission.Proofs.Fast.R4InlineArtifactSuffix
import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineProdiag0
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR0z10
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR0z20
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR0z30
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR0e0
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedm0
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedm1
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedm2
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedm3
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds10
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds11
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds12
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds13
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds20
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds21
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds22
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds23
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds30
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds31
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds32
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineReds33
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedt0
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedt1
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedt2
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineRedt3
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR1h1
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR1d1
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR1c21
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR1c31
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR1e1
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR2h2
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR2d2
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR2c32
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR2e2
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR3h3
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR3d3
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineR3e3
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.R4InlineBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

def block_prodiag_0 : Block Artifact.submissionArtifact .Osaka 8998 prodiag_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6941 21 8998 prodiag_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6941 + 21 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 0 8998 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 0 21 prodiag_0New rfl) (by decide)

def block_r0z1_0 : Block Artifact.submissionArtifact .Osaka 9021 r0z1_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6962 21 9021 r0z1_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6962 + 21 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 21 9021 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 21 21 r0z1_0New rfl) (by decide)

def block_r0z2_0 : Block Artifact.submissionArtifact .Osaka 9044 r0z2_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6983 21 9044 r0z2_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6983 + 21 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 42 9044 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 42 21 r0z2_0New rfl) (by decide)

def block_r0z3_0 : Block Artifact.submissionArtifact .Osaka 9067 r0z3_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7004 21 9067 r0z3_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7004 + 21 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 63 9067 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 63 21 r0z3_0New rfl) (by decide)

def block_r0e_0 : Block Artifact.submissionArtifact .Osaka 9090 r0e_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7025 3 9090 r0e_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7025 + 3 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 84 9090 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 84 3 r0e_0New rfl) (by decide)

def block_redm_0 : Block Artifact.submissionArtifact .Osaka 9093 redm_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7028 10 9093 redm_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7028 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 87 9093 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 87 10 redm_0New rfl) (by decide)

def block_redm_1 : Block Artifact.submissionArtifact .Osaka 9290 redm_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7217 10 9290 redm_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7217 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 276 9290 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 276 10 redm_1New rfl) (by decide)

def block_redm_2 : Block Artifact.submissionArtifact .Osaka 9458 redm_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7379 10 9458 redm_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7379 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 438 9458 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 438 10 redm_2New rfl) (by decide)

def block_redm_3 : Block Artifact.submissionArtifact .Osaka 9593 redm_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7510 10 9593 redm_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7510 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 569 9593 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 569 10 redm_3New rfl) (by decide)

def block_reds1_0 : Block Artifact.submissionArtifact .Osaka 9103 reds1_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7038 25 9103 reds1_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7038 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 97 9103 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 97 25 reds1_0New rfl) (by decide)

def block_reds1_1 : Block Artifact.submissionArtifact .Osaka 9300 reds1_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7227 25 9300 reds1_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7227 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 286 9300 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 286 25 reds1_1New rfl) (by decide)

def block_reds1_2 : Block Artifact.submissionArtifact .Osaka 9468 reds1_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7389 25 9468 reds1_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7389 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 448 9468 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 448 25 reds1_2New rfl) (by decide)

def block_reds1_3 : Block Artifact.submissionArtifact .Osaka 9603 reds1_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7520 25 9603 reds1_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7520 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 579 9603 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 579 25 reds1_3New rfl) (by decide)

def block_reds2_0 : Block Artifact.submissionArtifact .Osaka 9128 reds2_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7063 25 9128 reds2_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7063 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 122 9128 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 122 25 reds2_0New rfl) (by decide)

def block_reds2_1 : Block Artifact.submissionArtifact .Osaka 9325 reds2_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7252 25 9325 reds2_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7252 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 311 9325 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 311 25 reds2_1New rfl) (by decide)

def block_reds2_2 : Block Artifact.submissionArtifact .Osaka 9493 reds2_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7414 25 9493 reds2_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7414 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 473 9493 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 473 25 reds2_2New rfl) (by decide)

def block_reds2_3 : Block Artifact.submissionArtifact .Osaka 9628 reds2_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7545 25 9628 reds2_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7545 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 604 9628 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 604 25 reds2_3New rfl) (by decide)

def block_reds3_0 : Block Artifact.submissionArtifact .Osaka 9153 reds3_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7088 25 9153 reds3_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7088 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 147 9153 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 147 25 reds3_0New rfl) (by decide)

def block_reds3_1 : Block Artifact.submissionArtifact .Osaka 9350 reds3_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7277 25 9350 reds3_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7277 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 336 9350 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 336 25 reds3_1New rfl) (by decide)

def block_reds3_2 : Block Artifact.submissionArtifact .Osaka 9518 reds3_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7439 25 9518 reds3_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7439 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 498 9518 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 498 25 reds3_2New rfl) (by decide)

def block_reds3_3 : Block Artifact.submissionArtifact .Osaka 9653 reds3_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7570 25 9653 reds3_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7570 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 629 9653 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 629 25 reds3_3New rfl) (by decide)

def block_redt_0 : Block Artifact.submissionArtifact .Osaka 9178 redt_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7113 10 9178 redt_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7113 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 172 9178 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 172 10 redt_0New rfl) (by decide)

def block_redt_1 : Block Artifact.submissionArtifact .Osaka 9375 redt_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7302 10 9375 redt_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7302 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 361 9375 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 361 10 redt_1New rfl) (by decide)

def block_redt_2 : Block Artifact.submissionArtifact .Osaka 9543 redt_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7464 10 9543 redt_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7464 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 523 9543 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 523 10 redt_2New rfl) (by decide)

def block_redt_3 : Block Artifact.submissionArtifact .Osaka 9678 redt_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7595 10 9678 redt_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7595 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 654 9678 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 654 10 redt_3New rfl) (by decide)

def block_r1h_1 : Block Artifact.submissionArtifact .Osaka 9188 r1h_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7123 5 9188 r1h_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7123 + 5 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 182 9188 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 182 5 r1h_1New rfl) (by decide)

def block_r1d_1 : Block Artifact.submissionArtifact .Osaka 9198 r1d_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7129 28 9198 r1d_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7129 + 28 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 188 9198 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 188 28 r1d_1New rfl) (by decide)

def block_r1c2_1 : Block Artifact.submissionArtifact .Osaka 9226 r1c2_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7157 27 9226 r1c2_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7157 + 27 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 216 9226 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 216 27 r1c2_1New rfl) (by decide)

def block_r1c3_1 : Block Artifact.submissionArtifact .Osaka 9255 r1c3_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7184 28 9255 r1c3_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7184 + 28 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 243 9255 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 243 28 r1c3_1New rfl) (by decide)

def block_r1e_1 : Block Artifact.submissionArtifact .Osaka 9285 r1e_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7212 5 9285 r1e_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7212 + 5 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 271 9285 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 271 5 r1e_1New rfl) (by decide)

def block_r2h_2 : Block Artifact.submissionArtifact .Osaka 9385 r2h_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7312 5 9385 r2h_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7312 + 5 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 371 9385 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 371 5 r2h_2New rfl) (by decide)

def block_r2d_2 : Block Artifact.submissionArtifact .Osaka 9395 r2d_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7318 28 9395 r2d_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7318 + 28 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 377 9395 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 377 28 r2d_2New rfl) (by decide)

def block_r2c3_2 : Block Artifact.submissionArtifact .Osaka 9423 r2c3_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7346 28 9423 r2c3_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7346 + 28 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 405 9423 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 405 28 r2c3_2New rfl) (by decide)

def block_r2e_2 : Block Artifact.submissionArtifact .Osaka 9453 r2e_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7374 5 9453 r2e_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7374 + 5 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 433 9453 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 433 5 r2e_2New rfl) (by decide)

def block_r3h_3 : Block Artifact.submissionArtifact .Osaka 9553 r3h_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7474 5 9553 r3h_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7474 + 5 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 533 9553 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 533 5 r3h_3New rfl) (by decide)

def block_r3d_3 : Block Artifact.submissionArtifact .Osaka 9563 r3d_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7480 25 9563 r3d_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7480 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 539 9563 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 539 25 r3d_3New rfl) (by decide)

def block_r3e_3 : Block Artifact.submissionArtifact .Osaka 9588 r3e_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7505 5 9588 r3e_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7505 + 5 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 564 9588 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 564 5 r3e_3New rfl) (by decide)

def entryProgram : List Instr := [.push 2 8998, .op .JUMP]
def block_entry : Block Artifact.submissionArtifact .Osaka 4280 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3328 2 4280 entryProgram
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3328 + 2 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)


theorem validJump5615 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8998 = true :=
  Artifact.isValidJumpDest_index 6941 (by rfl)

theorem validJump4725 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4725 = true :=
  Artifact.isValidJumpDest_index 3733 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.R4InlineBlocks
