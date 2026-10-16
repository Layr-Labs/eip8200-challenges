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
  WindowTwentyOneSlice.block Artifact.allWellFormed 7025 4 9090 r0e_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7025 + 4 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 84 9090 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 84 4 r0e_0New rfl) (by decide)

def block_redm_0 : Block Artifact.submissionArtifact .Osaka 9096 redm_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7029 10 9096 redm_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7029 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 88 9096 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 88 10 redm_0New rfl) (by decide)

def block_redm_1 : Block Artifact.submissionArtifact .Osaka 9299 redm_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7222 10 9299 redm_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7222 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 281 9299 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 281 10 redm_1New rfl) (by decide)

def block_redm_2 : Block Artifact.submissionArtifact .Osaka 9473 redm_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7388 10 9473 redm_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7388 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 447 9473 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 447 10 redm_2New rfl) (by decide)

def block_redm_3 : Block Artifact.submissionArtifact .Osaka 9613 redm_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7522 10 9613 redm_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7522 + 10 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 581 9613 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 581 10 redm_3New rfl) (by decide)

def block_reds1_0 : Block Artifact.submissionArtifact .Osaka 9106 reds1_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7039 25 9106 reds1_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7039 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 98 9106 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 98 25 reds1_0New rfl) (by decide)

def block_reds1_1 : Block Artifact.submissionArtifact .Osaka 9309 reds1_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7232 25 9309 reds1_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7232 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 291 9309 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 291 25 reds1_1New rfl) (by decide)

def block_reds1_2 : Block Artifact.submissionArtifact .Osaka 9483 reds1_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7398 25 9483 reds1_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7398 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 457 9483 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 457 25 reds1_2New rfl) (by decide)

def block_reds1_3 : Block Artifact.submissionArtifact .Osaka 9623 reds1_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7532 25 9623 reds1_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7532 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 591 9623 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 591 25 reds1_3New rfl) (by decide)

def block_reds2_0 : Block Artifact.submissionArtifact .Osaka 9131 reds2_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7064 25 9131 reds2_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7064 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 123 9131 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 123 25 reds2_0New rfl) (by decide)

def block_reds2_1 : Block Artifact.submissionArtifact .Osaka 9334 reds2_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7257 25 9334 reds2_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7257 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 316 9334 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 316 25 reds2_1New rfl) (by decide)

def block_reds2_2 : Block Artifact.submissionArtifact .Osaka 9508 reds2_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7423 25 9508 reds2_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7423 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 482 9508 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 482 25 reds2_2New rfl) (by decide)

def block_reds2_3 : Block Artifact.submissionArtifact .Osaka 9648 reds2_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7557 25 9648 reds2_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7557 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 616 9648 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 616 25 reds2_3New rfl) (by decide)

def block_reds3_0 : Block Artifact.submissionArtifact .Osaka 9156 reds3_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7089 25 9156 reds3_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7089 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 148 9156 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 148 25 reds3_0New rfl) (by decide)

def block_reds3_1 : Block Artifact.submissionArtifact .Osaka 9359 reds3_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7282 25 9359 reds3_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7282 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 341 9359 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 341 25 reds3_1New rfl) (by decide)

def block_reds3_2 : Block Artifact.submissionArtifact .Osaka 9533 reds3_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7448 25 9533 reds3_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7448 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 507 9533 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 507 25 reds3_2New rfl) (by decide)

def block_reds3_3 : Block Artifact.submissionArtifact .Osaka 9673 reds3_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7582 25 9673 reds3_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7582 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 641 9673 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 641 25 reds3_3New rfl) (by decide)

def block_redt_0 : Block Artifact.submissionArtifact .Osaka 9181 redt_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7114 11 9181 redt_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7114 + 11 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 173 9181 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 173 11 redt_0New rfl) (by decide)

def block_redt_1 : Block Artifact.submissionArtifact .Osaka 9384 redt_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7307 11 9384 redt_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7307 + 11 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 366 9384 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 366 11 redt_1New rfl) (by decide)

def block_redt_2 : Block Artifact.submissionArtifact .Osaka 9558 redt_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7473 11 9558 redt_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7473 + 11 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 532 9558 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 532 11 redt_2New rfl) (by decide)

def block_redt_3 : Block Artifact.submissionArtifact .Osaka 9698 redt_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7607 11 9698 redt_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7607 + 11 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 666 9698 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 666 11 redt_3New rfl) (by decide)

def block_r1h_1 : Block Artifact.submissionArtifact .Osaka 9192 r1h_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7125 6 9192 r1h_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7125 + 6 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 184 9192 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 184 6 r1h_1New rfl) (by decide)

def block_r1d_1 : Block Artifact.submissionArtifact .Osaka 9203 r1d_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7132 28 9203 r1d_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7132 + 28 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 191 9203 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 191 28 r1d_1New rfl) (by decide)

def block_r1c2_1 : Block Artifact.submissionArtifact .Osaka 9231 r1c2_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7160 27 9231 r1c2_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7160 + 27 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 219 9231 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 219 27 r1c2_1New rfl) (by decide)

def block_r1c3_1 : Block Artifact.submissionArtifact .Osaka 9260 r1c3_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7187 27 9260 r1c3_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7187 + 27 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 246 9260 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 246 27 r1c3_1New rfl) (by decide)

def block_r1e_1 : Block Artifact.submissionArtifact .Osaka 9289 r1e_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7214 8 9289 r1e_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7214 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 273 9289 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 273 8 r1e_1New rfl) (by decide)

def block_r2h_2 : Block Artifact.submissionArtifact .Osaka 9395 r2h_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7318 6 9395 r2h_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7318 + 6 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 377 9395 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 377 6 r2h_2New rfl) (by decide)

def block_r2d_2 : Block Artifact.submissionArtifact .Osaka 9406 r2d_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7325 28 9406 r2d_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7325 + 28 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 384 9406 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 384 28 r2d_2New rfl) (by decide)

def block_r2c3_2 : Block Artifact.submissionArtifact .Osaka 9434 r2c3_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7353 27 9434 r2c3_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7353 + 27 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 412 9434 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 412 27 r2c3_2New rfl) (by decide)

def block_r2e_2 : Block Artifact.submissionArtifact .Osaka 9463 r2e_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7380 8 9463 r2e_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7380 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 439 9463 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 439 8 r2e_2New rfl) (by decide)

def block_r3h_3 : Block Artifact.submissionArtifact .Osaka 9569 r3h_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7484 6 9569 r3h_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7484 + 6 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 543 9569 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 543 6 r3h_3New rfl) (by decide)

def block_r3d_3 : Block Artifact.submissionArtifact .Osaka 9580 r3d_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7491 25 9580 r3d_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7491 + 25 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 550 9580 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 550 25 r3d_3New rfl) (by decide)

def block_r3e_3 : Block Artifact.submissionArtifact .Osaka 9605 r3e_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7516 6 9605 r3e_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7516 + 6 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 575 9605 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 575 6 r3e_3New rfl) (by decide)

def entryProgram : List Instr := [.op .JUMPDEST, .push 2 8998, .op .JUMP]
def block_entry : Block Artifact.submissionArtifact .Osaka 4280 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3328 3 4280 entryProgram
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3328 + 3 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)


theorem validJump5615 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8998 = true :=
  Artifact.isValidJumpDest_index 6941 (by rfl)

theorem validJump4725 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4725 = true :=
  Artifact.isValidJumpDest_index 3733 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.R4InlineBlocks
