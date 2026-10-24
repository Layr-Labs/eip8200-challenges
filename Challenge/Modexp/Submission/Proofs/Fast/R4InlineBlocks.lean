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

def block_prodiag_0 : Block Artifact.submissionArtifact .Osaka 8997 prodiag_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6940 21 8997 prodiag_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6940 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 0 8997 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 0 21 prodiag_0New rfl) (by decide)

def block_r0z1_0 : Block Artifact.submissionArtifact .Osaka 9020 r0z1_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6961 21 9020 r0z1_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6961 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 21 9020 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 21 21 r0z1_0New rfl) (by decide)

def block_r0z2_0 : Block Artifact.submissionArtifact .Osaka 9043 r0z2_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6982 21 9043 r0z2_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6982 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 42 9043 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 42 21 r0z2_0New rfl) (by decide)

def block_r0z3_0 : Block Artifact.submissionArtifact .Osaka 9066 r0z3_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7003 21 9066 r0z3_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7003 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 63 9066 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 63 21 r0z3_0New rfl) (by decide)

def block_r0e_0 : Block Artifact.submissionArtifact .Osaka 9089 r0e_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7024 3 9089 r0e_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7024 + 3 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 84 9089 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 84 3 r0e_0New rfl) (by decide)

def block_redm_0 : Block Artifact.submissionArtifact .Osaka 9092 redm_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7027 10 9092 redm_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7027 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 87 9092 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 87 10 redm_0New rfl) (by decide)

def block_redm_1 : Block Artifact.submissionArtifact .Osaka 9289 redm_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7216 10 9289 redm_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7216 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 276 9289 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 276 10 redm_1New rfl) (by decide)

def block_redm_2 : Block Artifact.submissionArtifact .Osaka 9457 redm_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7378 10 9457 redm_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7378 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 438 9457 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 438 10 redm_2New rfl) (by decide)

def block_redm_3 : Block Artifact.submissionArtifact .Osaka 9592 redm_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7509 10 9592 redm_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7509 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 569 9592 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 569 10 redm_3New rfl) (by decide)

def block_reds1_0 : Block Artifact.submissionArtifact .Osaka 9102 reds1_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7037 25 9102 reds1_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7037 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 97 9102 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 97 25 reds1_0New rfl) (by decide)

def block_reds1_1 : Block Artifact.submissionArtifact .Osaka 9299 reds1_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7226 25 9299 reds1_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7226 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 286 9299 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 286 25 reds1_1New rfl) (by decide)

def block_reds1_2 : Block Artifact.submissionArtifact .Osaka 9467 reds1_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7388 25 9467 reds1_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7388 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 448 9467 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 448 25 reds1_2New rfl) (by decide)

def block_reds1_3 : Block Artifact.submissionArtifact .Osaka 9602 reds1_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7519 25 9602 reds1_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7519 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 579 9602 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 579 25 reds1_3New rfl) (by decide)

def block_reds2_0 : Block Artifact.submissionArtifact .Osaka 9127 reds2_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7062 25 9127 reds2_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7062 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 122 9127 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 122 25 reds2_0New rfl) (by decide)

def block_reds2_1 : Block Artifact.submissionArtifact .Osaka 9324 reds2_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7251 25 9324 reds2_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7251 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 311 9324 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 311 25 reds2_1New rfl) (by decide)

def block_reds2_2 : Block Artifact.submissionArtifact .Osaka 9492 reds2_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7413 25 9492 reds2_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7413 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 473 9492 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 473 25 reds2_2New rfl) (by decide)

def block_reds2_3 : Block Artifact.submissionArtifact .Osaka 9627 reds2_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7544 25 9627 reds2_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7544 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 604 9627 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 604 25 reds2_3New rfl) (by decide)

def block_reds3_0 : Block Artifact.submissionArtifact .Osaka 9152 reds3_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7087 25 9152 reds3_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7087 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 147 9152 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 147 25 reds3_0New rfl) (by decide)

def block_reds3_1 : Block Artifact.submissionArtifact .Osaka 9349 reds3_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7276 25 9349 reds3_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7276 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 336 9349 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 336 25 reds3_1New rfl) (by decide)

def block_reds3_2 : Block Artifact.submissionArtifact .Osaka 9517 reds3_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7438 25 9517 reds3_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7438 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 498 9517 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 498 25 reds3_2New rfl) (by decide)

def block_reds3_3 : Block Artifact.submissionArtifact .Osaka 9652 reds3_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7569 25 9652 reds3_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7569 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 629 9652 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 629 25 reds3_3New rfl) (by decide)

def block_redt_0 : Block Artifact.submissionArtifact .Osaka 9177 redt_0New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7112 10 9177 redt_0New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7112 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 172 9177 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 172 10 redt_0New rfl) (by decide)

def block_redt_1 : Block Artifact.submissionArtifact .Osaka 9374 redt_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7301 10 9374 redt_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7301 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 361 9374 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 361 10 redt_1New rfl) (by decide)

def block_redt_2 : Block Artifact.submissionArtifact .Osaka 9542 redt_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7463 10 9542 redt_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7463 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 523 9542 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 523 10 redt_2New rfl) (by decide)

def block_redt_3 : Block Artifact.submissionArtifact .Osaka 9677 redt_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7594 10 9677 redt_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7594 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 654 9677 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 654 10 redt_3New rfl) (by decide)

def block_r1h_1 : Block Artifact.submissionArtifact .Osaka 9187 r1h_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7122 5 9187 r1h_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7122 + 5 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 182 9187 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 182 5 r1h_1New rfl) (by decide)

def block_r1d_1 : Block Artifact.submissionArtifact .Osaka 9197 r1d_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7128 28 9197 r1d_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7128 + 28 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 188 9197 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 188 28 r1d_1New rfl) (by decide)

def block_r1c2_1 : Block Artifact.submissionArtifact .Osaka 9225 r1c2_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7156 27 9225 r1c2_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7156 + 27 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 216 9225 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 216 27 r1c2_1New rfl) (by decide)

def block_r1c3_1 : Block Artifact.submissionArtifact .Osaka 9254 r1c3_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7183 28 9254 r1c3_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7183 + 28 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 243 9254 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 243 28 r1c3_1New rfl) (by decide)

def block_r1e_1 : Block Artifact.submissionArtifact .Osaka 9284 r1e_1New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7211 5 9284 r1e_1New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7211 + 5 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 271 9284 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 271 5 r1e_1New rfl) (by decide)

def block_r2h_2 : Block Artifact.submissionArtifact .Osaka 9384 r2h_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7311 5 9384 r2h_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7311 + 5 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 371 9384 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 371 5 r2h_2New rfl) (by decide)

def block_r2d_2 : Block Artifact.submissionArtifact .Osaka 9394 r2d_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7317 28 9394 r2d_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7317 + 28 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 377 9394 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 377 28 r2d_2New rfl) (by decide)

def block_r2c3_2 : Block Artifact.submissionArtifact .Osaka 9422 r2c3_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7345 28 9422 r2c3_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7345 + 28 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 405 9422 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 405 28 r2c3_2New rfl) (by decide)

def block_r2e_2 : Block Artifact.submissionArtifact .Osaka 9452 r2e_2New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7373 5 9452 r2e_2New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7373 + 5 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 433 9452 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 433 5 r2e_2New rfl) (by decide)

def block_r3h_3 : Block Artifact.submissionArtifact .Osaka 9552 r3h_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7473 5 9552 r3h_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7473 + 5 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 533 9552 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 533 5 r3h_3New rfl) (by decide)

def block_r3d_3 : Block Artifact.submissionArtifact .Osaka 9562 r3d_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7479 25 9562 r3d_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7479 + 25 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 539 9562 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 539 25 r3d_3New rfl) (by decide)

def block_r3e_3 : Block Artifact.submissionArtifact .Osaka 9587 r3e_3New :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7504 5 9587 r3e_3New
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7504 + 5 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 564 9587 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 564 5 r3e_3New rfl) (by decide)

def entryProgram : List Instr := [.op .JUMPDEST, .push 2 8997, .op .JUMP]
def block_entry : Block Artifact.submissionArtifact .Osaka 4280 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3328 3 4280 entryProgram
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3328 + 3 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)


theorem validJump5615 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8997 = true :=
  Artifact.isValidJumpDest_index 6940 (by rfl)

theorem validJump4725 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4725 = true :=
  Artifact.isValidJumpDest_index 3733 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.R4InlineBlocks
