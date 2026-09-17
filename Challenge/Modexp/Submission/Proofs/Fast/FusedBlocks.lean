import Challenge.Modexp.Submission.Proofs.Fast.FusedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Located blocks of the fused R8-square region. Generated. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

def b_entry : Block Artifact.submissionArtifact .Osaka 5314 [.op .JUMPDEST] :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4104 1 5314 [.op .JUMPDEST]
    (by decide) (by rfl) (by rfl) (by decide)

def b_pro : Block Artifact.submissionArtifact .Osaka 5315 (FusedPrograms.prologuePOPProgram (UInt256.ofNat 3417)) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4105 213 5315 (FusedPrograms.prologuePOPProgram (UInt256.ofNat 3417))
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_0 : Block Artifact.submissionArtifact .Osaka 5561 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4318 1 5561 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_1 : Block Artifact.submissionArtifact .Osaka 5562 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4319 30 5562 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_2 : Block Artifact.submissionArtifact .Osaka 5606 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4349 30 5606 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_3 : Block Artifact.submissionArtifact .Osaka 5641 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4379 30 5641 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_4 : Block Artifact.submissionArtifact .Osaka 5676 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4409 28 5676 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_5 : Block Artifact.submissionArtifact .Osaka 5709 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4437 1 5709 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_6 : Block Artifact.submissionArtifact .Osaka 5710 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4438 29 5710 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_7 : Block Artifact.submissionArtifact .Osaka 5743 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4467 29 5743 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_8 : Block Artifact.submissionArtifact .Osaka 5776 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4496 29 5776 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j0_9 : Block Artifact.submissionArtifact .Osaka 5809 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4525 11 5809 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th0 : Block Artifact.submissionArtifact .Osaka 5826 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4536 4 5826 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g0_0 : Block Artifact.submissionArtifact .Osaka 5830 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4540 6 5830 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g0_2 : Block Artifact.submissionArtifact .Osaka 5837 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4547 8 5837 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g0_3 : Block Artifact.submissionArtifact .Osaka 5845 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4555 16 5845 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g0_4 : Block Artifact.submissionArtifact .Osaka 5863 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4571 11 5863 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g0_5 : Block Artifact.submissionArtifact .Osaka 5874 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4582 5 5874 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_0 : Block Artifact.submissionArtifact .Osaka 5880 (StagedOperand.stepProgram 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4587 31 5880 (StagedOperand.stepProgram 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_1 : Block Artifact.submissionArtifact .Osaka 5917 (StagedOperand.stepProgram 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4618 31 5917 (StagedOperand.stepProgram 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_2 : Block Artifact.submissionArtifact .Osaka 5954 (StagedOperand.stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4649 31 5954 (StagedOperand.stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_3 : Block Artifact.submissionArtifact .Osaka 5991 (StagedOperand.stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4680 31 5991 (StagedOperand.stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_4 : Block Artifact.submissionArtifact .Osaka 6028 (StagedOperand.stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4711 31 6028 (StagedOperand.stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_5 : Block Artifact.submissionArtifact .Osaka 6065 (StagedOperand.stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4742 31 6065 (StagedOperand.stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c0_mid : Block Artifact.submissionArtifact .Osaka 6102 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4773 23 6102 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_0 : Block Artifact.submissionArtifact .Osaka 6131 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4796 1 6131 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_1 : Block Artifact.submissionArtifact .Osaka 6132 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4797 30 6132 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_2 : Block Artifact.submissionArtifact .Osaka 6176 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4827 30 6176 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_3 : Block Artifact.submissionArtifact .Osaka 6211 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4857 30 6211 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_4 : Block Artifact.submissionArtifact .Osaka 6246 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4887 28 6246 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_5 : Block Artifact.submissionArtifact .Osaka 6279 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4915 1 6279 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_6 : Block Artifact.submissionArtifact .Osaka 6280 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4916 29 6280 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_7 : Block Artifact.submissionArtifact .Osaka 6313 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4945 29 6313 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_8 : Block Artifact.submissionArtifact .Osaka 6346 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4974 29 6346 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j1_9 : Block Artifact.submissionArtifact .Osaka 6379 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5003 11 6379 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th1 : Block Artifact.submissionArtifact .Osaka 6396 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5014 4 6396 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g1_0 : Block Artifact.submissionArtifact .Osaka 6400 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5018 6 6400 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g1_2 : Block Artifact.submissionArtifact .Osaka 6407 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5025 8 6407 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g1_3 : Block Artifact.submissionArtifact .Osaka 6415 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5033 16 6415 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g1_4 : Block Artifact.submissionArtifact .Osaka 6433 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5049 11 6433 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g1_5 : Block Artifact.submissionArtifact .Osaka 6444 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5060 5 6444 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_c1_1 : Block Artifact.submissionArtifact .Osaka 6450 (StagedOperand.stepProgram 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5065 31 6450 (StagedOperand.stepProgram 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c1_2 : Block Artifact.submissionArtifact .Osaka 6487 (StagedOperand.stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5096 31 6487 (StagedOperand.stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c1_3 : Block Artifact.submissionArtifact .Osaka 6524 (StagedOperand.stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5127 31 6524 (StagedOperand.stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c1_4 : Block Artifact.submissionArtifact .Osaka 6561 (StagedOperand.stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5158 31 6561 (StagedOperand.stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c1_5 : Block Artifact.submissionArtifact .Osaka 6598 (StagedOperand.stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5189 31 6598 (StagedOperand.stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c1_mid : Block Artifact.submissionArtifact .Osaka 6635 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5220 23 6635 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_0 : Block Artifact.submissionArtifact .Osaka 6664 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5243 1 6664 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_1 : Block Artifact.submissionArtifact .Osaka 6665 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5244 30 6665 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_2 : Block Artifact.submissionArtifact .Osaka 6709 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5274 30 6709 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_3 : Block Artifact.submissionArtifact .Osaka 6744 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5304 30 6744 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_4 : Block Artifact.submissionArtifact .Osaka 6779 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5334 28 6779 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_5 : Block Artifact.submissionArtifact .Osaka 6812 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5362 1 6812 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_6 : Block Artifact.submissionArtifact .Osaka 6813 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5363 29 6813 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_7 : Block Artifact.submissionArtifact .Osaka 6846 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5392 29 6846 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_8 : Block Artifact.submissionArtifact .Osaka 6879 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5421 29 6879 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j2_9 : Block Artifact.submissionArtifact .Osaka 6912 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5450 11 6912 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th2 : Block Artifact.submissionArtifact .Osaka 6929 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5461 4 6929 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g2_0 : Block Artifact.submissionArtifact .Osaka 6933 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5465 6 6933 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g2_2 : Block Artifact.submissionArtifact .Osaka 6940 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5472 8 6940 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g2_3 : Block Artifact.submissionArtifact .Osaka 6948 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5480 16 6948 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g2_4 : Block Artifact.submissionArtifact .Osaka 6966 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5496 11 6966 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g2_5 : Block Artifact.submissionArtifact .Osaka 6977 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5507 5 6977 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_c2_2 : Block Artifact.submissionArtifact .Osaka 6983 (StagedOperand.stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5512 31 6983 (StagedOperand.stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c2_3 : Block Artifact.submissionArtifact .Osaka 7020 (StagedOperand.stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5543 31 7020 (StagedOperand.stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c2_4 : Block Artifact.submissionArtifact .Osaka 7057 (StagedOperand.stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5574 31 7057 (StagedOperand.stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c2_5 : Block Artifact.submissionArtifact .Osaka 7094 (StagedOperand.stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5605 31 7094 (StagedOperand.stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c2_mid : Block Artifact.submissionArtifact .Osaka 7131 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5636 23 7131 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_0 : Block Artifact.submissionArtifact .Osaka 7160 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5659 1 7160 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_1 : Block Artifact.submissionArtifact .Osaka 7161 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5660 30 7161 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_2 : Block Artifact.submissionArtifact .Osaka 7205 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5690 30 7205 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_3 : Block Artifact.submissionArtifact .Osaka 7240 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5720 30 7240 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_4 : Block Artifact.submissionArtifact .Osaka 7275 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5750 28 7275 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_5 : Block Artifact.submissionArtifact .Osaka 7308 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5778 1 7308 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_6 : Block Artifact.submissionArtifact .Osaka 7309 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5779 29 7309 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_7 : Block Artifact.submissionArtifact .Osaka 7342 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5808 29 7342 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_8 : Block Artifact.submissionArtifact .Osaka 7375 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5837 29 7375 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j3_9 : Block Artifact.submissionArtifact .Osaka 7408 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5866 11 7408 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th3 : Block Artifact.submissionArtifact .Osaka 7425 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5877 4 7425 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g3_0 : Block Artifact.submissionArtifact .Osaka 7429 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5881 6 7429 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g3_2 : Block Artifact.submissionArtifact .Osaka 7436 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5888 8 7436 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g3_3 : Block Artifact.submissionArtifact .Osaka 7444 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5896 16 7444 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g3_4 : Block Artifact.submissionArtifact .Osaka 7462 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5912 11 7462 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g3_5 : Block Artifact.submissionArtifact .Osaka 7473 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5923 5 7473 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_c3_3 : Block Artifact.submissionArtifact .Osaka 7479 (StagedOperand.stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5928 31 7479 (StagedOperand.stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c3_4 : Block Artifact.submissionArtifact .Osaka 7516 (StagedOperand.stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5959 31 7516 (StagedOperand.stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c3_5 : Block Artifact.submissionArtifact .Osaka 7553 (StagedOperand.stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5990 31 7553 (StagedOperand.stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c3_mid : Block Artifact.submissionArtifact .Osaka 7590 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6021 23 7590 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_0 : Block Artifact.submissionArtifact .Osaka 7619 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6044 1 7619 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_1 : Block Artifact.submissionArtifact .Osaka 7620 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6045 30 7620 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_2 : Block Artifact.submissionArtifact .Osaka 7664 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6075 30 7664 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_3 : Block Artifact.submissionArtifact .Osaka 7699 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6105 30 7699 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_4 : Block Artifact.submissionArtifact .Osaka 7734 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6135 28 7734 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_5 : Block Artifact.submissionArtifact .Osaka 7767 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6163 1 7767 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_6 : Block Artifact.submissionArtifact .Osaka 7768 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6164 29 7768 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_7 : Block Artifact.submissionArtifact .Osaka 7801 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6193 29 7801 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_8 : Block Artifact.submissionArtifact .Osaka 7834 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6222 29 7834 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j4_9 : Block Artifact.submissionArtifact .Osaka 7867 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6251 11 7867 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th4 : Block Artifact.submissionArtifact .Osaka 7884 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6262 4 7884 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g4_0 : Block Artifact.submissionArtifact .Osaka 7888 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6266 6 7888 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g4_2 : Block Artifact.submissionArtifact .Osaka 7895 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6273 8 7895 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g4_3 : Block Artifact.submissionArtifact .Osaka 7903 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6281 16 7903 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g4_4 : Block Artifact.submissionArtifact .Osaka 7921 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6297 11 7921 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g4_5 : Block Artifact.submissionArtifact .Osaka 7932 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6308 5 7932 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_c4_4 : Block Artifact.submissionArtifact .Osaka 7938 (StagedOperand.stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6313 31 7938 (StagedOperand.stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c4_5 : Block Artifact.submissionArtifact .Osaka 7975 (StagedOperand.stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6344 31 7975 (StagedOperand.stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c4_mid : Block Artifact.submissionArtifact .Osaka 8012 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6375 23 8012 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_0 : Block Artifact.submissionArtifact .Osaka 8041 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6398 1 8041 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_1 : Block Artifact.submissionArtifact .Osaka 8042 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6399 30 8042 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_2 : Block Artifact.submissionArtifact .Osaka 8086 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6429 30 8086 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_3 : Block Artifact.submissionArtifact .Osaka 8121 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6459 30 8121 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_4 : Block Artifact.submissionArtifact .Osaka 8156 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6489 28 8156 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_5 : Block Artifact.submissionArtifact .Osaka 8189 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6517 1 8189 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_6 : Block Artifact.submissionArtifact .Osaka 8190 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6518 29 8190 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_7 : Block Artifact.submissionArtifact .Osaka 8223 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6547 29 8223 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_8 : Block Artifact.submissionArtifact .Osaka 8256 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6576 29 8256 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j5_9 : Block Artifact.submissionArtifact .Osaka 8289 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6605 11 8289 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th5 : Block Artifact.submissionArtifact .Osaka 8306 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6616 4 8306 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g5_0 : Block Artifact.submissionArtifact .Osaka 8310 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6620 6 8310 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g5_2 : Block Artifact.submissionArtifact .Osaka 8317 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6627 8 8317 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g5_3 : Block Artifact.submissionArtifact .Osaka 8325 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6635 16 8325 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g5_4 : Block Artifact.submissionArtifact .Osaka 8343 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6651 11 8343 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g5_5 : Block Artifact.submissionArtifact .Osaka 8354 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6662 5 8354 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_c5_5 : Block Artifact.submissionArtifact .Osaka 8360 (StagedOperand.stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6667 31 8360 (StagedOperand.stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def b_c5_mid : Block Artifact.submissionArtifact .Osaka 8397 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6698 23 8397 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_0 : Block Artifact.submissionArtifact .Osaka 8426 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6721 1 8426 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_1 : Block Artifact.submissionArtifact .Osaka 8427 (CiosCached.l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6722 30 8427 (CiosCached.l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_2 : Block Artifact.submissionArtifact .Osaka 8471 (CiosCached.l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6752 30 8471 (CiosCached.l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_3 : Block Artifact.submissionArtifact .Osaka 8506 (CiosCached.l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6782 30 8506 (CiosCached.l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_4 : Block Artifact.submissionArtifact .Osaka 8541 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6812 28 8541 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_5 : Block Artifact.submissionArtifact .Osaka 8574 CiosCached.joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6840 1 8574 CiosCached.joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_6 : Block Artifact.submissionArtifact .Osaka 8575 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6841 29 8575 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_7 : Block Artifact.submissionArtifact .Osaka 8608 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6870 29 8608 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_8 : Block Artifact.submissionArtifact .Osaka 8641 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6899 29 8641 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def b_j6_9 : Block Artifact.submissionArtifact .Osaka 8674 CarryRowPrograms.tailStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6928 11 8674 CarryRowPrograms.tailStore
    (by decide) (by rfl) (by rfl) (by decide)

def b_th6 : Block Artifact.submissionArtifact .Osaka 8691 FusedPrograms.headPOPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6939 4 8691 FusedPrograms.headPOPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_g6_0 : Block Artifact.submissionArtifact .Osaka 8695 SquareRow.programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6943 6 8695 SquareRow.programA
    (by decide) (by rfl) (by rfl) (by decide)

def b_g6_2 : Block Artifact.submissionArtifact .Osaka 8702 SquareRow.programB1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6950 8 8702 SquareRow.programB1
    (by decide) (by rfl) (by rfl) (by decide)

def b_g6_3 : Block Artifact.submissionArtifact .Osaka 8710 SquareRow.programB23a :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6958 16 8710 SquareRow.programB23a
    (by decide) (by rfl) (by rfl) (by decide)

def b_g6_4 : Block Artifact.submissionArtifact .Osaka 8728 SquareRow.programB23b :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6974 11 8728 SquareRow.programB23b
    (by decide) (by rfl) (by rfl) (by decide)

def b_g6_5 : Block Artifact.submissionArtifact .Osaka 8739 FusedPrograms.b4POPProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6985 5 8739 FusedPrograms.b4POPProgram
    (by decide) (by rfl) (by rfl) (by decide)

def b_rejoin : Block Artifact.submissionArtifact .Osaka 8745 FusedPrograms.rejoinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6990 2 8745 FusedPrograms.rejoinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestFused : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5314 = true :=
  Artifact.isValidJumpDest_index 4104 (by rfl)

/-- Fused `SGT` locations (index, pc), one per glued row. -/
theorem sgtIndex0 : Artifact.submissionInstructions[4546]? = some (.op .SGT) := by
  rfl
theorem sgtPC0 : Artifact.submissionArtifact.instructionPC 4546 = 5836 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem sgtIndex1 : Artifact.submissionInstructions[5024]? = some (.op .SGT) := by
  rfl
theorem sgtPC1 : Artifact.submissionArtifact.instructionPC 5024 = 6406 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem sgtIndex2 : Artifact.submissionInstructions[5471]? = some (.op .SGT) := by
  rfl
theorem sgtPC2 : Artifact.submissionArtifact.instructionPC 5471 = 6939 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem sgtIndex3 : Artifact.submissionInstructions[5887]? = some (.op .SGT) := by
  rfl
theorem sgtPC3 : Artifact.submissionArtifact.instructionPC 5887 = 7435 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem sgtIndex4 : Artifact.submissionInstructions[6272]? = some (.op .SGT) := by
  rfl
theorem sgtPC4 : Artifact.submissionArtifact.instructionPC 6272 = 7894 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem sgtIndex5 : Artifact.submissionInstructions[6626]? = some (.op .SGT) := by
  rfl
theorem sgtPC5 : Artifact.submissionArtifact.instructionPC 6626 = 8316 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem sgtIndex6 : Artifact.submissionInstructions[6949]? = some (.op .SGT) := by
  rfl
theorem sgtPC6 : Artifact.submissionArtifact.instructionPC 6949 = 8701 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.FusedBlocks
