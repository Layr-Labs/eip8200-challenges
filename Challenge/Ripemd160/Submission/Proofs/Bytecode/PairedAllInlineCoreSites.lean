import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreStraight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound4
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound5
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound6
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound7
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound16
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound17
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound21
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound23
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound27
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound28
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound35
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound40
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound41
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound43
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound46
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound55
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound57
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound58
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound61
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound62
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound63
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound66
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound68
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound70
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound74
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedRound77
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace PairedAllInlineCoreTrace CachedCoreCommon
def gasSteps_core_prefix (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 888, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f (cache s.memory ++ rho)}
      {s with pc := UInt256.ofNat 4816, stack := coreStack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] (PairedAllInlineCoreTrace.corePrefixChain.eval s.memory f) (cache s.memory ++ rho)} := by
  have hs : (cache s.memory ++ rho).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  let f0 := f
  let f1 := PairedAllInlineCoreTrace.group0Block.eval s.memory f0
  have g0 := CachedCoreStraight.group0Gas.run s f0 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f2 := PairedAllInlineCoreTrace.inline0Block.eval s.memory f1
  have g1 := CachedCoreStraight.inline0Gas.run s f1 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f3 := PairedAllInlineCoreTrace.inline1Block.eval s.memory f2
  have g2 := CachedCoreStraight.inline1Gas.run s f2 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f4 := PairedAllInlineCoreTrace.inline2Block.eval s.memory f3
  have g3 := CachedRound2.gasSteps s f3 rho hstack hrun hactive hcode hfork hnp
  let f5 := PairedAllInlineCoreTrace.inline3Block.eval s.memory f4
  have g4 := CachedRound3.gasSteps s f4 rho hstack hrun hactive hcode hfork hnp
  let f6 := PairedAllInlineCoreTrace.inline4Block.eval s.memory f5
  have g5 := CachedRound4.gasSteps s f5 rho hstack hrun hactive hcode hfork hnp
  let f7 := PairedAllInlineCoreTrace.inline5Block.eval s.memory f6
  have g6 := CachedRound5.gasSteps s f6 rho hstack hrun hactive hcode hfork hnp
  let f8 := PairedAllInlineCoreTrace.inline6Block.eval s.memory f7
  have g7 := CachedRound6.gasSteps s f7 rho hstack hrun hactive hcode hfork hnp
  let f9 := PairedAllInlineCoreTrace.inline7Block.eval s.memory f8
  have g8 := CachedRound7.gasSteps s f8 rho hstack hrun hactive hcode hfork hnp
  let f10 := PairedAllInlineCoreTrace.inline8Block.eval s.memory f9
  have g9 := CachedCoreStraight.inline8Gas.run s f9 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f11 := PairedAllInlineCoreTrace.inline9Block.eval s.memory f10
  have g10 := CachedCoreStraight.inline9Gas.run s f10 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f12 := PairedAllInlineCoreTrace.inline10Block.eval s.memory f11
  have g11 := CachedCoreStraight.inline10Gas.run s f11 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f13 := PairedAllInlineCoreTrace.inline11Block.eval s.memory f12
  have g12 := CachedCoreStraight.inline11Gas.run s f12 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f14 := PairedAllInlineCoreTrace.inline12Block.eval s.memory f13
  have g13 := CachedCoreStraight.inline12Gas.run s f13 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f15 := PairedAllInlineCoreTrace.inline13Block.eval s.memory f14
  have g14 := CachedCoreStraight.inline13Gas.run s f14 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f16 := PairedAllInlineCoreTrace.inline14Block.eval s.memory f15
  have g15 := CachedCoreStraight.inline14Gas.run s f15 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f17 := PairedAllInlineCoreTrace.inline15Block.eval s.memory f16
  have g16 := CachedCoreStraight.inline15Gas.run s f16 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f18 := PairedAllInlineCoreTrace.group16Block.eval s.memory f17
  have g17 := CachedCoreStraight.group16Gas.run s f17 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f19 := PairedAllInlineCoreTrace.inline16Block.eval s.memory f18
  have g18 := CachedRound16.gasSteps s f18 rho hstack hrun hactive hcode hfork hnp
  let f20 := PairedAllInlineCoreTrace.inline17Block.eval s.memory f19
  have g19 := CachedRound17.gasSteps s f19 rho hstack hrun hactive hcode hfork hnp
  let f21 := PairedAllInlineCoreTrace.inline18Block.eval s.memory f20
  have g20 := CachedCoreStraight.inline18Gas.run s f20 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f22 := PairedAllInlineCoreTrace.inline19Block.eval s.memory f21
  have g21 := CachedCoreStraight.inline19Gas.run s f21 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f23 := PairedAllInlineCoreTrace.inline20Block.eval s.memory f22
  have g22 := CachedCoreStraight.inline20Gas.run s f22 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f24 := PairedAllInlineCoreTrace.inline21Block.eval s.memory f23
  have g23 := CachedRound21.gasSteps s f23 rho hstack hrun hactive hcode hfork hnp
  let f25 := PairedAllInlineCoreTrace.inline22Block.eval s.memory f24
  have g24 := CachedCoreStraight.inline22Gas.run s f24 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f26 := PairedAllInlineCoreTrace.inline23Block.eval s.memory f25
  have g25 := CachedRound23.gasSteps s f25 rho hstack hrun hactive hcode hfork hnp
  let f27 := PairedAllInlineCoreTrace.inline24Block.eval s.memory f26
  have g26 := CachedCoreStraight.inline24Gas.run s f26 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f28 := PairedAllInlineCoreTrace.inline25Block.eval s.memory f27
  have g27 := CachedCoreStraight.inline25Gas.run s f27 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f29 := PairedAllInlineCoreTrace.inline26Block.eval s.memory f28
  have g28 := CachedCoreStraight.inline26Gas.run s f28 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f30 := PairedAllInlineCoreTrace.inline27Block.eval s.memory f29
  have g29 := CachedRound27.gasSteps s f29 rho hstack hrun hactive hcode hfork hnp
  let f31 := PairedAllInlineCoreTrace.inline28Block.eval s.memory f30
  have g30 := CachedRound28.gasSteps s f30 rho hstack hrun hactive hcode hfork hnp
  let f32 := PairedAllInlineCoreTrace.inline29Block.eval s.memory f31
  have g31 := CachedCoreStraight.inline29Gas.run s f31 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f33 := PairedAllInlineCoreTrace.inline30Block.eval s.memory f32
  have g32 := CachedCoreStraight.inline30Gas.run s f32 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f34 := PairedAllInlineCoreTrace.inline31Block.eval s.memory f33
  have g33 := CachedCoreStraight.inline31Gas.run s f33 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f35 := PairedAllInlineCoreTrace.group32Block.eval s.memory f34
  have g34 := CachedCoreStraight.group32Gas.run s f34 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f36 := PairedAllInlineCoreTrace.inline32Block.eval s.memory f35
  have g35 := CachedRound32.gasSteps s f35 rho hstack hrun hactive hcode hfork hnp
  let f37 := PairedAllInlineCoreTrace.inline33Block.eval s.memory f36
  have g36 := CachedCoreStraight.inline33Gas.run s f36 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f38 := PairedAllInlineCoreTrace.inline34Block.eval s.memory f37
  have g37 := CachedCoreStraight.inline34Gas.run s f37 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f39 := PairedAllInlineCoreTrace.inline35Block.eval s.memory f38
  have g38 := CachedRound35.gasSteps s f38 rho hstack hrun hactive hcode hfork hnp
  let f40 := PairedAllInlineCoreTrace.inline36Block.eval s.memory f39
  have g39 := CachedCoreStraight.inline36Gas.run s f39 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f41 := PairedAllInlineCoreTrace.inline37Block.eval s.memory f40
  have g40 := CachedCoreStraight.inline37Gas.run s f40 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f42 := PairedAllInlineCoreTrace.inline38Block.eval s.memory f41
  have g41 := CachedCoreStraight.inline38Gas.run s f41 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f43 := PairedAllInlineCoreTrace.inline39Block.eval s.memory f42
  have g42 := CachedCoreStraight.inline39Gas.run s f42 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f44 := PairedAllInlineCoreTrace.inline40Block.eval s.memory f43
  have g43 := CachedRound40.gasSteps s f43 rho hstack hrun hactive hcode hfork hnp
  let f45 := PairedAllInlineCoreTrace.inline41Block.eval s.memory f44
  have g44 := CachedRound41.gasSteps s f44 rho hstack hrun hactive hcode hfork hnp
  let f46 := PairedAllInlineCoreTrace.inline42Block.eval s.memory f45
  have g45 := CachedCoreStraight.inline42Gas.run s f45 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f47 := PairedAllInlineCoreTrace.inline43Block.eval s.memory f46
  have g46 := CachedRound43.gasSteps s f46 rho hstack hrun hactive hcode hfork hnp
  let f48 := PairedAllInlineCoreTrace.inline44Block.eval s.memory f47
  have g47 := CachedCoreStraight.inline44Gas.run s f47 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f49 := PairedAllInlineCoreTrace.inline45Block.eval s.memory f48
  have g48 := CachedCoreStraight.inline45Gas.run s f48 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f50 := PairedAllInlineCoreTrace.inline46Block.eval s.memory f49
  have g49 := CachedRound46.gasSteps s f49 rho hstack hrun hactive hcode hfork hnp
  let f51 := PairedAllInlineCoreTrace.inline47Block.eval s.memory f50
  have g50 := CachedCoreStraight.inline47Gas.run s f50 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f52 := PairedAllInlineCoreTrace.group48Block.eval s.memory f51
  have g51 := CachedCoreStraight.group48Gas.run s f51 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f53 := PairedAllInlineCoreTrace.inline48Block.eval s.memory f52
  have g52 := CachedCoreStraight.inline48Gas.run s f52 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f54 := PairedAllInlineCoreTrace.inline49Block.eval s.memory f53
  have g53 := CachedCoreStraight.inline49Gas.run s f53 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f55 := PairedAllInlineCoreTrace.inline50Block.eval s.memory f54
  have g54 := CachedCoreStraight.inline50Gas.run s f54 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f56 := PairedAllInlineCoreTrace.inline51Block.eval s.memory f55
  have g55 := CachedCoreStraight.inline51Gas.run s f55 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f57 := PairedAllInlineCoreTrace.inline52Block.eval s.memory f56
  have g56 := CachedCoreStraight.inline52Gas.run s f56 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f58 := PairedAllInlineCoreTrace.inline53Block.eval s.memory f57
  have g57 := CachedCoreStraight.inline53Gas.run s f57 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f59 := PairedAllInlineCoreTrace.inline54Block.eval s.memory f58
  have g58 := CachedCoreStraight.inline54Gas.run s f58 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f60 := PairedAllInlineCoreTrace.inline55Block.eval s.memory f59
  have g59 := CachedRound55.gasSteps s f59 rho hstack hrun hactive hcode hfork hnp
  let f61 := PairedAllInlineCoreTrace.inline56Block.eval s.memory f60
  have g60 := CachedCoreStraight.inline56Gas.run s f60 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f62 := PairedAllInlineCoreTrace.inline57Block.eval s.memory f61
  have g61 := CachedRound57.gasSteps s f61 rho hstack hrun hactive hcode hfork hnp
  let f63 := PairedAllInlineCoreTrace.inline58Block.eval s.memory f62
  have g62 := CachedRound58.gasSteps s f62 rho hstack hrun hactive hcode hfork hnp
  let f64 := PairedAllInlineCoreTrace.inline59Block.eval s.memory f63
  have g63 := CachedCoreStraight.inline59Gas.run s f63 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f65 := PairedAllInlineCoreTrace.inline60Block.eval s.memory f64
  have g64 := CachedCoreStraight.inline60Gas.run s f64 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f66 := PairedAllInlineCoreTrace.inline61Block.eval s.memory f65
  have g65 := CachedRound61.gasSteps s f65 rho hstack hrun hactive hcode hfork hnp
  let f67 := PairedAllInlineCoreTrace.inline62Block.eval s.memory f66
  have g66 := CachedRound62.gasSteps s f66 rho hstack hrun hactive hcode hfork hnp
  let f68 := PairedAllInlineCoreTrace.inline63Block.eval s.memory f67
  have g67 := CachedRound63.gasSteps s f67 rho hstack hrun hactive hcode hfork hnp
  let f69 := PairedAllInlineCoreTrace.group64Block.eval s.memory f68
  have g68 := CachedCoreStraight.group64Gas.run s f68 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f70 := PairedAllInlineCoreTrace.inline64Block.eval s.memory f69
  have g69 := CachedRound64.gasSteps s f69 rho hstack hrun hactive hcode hfork hnp
  let f71 := PairedAllInlineCoreTrace.inline65Block.eval s.memory f70
  have g70 := CachedCoreStraight.inline65Gas.run s f70 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f72 := PairedAllInlineCoreTrace.inline66Block.eval s.memory f71
  have g71 := CachedRound66.gasSteps s f71 rho hstack hrun hactive hcode hfork hnp
  let f73 := PairedAllInlineCoreTrace.inline67Block.eval s.memory f72
  have g72 := CachedCoreStraight.inline67Gas.run s f72 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f74 := PairedAllInlineCoreTrace.inline68Block.eval s.memory f73
  have g73 := CachedRound68.gasSteps s f73 rho hstack hrun hactive hcode hfork hnp
  let f75 := PairedAllInlineCoreTrace.inline69Block.eval s.memory f74
  have g74 := CachedCoreStraight.inline69Gas.run s f74 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f76 := PairedAllInlineCoreTrace.inline70Block.eval s.memory f75
  have g75 := CachedRound70.gasSteps s f75 rho hstack hrun hactive hcode hfork hnp
  let f77 := PairedAllInlineCoreTrace.inline71Block.eval s.memory f76
  have g76 := CachedCoreStraight.inline71Gas.run s f76 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f78 := PairedAllInlineCoreTrace.inline72Block.eval s.memory f77
  have g77 := CachedCoreStraight.inline72Gas.run s f77 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f79 := PairedAllInlineCoreTrace.inline73Block.eval s.memory f78
  have g78 := CachedCoreStraight.inline73Gas.run s f78 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f80 := PairedAllInlineCoreTrace.inline74Block.eval s.memory f79
  have g79 := CachedRound74.gasSteps s f79 rho hstack hrun hactive hcode hfork hnp
  let f81 := PairedAllInlineCoreTrace.inline75Block.eval s.memory f80
  have g80 := CachedCoreStraight.inline75Gas.run s f80 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f82 := PairedAllInlineCoreTrace.inline76Block.eval s.memory f81
  have g81 := CachedCoreStraight.inline76Gas.run s f81 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  let f83 := PairedAllInlineCoreTrace.inline77Block.eval s.memory f82
  have g82 := CachedRound77.gasSteps s f82 rho hstack hrun hactive hcode hfork hnp
  let f84 := PairedAllInlineCoreTrace.inline78Block.eval s.memory f83
  have g83 := CachedCoreStraight.inline78Gas.run s f83 (cache s.memory ++ rho) hs hrun hactive hcode hfork hnp
  have g := g0.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans (g9.trans (g10.trans (g11.trans (g12.trans (g13.trans (g14.trans (g15.trans (g16.trans (g17.trans (g18.trans (g19.trans (g20.trans (g21.trans (g22.trans (g23.trans (g24.trans (g25.trans (g26.trans (g27.trans (g28.trans (g29.trans (g30.trans (g31.trans (g32.trans (g33.trans (g34.trans (g35.trans (g36.trans (g37.trans (g38.trans (g39.trans (g40.trans (g41.trans (g42.trans (g43.trans (g44.trans (g45.trans (g46.trans (g47.trans (g48.trans (g49.trans (g50.trans (g51.trans (g52.trans (g53.trans (g54.trans (g55.trans (g56.trans (g57.trans (g58.trans (g59.trans (g60.trans (g61.trans (g62.trans (g63.trans (g64.trans (g65.trans (g66.trans (g67.trans (g68.trans (g69.trans (g70.trans (g71.trans (g72.trans (g73.trans (g74.trans (g75.trans (g76.trans (g77.trans (g78.trans (g79.trans (g80.trans (g81.trans (g82.trans (g83)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact g
#print axioms gasSteps_core_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
