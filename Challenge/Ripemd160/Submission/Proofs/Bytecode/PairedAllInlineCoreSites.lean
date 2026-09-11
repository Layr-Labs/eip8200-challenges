import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreStraight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair48
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair50
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair52
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair54
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair56
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair58
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair60
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedPair62
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedHelperBooleanTrace

/-- The actual shared core, related to the unchanged eighty-round model. -/
def gasSteps_core_prefix (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 735, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho}
      {s with pc := UInt256.ofNat 4597, stack := coreStack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] (PairedAllInlineCoreTrace.corePrefixChain.eval s.memory f) rho} := by
  let f0 := f
  let f1 := SharedCoreStraight.group0Physical.eval s.memory f0
  have g0 := SharedCoreStraight.group0Gas.run s f0 rho hstack hrun hactive hcode hfork hnp
  let f2 := SharedCoreStraight.inline0Physical.eval s.memory f1
  have g1 := SharedCoreStraight.inline0Gas.run s f1 rho hstack hrun hactive hcode hfork hnp
  let f3 := SharedCoreStraight.inline1Physical.eval s.memory f2
  have g2 := SharedCoreStraight.inline1Gas.run s f2 rho hstack hrun hactive hcode hfork hnp
  let f4 := SharedCoreStraight.inline2Physical.eval s.memory f3
  have g3 := SharedCoreStraight.inline2Gas.run s f3 rho hstack hrun hactive hcode hfork hnp
  let f5 := SharedCoreStraight.inline3Physical.eval s.memory f4
  have g4 := SharedCoreStraight.inline3Gas.run s f4 rho hstack hrun hactive hcode hfork hnp
  let f6 := SharedCoreStraight.inline4Physical.eval s.memory f5
  have g5 := SharedCoreStraight.inline4Gas.run s f5 rho hstack hrun hactive hcode hfork hnp
  let f7 := SharedCoreStraight.inline5Physical.eval s.memory f6
  have g6 := SharedCoreStraight.inline5Gas.run s f6 rho hstack hrun hactive hcode hfork hnp
  let f8 := SharedCoreStraight.inline6Physical.eval s.memory f7
  have g7 := SharedCoreStraight.inline6Gas.run s f7 rho hstack hrun hactive hcode hfork hnp
  let f9 := SharedCoreStraight.inline7Physical.eval s.memory f8
  have g8 := SharedCoreStraight.inline7Gas.run s f8 rho hstack hrun hactive hcode hfork hnp
  let f10 := SharedCoreStraight.inline8Physical.eval s.memory f9
  have g9 := SharedCoreStraight.inline8Gas.run s f9 rho hstack hrun hactive hcode hfork hnp
  let f11 := SharedCoreStraight.inline9Physical.eval s.memory f10
  have g10 := SharedCoreStraight.inline9Gas.run s f10 rho hstack hrun hactive hcode hfork hnp
  let f12 := SharedCoreStraight.inline10Physical.eval s.memory f11
  have g11 := SharedCoreStraight.inline10Gas.run s f11 rho hstack hrun hactive hcode hfork hnp
  let f13 := SharedCoreStraight.inline11Physical.eval s.memory f12
  have g12 := SharedCoreStraight.inline11Gas.run s f12 rho hstack hrun hactive hcode hfork hnp
  let f14 := SharedCoreStraight.inline12Physical.eval s.memory f13
  have g13 := SharedCoreStraight.inline12Gas.run s f13 rho hstack hrun hactive hcode hfork hnp
  let f15 := SharedCoreStraight.inline13Physical.eval s.memory f14
  have g14 := SharedCoreStraight.inline13Gas.run s f14 rho hstack hrun hactive hcode hfork hnp
  let f16 := SharedCoreStraight.inline14Physical.eval s.memory f15
  have g15 := SharedCoreStraight.inline14Gas.run s f15 rho hstack hrun hactive hcode hfork hnp
  let f17 := SharedCoreStraight.inline15Physical.eval s.memory f16
  have g16 := SharedCoreStraight.inline15Gas.run s f16 rho hstack hrun hactive hcode hfork hnp
  let f18 := SharedCoreStraight.group16Physical.eval s.memory f17
  have g17 := SharedCoreStraight.group16Gas.run s f17 rho hstack hrun hactive hcode hfork hnp
  let f19 := SharedCoreStraight.inline16Physical.eval s.memory f18
  have g18 := SharedCoreStraight.inline16Gas.run s f18 rho hstack hrun hactive hcode hfork hnp
  let f20 := SharedCoreStraight.inline17Physical.eval s.memory f19
  have g19 := SharedCoreStraight.inline17Gas.run s f19 rho hstack hrun hactive hcode hfork hnp
  let f21 := SharedCoreStraight.inline18Physical.eval s.memory f20
  have g20 := SharedCoreStraight.inline18Gas.run s f20 rho hstack hrun hactive hcode hfork hnp
  let f22 := SharedCoreStraight.inline19Physical.eval s.memory f21
  have g21 := SharedCoreStraight.inline19Gas.run s f21 rho hstack hrun hactive hcode hfork hnp
  let f23 := SharedCoreStraight.inline20Physical.eval s.memory f22
  have g22 := SharedCoreStraight.inline20Gas.run s f22 rho hstack hrun hactive hcode hfork hnp
  let f24 := SharedCoreStraight.inline21Physical.eval s.memory f23
  have g23 := SharedCoreStraight.inline21Gas.run s f23 rho hstack hrun hactive hcode hfork hnp
  let f25 := SharedCoreStraight.inline22Physical.eval s.memory f24
  have g24 := SharedCoreStraight.inline22Gas.run s f24 rho hstack hrun hactive hcode hfork hnp
  let f26 := SharedCoreStraight.inline23Physical.eval s.memory f25
  have g25 := SharedCoreStraight.inline23Gas.run s f25 rho hstack hrun hactive hcode hfork hnp
  let f27 := SharedCoreStraight.inline24Physical.eval s.memory f26
  have g26 := SharedCoreStraight.inline24Gas.run s f26 rho hstack hrun hactive hcode hfork hnp
  let f28 := SharedCoreStraight.inline25Physical.eval s.memory f27
  have g27 := SharedCoreStraight.inline25Gas.run s f27 rho hstack hrun hactive hcode hfork hnp
  let f29 := SharedCoreStraight.inline26Physical.eval s.memory f28
  have g28 := SharedCoreStraight.inline26Gas.run s f28 rho hstack hrun hactive hcode hfork hnp
  let f30 := SharedCoreStraight.inline27Physical.eval s.memory f29
  have g29 := SharedCoreStraight.inline27Gas.run s f29 rho hstack hrun hactive hcode hfork hnp
  let f31 := SharedCoreStraight.inline28Physical.eval s.memory f30
  have g30 := SharedCoreStraight.inline28Gas.run s f30 rho hstack hrun hactive hcode hfork hnp
  let f32 := SharedCoreStraight.inline29Physical.eval s.memory f31
  have g31 := SharedCoreStraight.inline29Gas.run s f31 rho hstack hrun hactive hcode hfork hnp
  let f33 := SharedCoreStraight.inline30Physical.eval s.memory f32
  have g32 := SharedCoreStraight.inline30Gas.run s f32 rho hstack hrun hactive hcode hfork hnp
  let f34 := SharedCoreStraight.inline31Physical.eval s.memory f33
  have g33 := SharedCoreStraight.inline31Gas.run s f33 rho hstack hrun hactive hcode hfork hnp
  let f35 := SharedCoreStraight.group32Physical.eval s.memory f34
  have g34 := SharedCoreStraight.group32Gas.run s f34 rho hstack hrun hactive hcode hfork hnp
  let f36 := SharedCoreStraight.inline32Physical.eval s.memory f35
  have g35 := SharedCoreStraight.inline32Gas.run s f35 rho hstack hrun hactive hcode hfork hnp
  let f37 := SharedCoreStraight.inline33Physical.eval s.memory f36
  have g36 := SharedCoreStraight.inline33Gas.run s f36 rho hstack hrun hactive hcode hfork hnp
  let f38 := SharedCoreStraight.inline34Physical.eval s.memory f37
  have g37 := SharedCoreStraight.inline34Gas.run s f37 rho hstack hrun hactive hcode hfork hnp
  let f39 := SharedCoreStraight.inline35Physical.eval s.memory f38
  have g38 := SharedCoreStraight.inline35Gas.run s f38 rho hstack hrun hactive hcode hfork hnp
  let f40 := SharedCoreStraight.inline36Physical.eval s.memory f39
  have g39 := SharedCoreStraight.inline36Gas.run s f39 rho hstack hrun hactive hcode hfork hnp
  let f41 := SharedCoreStraight.inline37Physical.eval s.memory f40
  have g40 := SharedCoreStraight.inline37Gas.run s f40 rho hstack hrun hactive hcode hfork hnp
  let f42 := SharedCoreStraight.inline38Physical.eval s.memory f41
  have g41 := SharedCoreStraight.inline38Gas.run s f41 rho hstack hrun hactive hcode hfork hnp
  let f43 := SharedCoreStraight.inline39Physical.eval s.memory f42
  have g42 := SharedCoreStraight.inline39Gas.run s f42 rho hstack hrun hactive hcode hfork hnp
  let f44 := SharedCoreStraight.inline40Physical.eval s.memory f43
  have g43 := SharedCoreStraight.inline40Gas.run s f43 rho hstack hrun hactive hcode hfork hnp
  let f45 := SharedCoreStraight.inline41Physical.eval s.memory f44
  have g44 := SharedCoreStraight.inline41Gas.run s f44 rho hstack hrun hactive hcode hfork hnp
  let f46 := SharedCoreStraight.inline42Physical.eval s.memory f45
  have g45 := SharedCoreStraight.inline42Gas.run s f45 rho hstack hrun hactive hcode hfork hnp
  let f47 := SharedCoreStraight.inline43Physical.eval s.memory f46
  have g46 := SharedCoreStraight.inline43Gas.run s f46 rho hstack hrun hactive hcode hfork hnp
  let f48 := SharedCoreStraight.inline44Physical.eval s.memory f47
  have g47 := SharedCoreStraight.inline44Gas.run s f47 rho hstack hrun hactive hcode hfork hnp
  let f49 := SharedCoreStraight.inline45Physical.eval s.memory f48
  have g48 := SharedCoreStraight.inline45Gas.run s f48 rho hstack hrun hactive hcode hfork hnp
  let f50 := SharedCoreStraight.inline46Physical.eval s.memory f49
  have g49 := SharedCoreStraight.inline46Gas.run s f49 rho hstack hrun hactive hcode hfork hnp
  let f51 := SharedCoreStraight.inline47Physical.eval s.memory f50
  have g50 := SharedCoreStraight.inline47Gas.run s f50 rho hstack hrun hactive hcode hfork hnp
  let f52 := SharedCoreStraight.group48Physical.eval s.memory f51
  have g51 := SharedCoreStraight.group48Gas.run s f51 rho hstack hrun hactive hcode hfork hnp
  let f53 := SharedPair48.pairEval s.memory f52
  have g52 := SharedPair48.gasSteps_pair s f52 rho hstack hrun hactive hcode hfork hnp
  let f54 := SharedPair50.pairEval s.memory f53
  have g53 := SharedPair50.gasSteps_pair s f53 rho hstack hrun hactive hcode hfork hnp
  let f55 := SharedPair52.pairEval s.memory f54
  have g54 := SharedPair52.gasSteps_pair s f54 rho hstack hrun hactive hcode hfork hnp
  let f56 := SharedPair54.pairEval s.memory f55
  have g55 := SharedPair54.gasSteps_pair s f55 rho hstack hrun hactive hcode hfork hnp
  let f57 := SharedPair56.pairEval s.memory f56
  have g56 := SharedPair56.gasSteps_pair s f56 rho hstack hrun hactive hcode hfork hnp
  let f58 := SharedPair58.pairEval s.memory f57
  have g57 := SharedPair58.gasSteps_pair s f57 rho hstack hrun hactive hcode hfork hnp
  let f59 := SharedPair60.pairEval s.memory f58
  have g58 := SharedPair60.gasSteps_pair s f58 rho hstack hrun hactive hcode hfork hnp
  let f60 := SharedPair62.pairEval s.memory f59
  have g59 := SharedPair62.gasSteps_pair s f59 rho hstack hrun hactive hcode hfork hnp
  let f61 := SharedCoreStraight.group64Physical.eval s.memory f60
  have g60 := SharedCoreStraight.group64Gas.run s f60 rho hstack hrun hactive hcode hfork hnp
  let f62 := SharedCoreStraight.inline64Physical.eval s.memory f61
  have g61 := SharedCoreStraight.inline64Gas.run s f61 rho hstack hrun hactive hcode hfork hnp
  let f63 := SharedCoreStraight.inline65Physical.eval s.memory f62
  have g62 := SharedCoreStraight.inline65Gas.run s f62 rho hstack hrun hactive hcode hfork hnp
  let f64 := SharedCoreStraight.inline66Physical.eval s.memory f63
  have g63 := SharedCoreStraight.inline66Gas.run s f63 rho hstack hrun hactive hcode hfork hnp
  let f65 := SharedCoreStraight.inline67Physical.eval s.memory f64
  have g64 := SharedCoreStraight.inline67Gas.run s f64 rho hstack hrun hactive hcode hfork hnp
  let f66 := SharedCoreStraight.inline68Physical.eval s.memory f65
  have g65 := SharedCoreStraight.inline68Gas.run s f65 rho hstack hrun hactive hcode hfork hnp
  let f67 := SharedCoreStraight.inline69Physical.eval s.memory f66
  have g66 := SharedCoreStraight.inline69Gas.run s f66 rho hstack hrun hactive hcode hfork hnp
  let f68 := SharedCoreStraight.inline70Physical.eval s.memory f67
  have g67 := SharedCoreStraight.inline70Gas.run s f67 rho hstack hrun hactive hcode hfork hnp
  let f69 := SharedCoreStraight.inline71Physical.eval s.memory f68
  have g68 := SharedCoreStraight.inline71Gas.run s f68 rho hstack hrun hactive hcode hfork hnp
  let f70 := SharedCoreStraight.inline72Physical.eval s.memory f69
  have g69 := SharedCoreStraight.inline72Gas.run s f69 rho hstack hrun hactive hcode hfork hnp
  let f71 := SharedCoreStraight.inline73Physical.eval s.memory f70
  have g70 := SharedCoreStraight.inline73Gas.run s f70 rho hstack hrun hactive hcode hfork hnp
  let f72 := SharedCoreStraight.inline74Physical.eval s.memory f71
  have g71 := SharedCoreStraight.inline74Gas.run s f71 rho hstack hrun hactive hcode hfork hnp
  let f73 := SharedCoreStraight.inline75Physical.eval s.memory f72
  have g72 := SharedCoreStraight.inline75Gas.run s f72 rho hstack hrun hactive hcode hfork hnp
  let f74 := SharedCoreStraight.inline76Physical.eval s.memory f73
  have g73 := SharedCoreStraight.inline76Gas.run s f73 rho hstack hrun hactive hcode hfork hnp
  let f75 := SharedCoreStraight.inline77Physical.eval s.memory f74
  have g74 := SharedCoreStraight.inline77Gas.run s f74 rho hstack hrun hactive hcode hfork hnp
  have g75 := SharedCoreStraight.inline78Gas.run s f75 rho hstack hrun hactive hcode hfork hnp
  have g := g0.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans (g9.trans (g10.trans (g11.trans (g12.trans (g13.trans (g14.trans (g15.trans (g16.trans (g17.trans (g18.trans (g19.trans (g20.trans (g21.trans (g22.trans (g23.trans (g24.trans (g25.trans (g26.trans (g27.trans (g28.trans (g29.trans (g30.trans (g31.trans (g32.trans (g33.trans (g34.trans (g35.trans (g36.trans (g37.trans (g38.trans (g39.trans (g40.trans (g41.trans (g42.trans (g43.trans (g44.trans (g45.trans (g46.trans (g47.trans (g48.trans (g49.trans (g50.trans (g51.trans (g52.trans (g53.trans (g54.trans (g55.trans (g56.trans (g57.trans (g58.trans (g59.trans (g60.trans (g61.trans (g62.trans (g63.trans (g64.trans (g65.trans (g66.trans (g67.trans (g68.trans (g69.trans (g70.trans (g71.trans (g72.trans (g73.trans (g74.trans (g75)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact g

#print axioms gasSteps_core_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
