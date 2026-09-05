import Challenge.Ripemd160.Submission.H39Memo.PatternCorrect

#check Challenge.Ripemd160.Submission.H39Memo.PatternCorrect.trace_cases
#check Challenge.Ripemd160.Submission.H39Memo.PatternCorrect.correct
#check Challenge.Ripemd160.Submission.H39Memo.PatternCorrect.correct_at
#print axioms Challenge.Ripemd160.Submission.H39Memo.PatternTrace.prefix_next
#print axioms Challenge.Ripemd160.Submission.H39Memo.PatternTrace.dag1696
#print axioms Challenge.Ripemd160.Submission.H39Memo.PatternTrace.terminals_correct
#print axioms Challenge.Ripemd160.Submission.H39Memo.PatternCorrect.trace_cases
#print axioms Challenge.Ripemd160.Submission.H39Memo.PatternCorrect.correct
#print axioms Challenge.Ripemd160.Submission.H39Memo.PatternCorrect.correct_at

example (s : EvmSemantics.EVM.State) :
    (Challenge.Ripemd160.Submission.H39Memo.PatternTrace.fallback s).memory = s.memory := rfl

example (s : EvmSemantics.EVM.State) :
    (Challenge.Ripemd160.Submission.H39Memo.PatternTrace.fallback s).stack = [] := rfl

example (s : EvmSemantics.EVM.State) :
    (Challenge.Ripemd160.Submission.H39Memo.PatternTrace.fallback s).pc =
      EvmSemantics.UInt256.ofNat 1006 := rfl
