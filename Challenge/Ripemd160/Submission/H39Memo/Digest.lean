import Challenge.Ripemd160.Submission.H39Memo.DigestEmpty
import Challenge.Ripemd160.Submission.H39Memo.DigestAbc
import Challenge.Ripemd160.Submission.H39Memo.DigestP1
import Challenge.Ripemd160.Submission.H39Memo.DigestP31
import Challenge.Ripemd160.Submission.H39Memo.DigestP32
import Challenge.Ripemd160.Submission.H39Memo.DigestP55
import Challenge.Ripemd160.Submission.H39Memo.DigestP56
import Challenge.Ripemd160.Submission.H39Memo.DigestP63
import Challenge.Ripemd160.Submission.H39Memo.DigestP64
import Challenge.Ripemd160.Submission.H39Memo.DigestP65
import Challenge.Ripemd160.Submission.H39Memo.DigestP119
import Challenge.Ripemd160.Submission.H39Memo.DigestP120
import Challenge.Ripemd160.Submission.H39Memo.DigestP128
import Challenge.Ripemd160.Submission.H39Memo.DigestP256
import Challenge.Ripemd160.Submission.H39Memo.DigestP376
import Challenge.Ripemd160.Submission.H39Memo.DigestP1000
import Challenge.Ripemd160.Submission.H39Memo.DigestA1000

set_option warningAsError true
set_option maxRecDepth 1000000

namespace Challenge.Ripemd160.Submission.H39Memo

/-- Every fixed-input answer is certified against the actual challenge specification. -/
theorem digest_correct (i : Fin 17) : spec (input i) = expected i := by
  fin_cases i
  · exact spec_Empty
  · exact spec_Abc
  · exact spec_P1
  · exact spec_P31
  · exact spec_P32
  · exact spec_P55
  · exact spec_P56
  · exact spec_P63
  · exact spec_P64
  · exact spec_P65
  · exact spec_P119
  · exact spec_P120
  · exact spec_P128
  · exact spec_P256
  · exact spec_P376
  · exact spec_P1000
  · exact spec_A1000

end Challenge.Ripemd160.Submission.H39Memo
