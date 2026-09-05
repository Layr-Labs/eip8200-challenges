import Challenge.Ripemd160.Submission.H39Memo.Bytecode

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Reference

abbrev referenceBytecode : ByteArray :=
  Challenge.Ripemd160.Submission.H39Memo.h39Bytecode

theorem referenceBytecode_size_bound : referenceBytecode.size < 2 ^ 256 := by
  rw [referenceBytecode, Challenge.Ripemd160.Submission.H39Memo.h39Bytecode_size]
  decide

end Challenge.Ripemd160.Submission.H39Reference
