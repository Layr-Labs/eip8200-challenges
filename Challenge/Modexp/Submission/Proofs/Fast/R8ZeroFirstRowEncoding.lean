import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
open EvmSemantics YulEvmCompiler

/-- Exact frozen U byte range [5090, 5336), checked using the compiler IR encoder. -/
def frozenBytes : List UInt8 := [91, 128, 81, 128, 128, 159, 80, 1, 134, 143, 128, 9, 143, 128, 2, 128, 130, 16, 129, 146, 3, 3, 144, 135, 82, 97, 13, 254, 149, 80, 97, 10, 0, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 9, 0, 82, 97, 9, 224, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 8, 224, 82, 97, 9, 192, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 8, 192, 82, 97, 9, 160, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 8, 160, 82, 97, 9, 128, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 8, 128, 82, 97, 9, 96, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 8, 96, 82, 97, 9, 64, 81, 136, 131, 130, 2, 145, 132, 9, 128, 130, 17, 3, 129, 131, 1, 128, 147, 17, 3, 3, 144, 97, 8, 64, 82, 97, 8, 32, 82, 80, 95, 136, 139, 81, 2, 135, 128, 130, 141, 9, 141, 81, 8, 137, 86]

theorem encoded_frozen : assembleBytes (program (UInt256.ofNat 3586)) = frozenBytes := by decide

theorem program_length : (program (UInt256.ofNat 3586)).length = 213 := by decide

theorem encoded_length : (assembleBytes (program (UInt256.ofNat 3586))).length = 246 := by decide

#print axioms encoded_frozen
end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
