import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
structure Input where
  v0 : UInt256 := UInt256.ofNat 0
  v1 : UInt256 := UInt256.ofNat 0
  v2 : UInt256 := UInt256.ofNat 0
  v3 : UInt256 := UInt256.ofNat 0
  v4 : UInt256 := UInt256.ofNat 0
  v5 : UInt256 := UInt256.ofNat 0
  v6 : UInt256 := UInt256.ofNat 0
  v7 : UInt256 := UInt256.ofNat 0
  v8 : UInt256 := UInt256.ofNat 0
  v9 : UInt256 := UInt256.ofNat 0
  v10 : UInt256 := UInt256.ofNat 0
  v11 : UInt256 := UInt256.ofNat 0
  v12 : UInt256 := UInt256.ofNat 0
  v13 : UInt256 := UInt256.ofNat 0
  v14 : UInt256 := UInt256.ofNat 0
  v15 : UInt256 := UInt256.ofNat 0
  v16 : UInt256 := UInt256.ofNat 0
  v17 : UInt256 := UInt256.ofNat 0
  v18 : UInt256 := UInt256.ofNat 0
  v19 : UInt256 := UInt256.ofNat 0
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRaw
