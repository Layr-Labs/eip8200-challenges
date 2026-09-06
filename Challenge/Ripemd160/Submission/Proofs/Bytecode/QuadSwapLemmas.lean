import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true

/-! Exchange lemmas for SWAP1..SWAP12 on explicit cons lists (generated). -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas

open EvmSemantics


theorem exchange_swap1 (u w : UInt256) (rho : List UInt256) :
    (u :: w :: rho).exchange 0 1 = some (w :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [] rho

theorem exchange_swap2 (u v1 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: w :: rho).exchange 0 2 = some (w :: v1 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1] rho

theorem exchange_swap3 (u v1 v2 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: w :: rho).exchange 0 3 = some (w :: v1 :: v2 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2] rho

theorem exchange_swap4 (u v1 v2 v3 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: w :: rho).exchange 0 4 = some (w :: v1 :: v2 :: v3 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3] rho

theorem exchange_swap5 (u v1 v2 v3 v4 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: w :: rho).exchange 0 5 = some (w :: v1 :: v2 :: v3 :: v4 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4] rho

theorem exchange_swap6 (u v1 v2 v3 v4 v5 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: w :: rho).exchange 0 6 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5] rho

theorem exchange_swap7 (u v1 v2 v3 v4 v5 v6 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: w :: rho).exchange 0 7 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5, v6] rho

theorem exchange_swap8 (u v1 v2 v3 v4 v5 v6 v7 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: w :: rho).exchange 0 8 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5, v6, v7] rho

theorem exchange_swap9 (u v1 v2 v3 v4 v5 v6 v7 v8 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: w :: rho).exchange 0 9 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5, v6, v7, v8] rho

theorem exchange_swap10 (u v1 v2 v3 v4 v5 v6 v7 v8 v9 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: w :: rho).exchange 0 10 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5, v6, v7, v8, v9] rho

theorem exchange_swap11 (u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: w :: rho).exchange 0 11 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] rho

theorem exchange_swap12 (u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 w : UInt256) (rho : List UInt256) :
    (u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: w :: rho).exchange 0 12 = some (w :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] rho

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas
