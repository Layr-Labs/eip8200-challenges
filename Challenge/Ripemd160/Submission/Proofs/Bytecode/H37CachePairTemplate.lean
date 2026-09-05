import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairRoundTemplate PairRoundState
open QuadGapTemplate QuadGapTrace

/-- Shared entry: nine controls, five working words, then M, F, K and rho. -/
def firstTemplate (j : Nat) : List Instr :=
  [op .JUMPDEST, op .MLOAD] ++ firstBoolean j ++
    [op .ADD, w 0, w 8, op .ADD] ++
    (if j = 0 then [] else [d 15, op .ADD]) ++
    [d 13, op .AND, d 14, op .MUL, w 0, op .SHR,
     d 11, op .ADD, d 12, op .AND, w 8,
     d 13, op .MUL, push1 c22, op .SHR, w 0, op .MLOAD] ++
    secondBoolean j ++ [op .ADD, w 0, w 10, op .ADD] ++
    (if j = 0 then [] else [d 13, op .ADD]) ++
    [d 11, op .AND, d 12, op .MUL, w 0, op .SHR,
     d 8, op .ADD, d 10, op .AND, w 5,
     d 11, op .MUL, push1 c22, op .SHR, w 7, w 4]

/-- Second pair: the four future controls have become current controls. -/
def secondTemplate (j : Nat) : List Instr :=
  [op .MLOAD] ++ pairFirstBooleanOps j ++
    [op .ADD, swap1, pairSwap5, op .ADD] ++
    (if j = 0 then [] else [d 11, op .ADD]) ++
    [d 9, op .AND, d 10, op .MUL, swap1, op .SHR,
     pairDup8, op .ADD, d 8, op .AND, pairSwap5,
     d 9, op .MUL, push1 c22, op .SHR, swap1, op .MLOAD] ++
    pairSecondBooleanOps j ++ [op .ADD, swap1, pairSwap7, op .ADD] ++
    (if j = 0 then [] else [d 9, op .ADD]) ++
    [d 7, op .AND, d 8, op .MUL, swap1, op .SHR,
     dup5, op .ADD, d 6, op .AND, swap2,
     d 7, op .MUL, push1 c22, op .SHR, swap4, swap1]

def cache (constant : UInt256) (rho : List UInt256) : List UInt256 :=
  mask :: factor :: constant :: rho

end Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePair

