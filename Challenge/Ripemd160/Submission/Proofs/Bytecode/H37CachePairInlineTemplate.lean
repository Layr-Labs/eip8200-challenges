import Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePairTemplate

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairRoundTemplate PairRoundState
open QuadGapTemplate QuadGapTrace

def inlineFirstBoolean (j : Nat) : List Instr :=
  match j with
  | 0 => [d 2, d 4, op .XOR, d 5, op .XOR]
  | 1 => [d 3, d 5, op .XOR, d 3, op .AND, d 5, op .XOR]
  | 2 => [d 3, op .NOT, d 3, op .OR, d 5, op .XOR]
  | 3 => [d 2, d 4, op .XOR, d 5, op .AND, d 4, op .XOR]
  | _ => [d 4, op .NOT, d 4, op .OR, d 3, op .XOR]

def inlineSecondBoolean (j : Nat) : List Instr :=
  match j with
  | 0 => [d 3, d 3, op .XOR, d 2, op .XOR]
  | 1 => [d 2, d 2, op .XOR, d 4, op .AND, d 2, op .XOR]
  | 2 => [d 2, op .NOT, d 4, op .OR, d 2, op .XOR]
  | 3 => [d 3, d 3, op .XOR, d 2, op .AND, d 3, op .XOR]
  | _ => [d 1, op .NOT, d 3, op .OR, d 4, op .XOR]

/-- B1 control projection: pointers and shifts are materialized at their use.
The between-pair control SWAP1 is absent. Both K reads are DUP8. -/
def inlineTemplate (j : Nat) (p0 p1 : UInt256) (r0 r1 : Nat) : List Instr :=
  [push2 p0, op .MLOAD] ++ inlineFirstBoolean j ++
    [op .ADD, w 0, op .ADD] ++
    (if j = 0 then [] else [d 7, op .ADD]) ++
    [d 5, op .AND, d 6, op .MUL, push1 (UInt256.ofNat (32 - r0)), op .SHR,
     d 4, op .ADD, d 5, op .AND, w 1,
     d 6, op .MUL, push1 c22, op .SHR, push2 p1, op .MLOAD] ++
    inlineSecondBoolean j ++ [op .ADD, w 0, w 4, op .ADD] ++
    (if j = 0 then [] else [d 7, op .ADD]) ++
    [d 5, op .AND, d 6, op .MUL, push1 (UInt256.ofNat (32 - r1)), op .SHR,
     d 3, op .ADD, d 5, op .AND, w 0,
     d 6, op .MUL, push1 c22, op .SHR, w 2]

def inlineEntry (s : State) (pc : UInt256) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256) : State :=
  {s with pc := pc, stack := roundWords working ++ cache constant rho}

/-- Erase the return control from the old pair endpoint. -/
def eraseReturn (pc : UInt256) (s : State) : State :=
  {s with pc := pc, stack := s.stack.drop 1}

end Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePair

