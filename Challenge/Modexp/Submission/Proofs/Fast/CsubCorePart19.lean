import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart18

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def csTailState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2192
           stack := [UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     UInt256.ofNat (ptrAt (32 * n - 32) j),
                     UInt256.ofNat (ptrAt (7136 + 32 * n) j),
                     (csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

end Challenge.Modexp.Submission.Proofs.Fast.Csub
