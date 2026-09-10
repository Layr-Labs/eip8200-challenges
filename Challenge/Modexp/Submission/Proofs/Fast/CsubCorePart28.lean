import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart27

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

theorem lowValue_succ (memory : ByteArray) (ptr n j : Nat) :
    lowValue memory ptr n (j + 1) =
      lowValue memory ptr n j +
        (MachineState.readWord memory (ptr + 32 * (n - 1 - j))).toNat *
          Limbs.radix ^ j := by
  simp only [lowValue, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, Nat.ofDigits_append, List.length_map, List.length_range,
    Nat.ofDigits_singleton]
  ring

end Challenge.Modexp.Submission.Proofs.Fast.Csub
