import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Prefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Round

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Semantics
open EvmSemantics PairedLaneUInt256Bridge PairedLaneCore
open PairedHelperBooleanTrace PairedSynthCoreTrace Strip78Prefix Strip78Round

theorem resultMemory_prefix_strip (memory : ByteArray) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hready : NormalizedScheduleReady memory words) :
    PairedTailTrace.resultMemory memory
      (TerminalRound.modifiedFrame memory (dirtyFrame memory
        (corePrefix77Chain.eval memory ⟨PairedLaneWordRound.packCrypto left right, 0⟩))) =
      PairedTailTrace.resultMemory memory
        (TerminalRound.modifiedFrame memory
          (PairedAllInlineCoreTrace.corePrefixChain.eval memory
            ⟨PairedLaneWordRound.packCrypto left right, 0⟩).frame) := by
  rw [← prefix78_eq]
  rw [corePrefix77Chain_eval]
  rw [hoistedAlgorithmFold_crypto memory words 78 (by decide) left right
    (fun i hi => algorithmMessage_of_normalized memory words hready i (by omega))]
  apply resultMemory_strip_eq
  · exact normalize_pack _ _
  · exact normalize_pack _ _
  · exact normalize_pack _ _
  · change normalize (bits (physicalKey 4)) = bits (physicalKey 4)
    decide
  · change normalize (bits (algorithmMessage memory 79)) = bits (algorithmMessage memory 79)
    rw [algorithmMessage_of_normalized memory words hready 79 (by decide)]
    exact normalize_pack _ _

#print axioms resultMemory_prefix_strip
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Semantics
