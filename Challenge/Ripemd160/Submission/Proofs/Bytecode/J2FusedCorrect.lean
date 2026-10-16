import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedLoop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeFallback
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Challenge.Ripemd160
open J2Moves
open Challenge.Ripemd160

/-- Exact byte equality transfers the already-proved generic recognition criterion. -/
theorem ordinary_zero (input : ByteArray) (h256 : input.size = 256)
    (hz : J2FusedAccumulator.resultAcc256 input = 0) :
    J2Accumulator.resultAcc input input.size = 0 := by
  apply (J2Accumulator.resultAcc_zero_iff input input.size
    (by rw [h256]; unfold RecognitionAccumulator.Allowed; omega) rfl).mpr
  simpa only [h256] using (J2FusedAccumulator.resultAcc256_zero_iff input h256).mp hz

/-- Direct RETURN has its own PC but returns exactly the prepared digest. -/
def output (input : ByteArray) (rho : List UInt256) : State :=
  RecognitionSelectorRaw.returned (EarlySerializeReturn.prepared input rho)
    (UInt256.ofNat (fusedReturnPC+1)) rho

@[simp] theorem output_halt (input : ByteArray) (rho : List UInt256) :
    (output input rho).halt = .Returned := rfl

@[simp] theorem output_callStack (input : ByteArray) (rho : List UInt256) :
    (output input rho).callStack = [] := rfl

theorem output_spec (input : ByteArray) (rho : List UInt256)
    (h256 : input.size = 256) (hz : J2FusedAccumulator.resultAcc256 input = 0) :
    (output input rho).hReturn = spec input := by
  change (EarlySerializeReturn.output input rho).hReturn = spec input
  exact EarlySerializeReturn.output_spec input rho
    (by rw [h256]; unfold RecognitionAccumulator.Allowed; omega) (ordinary_zero input h256 hz)

/-- The successful 256 path. The direct-return trace is supplied by the relocated
instruction certificate; all input-dependent reasoning is proved here. -/
def hit (input : ByteArray) (saved : List UInt256)
    (moves : Moves (EarlySerializeReturn.prepared input saved) [])
    (h256 : input.size = 256) (hz : J2FusedAccumulator.resultAcc256 input = 0)
    (ret : GasSteps
      (atState (EarlySerializeReturn.prepared input saved) fusedReturnPC
        (J2FusedLoop.rest256 (EarlySerializeReturn.prepared input saved) []))
      (output input (J2FusedLoop.rest256 (EarlySerializeReturn.prepared input saved) []))) :
    GasSteps
      (atState (EarlySerializeReturn.prepared input saved) 4804
        [J2Raw.clamp (UInt256.ofNat input.size)])
      (output input (J2FusedLoop.rest256 (EarlySerializeReturn.prepared input saved) [])) :=
  (J2FusedLoop.gasSteps_hit256 _ [] moves h256 hz).trans ret

/-- The mismatch branch preserves the six-word frame suffix and prepared memory,
then enters the unchanged universal compressor. -/
def miss (input : ByteArray) (saved : List UInt256) (hfit : CalldataFits input)
    (moves : Moves (EarlySerializeReturn.prepared input saved) [])
    (h256 : input.size = 256) (hz : J2FusedAccumulator.resultAcc256 input ≠ 0) :
    GasSteps
      (atState (EarlySerializeReturn.prepared input saved) 4804
        [J2Raw.clamp (UInt256.ofNat input.size)])
      (StackTail.append (PaddingTrace.padFramed input)
        (J2FusedLoop.rest256 (EarlySerializeReturn.prepared input saved) [])) := by
  let s := EarlySerializeReturn.prepared input saved
  let rho := J2FusedLoop.rest256 s []
  have hc : rho.length ≤ 20 := by simp [rho, J2FusedLoop.rest256, J2Raw.finishRest]
  have gm := J2FusedLoop.gasSteps_miss256 s [] moves h256 hz
  have gf := EarlySerializeFallback.gasSteps input hfit (by omega)
    s.memory (EarlySerializeReturn.prepared_memory_size input saved) rho hc
  have gfm : GasSteps (atState s 4565 rho)
      (StackTail.append (PaddingTrace.padFramed input) rho) := by
    simpa only [atState, EarlySerializeFallback.incoming, s,
      EarlySerializeReturn.prepared, RecognitionSelectorResult.copied,
      EarlySerializeReturn.beforeCopy, EarlySerializeReturn.base] using gf
  exact gm.trans gfm

#print axioms ordinary_zero
#print axioms hit
#print axioms miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedCorrect
