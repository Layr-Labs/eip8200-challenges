import Challenge.Modexp.Submission.Proofs.CRT.CRTMaskElision
import Challenge.Modexp.Submission.Proofs.CRT.CRTMemoryBounds
import Challenge.Modexp.Submission.Proofs.CRT.CRTMemoryCells
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace HistoricalSearch.LifetimeCache
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Memory

/-- Semantic column states retain the original modulus frame. Executed states
borrow n8 before its first use, then n0 after its last use. The final state
restores the original frame before any branch or loop edge. -/
def cachedState (stage : Nat) (s : State) : State :=
  if stage = 0 ∨ 17 ≤ stage then s
  else if stage ≤ 8 then
    {s with stack := s.stack.set 10 (MachineState.readWord s.memory 1056)}
  else {s with stack := s.stack.set 2 (MachineState.readWord s.memory 1312)}

theorem read_store_disjoint (mem : ByteArray) (word : UInt256) (dst src : Nat)
    (hd : src+32 ≤ dst ∨ dst+32 ≤ src) :
    MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded word.toNat 32) dst) src =
      MachineState.readWord mem src := by
  apply readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hd

end HistoricalSearch.LifetimeCache
