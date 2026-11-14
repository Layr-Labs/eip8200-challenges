import Challenge.Modexp.Submission.Proofs.Cycle.CachedInverse
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.PersistentMemory
open EvmSemantics Challenge.EvmProof
theorem keeps_base (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
 (start count : Nat) (hlo : 256 ≤ start) (hhi : start+count ≤ 768) :
 MachineState.readPadded (R9InvConsumeComplete.historyMemory mem inv a b n) start count =
 MachineState.readPadded mem start count := by
 unfold R9InvConsumeComplete.historyMemory
 repeat' rw [Memory.readPadded_writeBytes_disjoint _ _ start count _ (by
   simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
   omega)]
#print axioms keeps_base
end CycleSubmission.PersistentMemory
