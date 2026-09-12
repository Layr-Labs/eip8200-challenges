import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalBridge
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedBlockModel Paired80Algorithm StaggerRepresentation

theorem scheduled_hashAt (s : State) (i : Nat) :
    StackMemory.hashAt (scheduledState s i).memory = StackMemory.hashAt s.memory := by
  simp (discharger := omega) only [scheduledState, StackMemory.hashAt,
    StaggerTableLayout.read_resultMemory_outside]

theorem scheduled_ready (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    StaggerMessage.Ready (scheduledState s i).memory (blockWords input i) := by
  exact StaggerMessage.ready s.memory (selectedWords s i) (blockWords input i)
    (fun k hk => extracted_words s input i h hfit hi ctx k hk)

theorem desiredHash_eq_folds (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h) :
    desiredHash s input i = Compression.embedHash (PairedCompressionBridge.combineLanes h
      (leftFold (blockWords input i) 80 (initialCrypto h))
      (rightFold (blockWords input i) 80 (initialCrypto h))) := by
  have hc := PairedCompressionBridge.paired_compression_eq_spec
    (Padding.paddedMessage input) (DriverTrace.blockOffset i) h
    (leftFold (blockWords input i)) (rightFold (blockWords input i))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  unfold desiredHash
  rw [stateHash_of_context s input i h ctx, ← hc]
  rfl

theorem resultMemory_model (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    StaggerCoreModel.resultMemory (scheduledState s i).memory = (resultState s input i).memory := by
  have hh : StackMemory.hashAt (scheduledState s i).memory = Compression.embedHash h :=
    (scheduled_hashAt s i).trans ctx.hash
  rw [StaggerFinalMemory.resultMemory_eq_folds _ _ h hh
    (scheduled_ready s input i h hfit hi ctx), ← desiredHash_eq_folds s input i h ctx]
  rfl
#print axioms scheduled_ready
#print axioms desiredHash_eq_folds
#print axioms resultMemory_model
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalBridge
