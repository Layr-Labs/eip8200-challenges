import Challenge.Ripemd160.Submission.Local20261028.PadModel
import Challenge.Ripemd160.Submission.Local20261028.PadReady
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyContract
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadFunctional
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
abbrev initial := PersistentStaggerFunctional.initial
abbrev combine := PersistentStaggerFunctional.combine
def result (len : UInt256) (h : Compression.HashState) : Compression.HashState :=
  let q := PadModel.paired len (initial h)
  combine h (PadModel.epilogue len q) q

theorem message_eq (n : Fin 3) (i : Nat) (hi : i < 77) :
    PadModel.message (PadMemory.length n) i = StaggerCoreModel.message (PadMemory.memory n) i := by
  have bounds := StaggerTableLayout.layout_valid ⟨i,hi⟩
  simp only [PadModel.message, StaggerCoreModel.message, ite_self]
  exact (PadMemory.load_eq n ⟨StaggerTableLayout.pairIndices[i]!, bounds.2.1⟩).symm

theorem fold_congr (f g : Nat → UInt256) (q : WordLane) (k : Nat)
    (heq : ∀ i, i < k → f i = g i) :
    StaggerModeSeven.fold f k q = StaggerModeSeven.fold g k q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg₂ (StaggerModeSeven.step k) (heq k (by omega))
      (ih (fun i hi => heq i (by omega)))

theorem fold_eq (n : Fin 3) (q : WordLane) (k : Nat) (hk : k ≤ 77) :
    StaggerModeSeven.fold (PadModel.message (PadMemory.length n)) k q =
      StaggerModeSeven.fold (StaggerCoreModel.message (PadMemory.memory n)) k q :=
  fold_congr _ _ q k (fun i hi => message_eq n i (by omega))

theorem load (n : Fin 3) (address : Nat) (j : Fin 61) (h : address = 18*j.val) :
    MachineState.readWord (PadMemory.memory n) address = PadValues.load (PadMemory.length n) address := by
  rw [h]
  exact PadMemory.load_eq n j

theorem prologue_eq (n : Fin 3) (q : WordLane) :
    PadModel.prologue (PadMemory.length n) q = StaggerCoreModel.prologue (PadMemory.memory n) q := by
  simp only [PadModel.prologue, StaggerCoreModel.prologue,
    PadModel.right0, PadModel.right1, PadModel.right2,
    StaggerCoreModel.right0, StaggerCoreModel.right1, StaggerCoreModel.right2]
  rw [load n 486 ⟨27,by decide⟩ rfl, load n 162 ⟨9,by decide⟩ rfl,
    load n 252 ⟨14,by decide⟩ rfl]

theorem paired_eq (n : Fin 3) (q : WordLane) :
    PadModel.paired (PadMemory.length n) q = StaggerCoreModel.paired (PadMemory.memory n) q := by
  unfold PadModel.paired StaggerCoreModel.paired
  rw [prologue_eq, fold_eq n _ 77 (by decide)]
  rfl

theorem epilogue_eq (n : Fin 3) (q : WordLane) :
    PadModel.epilogue (PadMemory.length n) q = StaggerCoreModel.epilogue (PadMemory.memory n) q := by
  simp only [PadModel.epilogue, StaggerCoreModel.epilogue, PadModel.left, StaggerCoreModel.left,
    PadModel.left77, PadModel.left78, PadModel.left79,
    StaggerCoreModel.left77, StaggerCoreModel.left78, StaggerCoreModel.left79]
  rw [load n 0 ⟨0,by decide⟩ rfl, load n 612 ⟨34,by decide⟩ rfl,
    load n 198 ⟨11,by decide⟩ rfl]

theorem result_eq (n : Fin 3) (h : Compression.HashState) :
    result (PadMemory.length n) h = PersistentStaggerFunctional.result (PadMemory.memory n) h := by
  simp only [result, PersistentStaggerFunctional.result, paired_eq, epilogue_eq]

theorem ready_schedule (input : ByteArray) (n : Fin 3) (hsize : input.size = 64*(n.val+1)) :
    StaggerMessage.Ready (PadMemory.memory n)
      (fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) input.size)[k]!) := by
  rw [PadReady.memory_eq_table]
  apply StaggerMessage.ready
  intro k hk
  have clean : ∀ n : Fin 3, ∀ k : Fin 16,
      StaggerTablePad.padWordsDirty (PadMemory.length n) k.val =
        PadOnlySchedule.padWords (PadMemory.length n) k.val := by decide
  rw [clean n ⟨k,hk⟩]
  have hfit : input.size < 2^64 := by have := n.isLt; rw [hsize]; omega
  have halign : input.size % 64 = 0 := by rw [hsize]; omega
  have hword := PadOnlySchedule.padWords_eq_cryptoWords input hfit halign k hk
  have hlen : UInt256.ofNat input.size = PadMemory.length n := by rw [hsize]; rfl
  rw [hlen] at hword
  rw [← hword]
  congr 1
  interval_cases k <;> simp [CompressionCorrect.schedule, List.range']

theorem result_compressBlock (input : ByteArray) (n : Fin 3)
    (hsize : input.size = 64*(n.val+1)) (h : Compression.HashState) :
    CompressionCorrect.hashArray (result (PadMemory.length n) h) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
        (Padding.paddedMessage input) input.size := by
  rw [result_eq]
  exact PersistentStaggerFunctional.result_compressBlock _ _ _ h (ready_schedule input n hsize)

#print axioms result_eq
#print axioms ready_schedule
#print axioms result_compressBlock
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadFunctional
