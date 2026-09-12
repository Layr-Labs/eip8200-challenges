import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCompressionBridge
set_option warningAsError true
set_option maxRecDepth 20000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
open EvmSemantics Paired144WordRound StaggerCoreModel
open Paired80Compression (unpackLeft)
open StaggerFinalMemory (unpackRight unpackRight_packCrypto)
open StaggerRepresentation Paired80Algorithm

def initial (h : Compression.HashState) : WordLane :=
  StaggerScalarWord.embed (initialCrypto h)

def combine (h : Compression.HashState) (l r : WordLane) : Compression.HashState :=
  PairedCompressionBridge.combineLanes h (unpackLeft l) (unpackRight r)

def result (memory : ByteArray) (h : Compression.HashState) : Compression.HashState :=
  let q := paired memory (initial h)
  combine h (epilogue memory q) q

theorem result_eq_folds (memory : ByteArray) (words : Nat → UInt32)
    (h : Compression.HashState) (hm : StaggerMessage.Ready memory words) :
    result memory h = PairedCompressionBridge.combineLanes h
      (leftFold words 80 (initialCrypto h)) (rightFold words 80 (initialCrypto h)) := by
  obtain ⟨dd,de,hp,hd,he⟩ := StaggerCoreCorrect.paired_crypto memory words (initialCrypto h) hm
  dsimp only [result, initial, combine]
  rw [hp,StaggerCoreCorrect.epilogue_dirtyDE memory words _ _ hm dd de hd he,
    StaggerFinalMemory.unpackRight_dirtyDE _ _ dd de hd he,StaggerCoreCorrect.leftFinish_fold]

/-- Functional compression carries the initial hash explicitly on the stack. -/
theorem result_compressBlock (memory bs : ByteArray) (off : Nat)
    (h : Compression.HashState)
    (hm : StaggerMessage.Ready memory (fun i => (CompressionCorrect.schedule bs off)[i]!)) :
    CompressionCorrect.hashArray (result memory h) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs off := by
  rw [result_eq_folds memory _ h hm]
  exact PairedCompressionBridge.paired_compression_eq_spec bs off h
    (leftFold (fun i => (CompressionCorrect.schedule bs off)[i]!))
    (rightFold (fun i => (CompressionCorrect.schedule bs off)[i]!))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

#print axioms result_eq_folds
#print axioms result_compressBlock
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
