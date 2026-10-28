import Challenge.Ripemd160.Submission.Local20261028.PadGas
import Challenge.Ripemd160.Submission.Local20261028.FirstComplete
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadContract
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem hash_spec (input : ByteArray) (n : Fin 3) (hsize : input.size = 64*(n.val+1))
    (h : Compression.HashState)
    (hh : CompressionCorrect.hashArray h = CompressionSeamBridge.hashAfter input (n.val+1)) :
    CompressionCorrect.hashArray (PadFunctional.result (PadMemory.length n) h) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input) := by
  rw [PadFunctional.result_compressBlock input n hsize, hh]
  have hc : DriverTrace.blockCount input = (n.val+1)+1 := by
    unfold DriverTrace.blockCount Padding.paddedLength
    rw [hsize]
    omega
  rw [hc,StackRunBridge.hashAfter_succ input (n.val+1)]
  congr 1
  omega

theorem returned_spec (s : State) (input : ByteArray) (n : Fin 3)
    (hsize : input.size = 64*(n.val+1)) (h : Compression.HashState)
    (hh : CompressionCorrect.hashArray h = CompressionSeamBridge.hashAfter input (n.val+1))
    (off limit : UInt256) (rho : List UInt256) :
    (PadGas.result s (PadMemory.length n) h off limit rho).hReturn = Challenge.Ripemd160.spec input := by
  have ho := Return32Serialize.returned_spec_of_hashArray s input off limit rho
    (PadFunctional.result (PadMemory.length n) h) (hash_spec input n hsize h hh)
  rw [Return32Serialize.result_hReturn] at ho
  exact (PadGas.hReturn_eq s (PadMemory.length n) h off limit rho).trans ho

theorem correct_from_padding (s : State) (e : FirstEntry.Env s) (input : ByteArray) (n : Fin 3)
    (hsize : input.size = 64*(n.val+1)) (h : Compression.HashState)
    (hh : CompressionCorrect.hashArray h = CompressionSeamBridge.hashAfter input (n.val+1))
    (off limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 892)
    (hcal : s.executionEnv.calldata = input) (ha : 34 ≤ s.activeWords.toNat)
    (hcall : s.callStack = []) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (withGas {s with pc := UInt256.ofNat 64, stack := StaggerPersistentFrame.frame h off limit (DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho)} gas)
        (.returned (Challenge.Ripemd160.spec input)) := by
  have hg := PadGas.gasSteps s (PadMemory.length n) h off limit rho hs e.running ha
    (by rw [hcal,hsize]; rfl) e.code e.fork e.noPrecompile
  exact FirstComplete.eval_of_returned_trace _ _ _ hg rfl hcall
    (returned_spec s input n hsize h hh off limit rho)

#print axioms hash_spec
#print axioms returned_spec
#print axioms correct_from_padding
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadContract
