import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificates

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

def leftCertificateChunk2 (i : Fin 16) :
    ImmediateSiteCertificate (leftData (32 + i.val)) := by
  fin_cases i <;>
    refine ⟨
      ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
        by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, ⟨by decide, trivial, rfl⟩⟩,
      by rfl, by rfl, by decide, ⟨by decide, trivial, rfl⟩⟩

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificates
