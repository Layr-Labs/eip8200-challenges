import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNRowPrograms MonproKNRowFrames MonproKNCache MonproKNEntryDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_cache (s : State) (mem : ByteArray) (pa pb : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions cacheProgram (entry s mem pa pb dst ret rest) =
      some (cached s mem pa pb dst ret rest) := by
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  simp [cacheProgram, createProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    entry, cached, negative32, allOnes, hc4, hc5, hc6, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  decide


end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryCache
