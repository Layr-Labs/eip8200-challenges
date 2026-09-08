import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryCache
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryZero
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryPointers
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryOut

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntry

open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel MonproKNRowPrograms MonproKNRowFrames
open MonproKNEntryDefs MonproKNEntryCache MonproKNEntryZero MonproKNEntryPointers
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions entryProgram (entry s mem pa pb dst ret rest) =
      some (outer s (mpZeroed s mem n) pa pb n 0 dst ret rest) := by
  rw [entryProgram_eq]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_cache s mem pa pb dst ret rest hcap)
      (run_zero s mem pa pb n dst ret rest hcap hact hn hcds hs32))
    (run_pointers s mem pa pb n dst ret rest hcap hpa hpaFit hpb hpbFit)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntry
