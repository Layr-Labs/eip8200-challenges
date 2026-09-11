import Challenge.Modexp.Submission.Proofs.Fast.CarryFullRowsFour

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CarryRowGas CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult

opaque gasSteps_specializedFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsCarry (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) :=
  (gasSteps_dispatch4 s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
    (by simpa using hs32)).trans <|
  (gasSteps_entry s mem pa pb 4 pdst ret rest (by omega) hrun hcode hfork hnp hact
    (by decide) (by decide) hpa hpaFit hpb hpbFit hcds hs32 hml).trans <|
  gasSteps_rowsFour s mem pa pb
    (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
    (MachineState.readWord mem (32*4-32)) (UInt256.ofNat (pa+32*4-32)) (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) pdst ret rest (by omega) hrun hcode hfork hnp hact
    hpa hpaFit hpb hpbFit hs32 htl hml hminv ⟨htl, rfl, rfl⟩ ⟨rfl,rfl,rfl⟩ rfl

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
