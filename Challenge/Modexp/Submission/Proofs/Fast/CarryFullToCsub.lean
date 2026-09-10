import Challenge.Modexp.Submission.Proofs.Fast.CarryFullFallback

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

opaque gasSteps_toCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  by_cases hn4 : n = 4
  · subst n
    rw [selectedRows, if_pos (Or.inl rfl)]
    exact gasSteps_specializedFour s mem pa pb pdst ret rest (by omega) hrun hcode
      hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv
  by_cases hn8 : n = 8
  · subst n
    rw [selectedRows, if_pos (Or.inr rfl)]
    exact gasSteps_specializedEight s mem pa pb pdst ret rest (by omega) hrun hcode
      hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv
  exact gasSteps_fallback s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
    hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv hn4 hn8

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
