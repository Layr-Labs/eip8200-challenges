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
open CiosCached CiosCachedMidMemory CarryIface
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand

opaque gasSteps_toCsub (L : RowLemmas) (E : EntryLemmas) (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) pdst ret rest) := by
  by_cases he : eligible mem n
  · have hprepared : eligible (mpZeroed s (inputMemory mem pa n) n) n :=
      (eligible_zeroed s _ n hn32).2 ((eligible_inputMemory mem pa n).2 he)
    rw [selectedRows, if_pos hprepared, inputMemory, if_pos he]
    by_cases hn4 : n = 4
    · subst n
      exact gasSteps_specializedFour L E s mem pa pb pdst ret rest hcap hrun hcode
        hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv he.2
    · have hn8 : n = 8 := he.1.resolve_left hn4
      subst n
      exact gasSteps_specializedEight L E s mem pa pb pdst ret rest hcap hrun hcode
        hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv he.2
  · rw [inputMemory, if_neg he]
    exact gasSteps_fallback E s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
      hn32 hpa (by omega) hpb hpbFit hcds hs32 htl hml hminv he

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
