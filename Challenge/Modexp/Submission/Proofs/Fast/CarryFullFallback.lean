import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedFour
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedEight

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
open CarryRowModel CarryResult

/-- Every other width: `mul entry` → `common` fallback → the generic `MONPRO` (pc 1746). -/
opaque gasSteps_fallback (E : EntryLemmas) (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n) (hslow : ¬ StagedOperand.eligible mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  have hf := ((E.gasSteps_mulEntry s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp).trans
    (Cios2Dispatch.gasSteps_commonFallbackEligible s mem (UInt256.ofNat 3713) pa pb n pdst ret rest
      (by omega) hrun hcode hfork hnp hact hn hn32 hs32 hslow)).trans
    (gasSteps_monpro s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact
      hn hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml)
  have hz : ¬ StagedOperand.eligible (mpZeroed s mem n) n := by
    rw [StagedOperand.eligible_zeroed s mem n hn32]
    exact hslow
  simpa only [selectedRows, if_neg hz] using hf

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
