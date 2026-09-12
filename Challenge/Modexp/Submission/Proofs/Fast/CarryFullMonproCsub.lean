import Challenge.Modexp.Submission.Proofs.Fast.CarryFullDispatch

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

opaque gasSteps_monproCsub (L : RowLemmas) (E : EntryLemmas) (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 4096)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 5376)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 5248 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 5344 = UInt256.ofNat (4128 + 32 * n))
    (hml : MachineState.readWord mem 5312 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 5376)
    (htn : (MachineState.readWord (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) 4128).toNat
      ≤ 1) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n n pdst ret
        rest) :=
  (gasSteps_toCsub L E s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact hn
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv).trans
    (Csub.gasSteps_csub s (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n pdst ret rest
      (by omega) hcode hfork hrun hnp hact hn hn32 hjump
      ((readWord_selected_preserved s mem pa pb n n 5312 hn32 (by omega)).trans hml)
      ((readWord_selected_preserved s mem pa pb n n 5344 hn32 (by omega)).trans htl)
      ((Csub.csStep_readWord_disjoint (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n 5248
            (by omega) (Or.inr (by omega)) n (Nat.le_refl n)).trans
        ((readWord_selected_preserved s mem pa pb n n 5248 hn32 (by omega)).trans hs32))
      hdstFit
      (by
        rw [Csub.csStep_readWord_disjoint (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n
          4128 (by omega) (Or.inr (by omega)) n (Nat.le_refl n)]
        exact htn))

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
