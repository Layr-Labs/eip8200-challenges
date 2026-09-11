import Challenge.Modexp.Submission.Proofs.Fast.CarryFullDispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CarryRowGas CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand

attribute [local irreducible] SquarePrepared.prepared SquarePrepared.before Monpro.mpZeroed
  SquareRowsModel.rows CarryRowModel.rowsCarry Monpro.rowsMem

opaque gasSteps_monproCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (selectedRows (SquarePrepared.prepared s mem pa pb n) pa pb n n) 8224).toNat
      ≤ 1) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (selectedRows (SquarePrepared.prepared s mem pa pb n) pa pb n n) n n pdst ret
        rest) :=
  (gasSteps_toCsub s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact hn
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv).trans
    (Csub.gasSteps_csub s (selectedRows (SquarePrepared.prepared s mem pa pb n) pa pb n n) n pdst ret rest
      (by omega) hcode hfork hrun hnp hact hn hn32 hjump
      ((readWord_selected_preserved s mem pa pb n n 9408 hn32 (by omega) (by omega)).trans hml)
      ((readWord_selected_preserved s mem pa pb n n 9440 hn32 (by omega) (by omega)).trans htl)
      ((Csub.csStep_readWord_disjoint (selectedRows (SquarePrepared.prepared s mem pa pb n) pa pb n n) n 9344
            (by omega) (Or.inr (by omega)) n (Nat.le_refl n)).trans
        ((readWord_selected_preserved s mem pa pb n n 9344 hn32 (by omega) (by omega)).trans hs32))
      hdstFit
      (by
        rw [Csub.csStep_readWord_disjoint (selectedRows (SquarePrepared.prepared s mem pa pb n) pa pb n n) n
          8224 (by omega) (Or.inr (by omega)) n (Nat.le_refl n)]
        exact htn))

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
