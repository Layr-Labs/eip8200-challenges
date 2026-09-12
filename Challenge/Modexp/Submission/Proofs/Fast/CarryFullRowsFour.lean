import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandCarrySnapshot
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase

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

/-- The four rows of a four-limb multiply, from the row-0 head (`hd = 4037`) to the final
subtraction. -/
opaque gasSteps_rowsFour (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 4) pb 4 0 (UInt256.ofNat 4012) (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) := by
  have hsz := hsnapshot.zeroed s (by decide) hpaFit
  have hminvz := inverse_mpZeroed s mem 4 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s 4 (by decide)
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s (rowsCarry (mpZeroed s mem 4) pa pb 4 i)
      pb 4 i (UInt256.ofNat 4012) (l1Target 4) inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) 3 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowFourNext L s (rowsCarry (mpZeroed s mem 4) pa pb 4 i) pa pb i
      tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by omega)
      hpaFit hpb hpbFit
      (inverse_rowsCarry (mpZeroed s mem 4) pa pb 4 i (by decide) hminvz)
      (readonlyCache_rowsCarry hcz (by decide) pa pb i)
      (extraCache_rowsCarry hez pa pb 4 i (by decide)) hAend (hsz.rows pb i (by decide) hpaFit)
  · exact
      gasSteps_rowFourLast L s (rowsCarry (mpZeroed s mem 4) pa pb 4 3) pa pb 3
        tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide)
        hpaFit hpb hpbFit
        (inverse_rowsCarry (mpZeroed s mem 4) pa pb 4 3 (by decide) hminvz)
        (readonlyCache_rowsCarry hcz (by decide) pa pb 3)
        (extraCache_rowsCarry hez pa pb 4 3 (by decide)) hAend (hsz.rows pb 3 (by decide) hpaFit)

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
