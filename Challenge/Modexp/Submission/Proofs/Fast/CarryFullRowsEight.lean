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
open CiosCached CarryRowGas CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult

opaque gasSteps_rowsEight (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2912)
    (hs32 : MachineState.readWord mem 2784 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 2880 = UInt256.ofNat (2080 + 32 * 8))
    (hml : MachineState.readWord mem 2848 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8)
    (hcontrol : CarryControl.Control mem) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 8) pa pb 8 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) := by
  have hctrlz := hcontrol.zeroed s 8 (by decide)
  have hsz := hsnapshot.zeroed s (by decide) hpaFit
  have hs32z : MachineState.readWord (mpZeroed s mem 8) 2784 =
      UInt256.ofNat (32 * 8) :=
    (readWord_mpZeroed s mem 8 2784 (by decide) (by omega)).trans hs32
  have htlz : MachineState.readWord (mpZeroed s mem 8) 2880 =
      UInt256.ofNat (2080 + 32 * 8) :=
    (readWord_mpZeroed s mem 8 2880 (by decide) (by omega)).trans htl
  have hmlz : MachineState.readWord (mpZeroed s mem 8) 2848 =
      UInt256.ofNat (32 * 8 - 32) :=
    (readWord_mpZeroed s mem 8 2848 (by decide) (by omega)).trans hml
  have hminvz := inverse_mpZeroed s mem 8 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s 8 (by decide)
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s (rowsCarry (mpZeroed s mem 8) pa pb 8 i)
      pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) 7 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowEightNext s (rowsCarry (mpZeroed s mem 8) pa pb 8 i) pa pb i
      tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by omega) hpa hpaFit hpb
      hpbFit
      ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 2784 (by decide) (by omega)
        i).trans hs32z)
      ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 2880 (by decide) (by omega)
        i).trans htlz)
      ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 2848 (by decide) (by omega)
        i).trans hmlz)
      (inverse_rowsCarry (mpZeroed s mem 8) pa pb 8 i (by decide) hminvz)
      (readonlyCache_rowsCarry hcz (by decide) pa pb i)
      (extraCache_rowsCarry hez pa pb 8 i (by decide)) hAend (hsz.rows pb i (by decide) hpaFit) (hctrlz.rows pa pb 8 (by decide) i)
  · exact
      gasSteps_rowEightLast s (rowsCarry (mpZeroed s mem 8) pa pb 8 7) pa pb 7
        tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide) hpa hpaFit hpb
        hpbFit
        ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 2784 (by decide) (by omega)
          7).trans hs32z)
        ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 2880 (by decide) (by omega)
          7).trans htlz)
        ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 2848 (by decide) (by omega)
          7).trans hmlz)
        (inverse_rowsCarry (mpZeroed s mem 8) pa pb 8 7 (by decide) hminvz)
        (readonlyCache_rowsCarry hcz (by decide) pa pb 7)
        (extraCache_rowsCarry hez pa pb 8 7 (by decide)) hAend (hsz.rows pb 7 (by decide) hpaFit) (hctrlz.rows pa pb 8 (by decide) 7)

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
