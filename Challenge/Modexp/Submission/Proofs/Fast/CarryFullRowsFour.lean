import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateInitialMultiply
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateGlobalBinding
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandCarrySnapshot
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

noncomputable section

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open CarryRowModel CarryResult

/-- The four rows of a four-limb multiply, from the row-0 head (`hd = 4261`) to the final
subtraction. -/
opaque gasSteps_rowsFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2048)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 4) pb 4 0 (UInt256.ofNat 3711) (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) := by
  have hcode' : s.executionEnv.code = TnCandidate.bytecode :=
    hcode.trans TnCandidateGlobalBinding.bytecode_eq
  have env := TnCandidateSquareSteps.environment s hcode' hfork hrun hnp
  have g := TnCandidateInitialMultiply.rows_steps s env mem pa pb 4
    (by decide) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    hpaFit hpb hpbFit hminv hc ⟨he.word96, he.word64, he.word32⟩ hAend hsnapshot
  simpa only [outState, TnCacheSetup.outState, TnCacheSetup.zeroTn,
    l1Target, l2Target, TnCacheSetup.l1Target, TnCacheSetup.l2Target,
    mpCsubState, CiosCachedMacCore.framed, List.cons_append, List.nil_append] using g

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
