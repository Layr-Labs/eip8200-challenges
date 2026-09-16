import Challenge.Modexp.Submission.Proofs.Fast.TnM128InitialMultiply
import Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
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

/-- The eight rows of an eight-limb multiply, from the row-0 head (`hd = 4261`) to the final
subtraction. -/
opaque gasSteps_rowsEight (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2048)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 8) pb 8 0 (UInt256.ofNat 3358) (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) := by
  have hcode' : s.executionEnv.code = TnM128Candidate.bytecode :=
    hcode.trans TnM128GlobalBinding.bytecode_eq
  have env := TnM128SquareSteps.environment s hcode' hfork hrun hnp
  have g := TnM128InitialMultiply.rows_steps s env mem pa pb 8
    (by decide) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    hpaFit hpb hpbFit hminv hc ⟨he.word96, he.word64, he.word32⟩ hAend hsnapshot
  simpa only [outState, TnM128Setup.outState, TnM128Setup.zeroTn,
    l1Target, TnM128Setup.l1Target,
    mpCsubState, CiosCachedMacCore.framed, List.cons_append, List.nil_append] using g

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
