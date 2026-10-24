import Challenge.Modexp.Submission.Proofs.CycleGlobal.EarlyCsubInstructions
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128InitialMultiply
import Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandCarrySnapshot
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

noncomputable section

namespace CycleSubmission.Global.Fast.CarryFull
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open CarryRowModel CarryResult

/-- The 4 rows of a four-limb multiply (multiplier at `0x100`), from the row-0 head to the
final subtraction. -/
opaque gasSteps_rowsFour (s : State) (mem : ByteArray) (pa : Nat)
    (w3 ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (TnM128RowsSteps.rowState s ⟨mpZeroed s mem 4, UInt256.ofNat 0⟩ 4 0 w3 ent tl inv m0 aEnd
        m96 m64 m32 pdst ret rest)
      (CycleSubmission.Global.Fast.EarlyCsub.atState s (rowsCarry (mpZeroed s mem 4) pa 256 4 4) 3442 pdst ret rest) := by
  have env : WindowTwentyOneBinding.Environment CycleSubmission.Artifact.artifact .Osaka s :=
    ⟨by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; decide, hcode,hfork,hrun,hnp⟩
  have g := TnM128InitialMultiply.rows_steps s env mem pa 4
    (by decide) w3 ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    hpaFit hminv hc ⟨he.word96, he.word64, he.word32⟩ hAend hsnapshot (fun h => absurd h (by decide))
  simpa only [CycleSubmission.Global.Fast.EarlyCsub.atState, CiosCachedMacCore.framed, List.cons_append, List.nil_append] using g

end CycleSubmission.Global.Fast.CarryFull
