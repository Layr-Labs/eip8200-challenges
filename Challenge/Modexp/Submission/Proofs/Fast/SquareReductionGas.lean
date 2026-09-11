import Challenge.Modexp.Submission.Proofs.Fast.SquareL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
import Challenge.Modexp.Submission.Proofs.Fast.SquareParts

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareReductionGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

def qBlock : Block Artifact.submissionArtifact .Osaka 4491 CiosReadonly.cachedProduct :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3426 16 4491 CiosReadonly.cachedProduct
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_reduce (s : State) (mem : ByteArray) (f pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hinv : CiosCachedMidMemory.inverseInvariant mem 8)
    (hroute : MachineState.readWord mem 9280 = UInt256.ofNat 5190)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps
      (stateAt s mem 4491 (f :: base pbi pa pb tag (UInt256.ofNat 4509) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)))
      (stateAt s (SquareReduce.reduction mem f)
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then 5190 else 4794)
        (base (negative32+pbi) pa pb tag (UInt256.ofNat 4509) inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  let mu := rowMu mem 8
  let c0 := rowC0 mem 8
  let S := SquareL2.state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hq : Challenge.EvmProof.GasSteps
      (stateAt s mem 4491 (f :: base pbi pa pb tag (UInt256.ofNat 4509) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) (S 4507 0) := by
    apply qBlock.steps (s := stateAt s mem 4491 (f :: base pbi pa pb tag (UInt256.ofNat 4509) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) (env.transfer rfl rfl) rfl
    exact CiosReadonly.run_cachedProduct_model {s with memory := mem} f pbi pa pb tag (UInt256.ofNat 4509)
      tl inv m0 aEnd m96 m64 m32 dst ret 8 rest hcap (by decide) hact hc hinv
  refine hq.trans <| (SquareL2.gasSteps_loops s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest
    hcap hact he env).trans ?_
  apply CarryRowBlocks.tailLoop.steps (s := S 4765 7) (env.transfer rfl rfl) rfl
  have hr : MachineState.readWord (l2Step mem mu c0 8 7).memory 9280 = UInt256.ofNat 5190 :=
    (SquareReduce.read_l2_outside mem mu c0 9280 (Or.inr (by decide)) 7 (by decide)).trans hroute
  have h := CarryRowRun.run_tail {s with memory := (l2Step mem mu c0 8 7).memory}
    (l2Step mem mu c0 8 7).carry mu f pbi pa pb tag (UInt256.ofNat 4509) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact (UInt256.ofNat 5190) hr
    (by change Decode.isValidJumpDest s.executionEnv.code 5190 = true; rw [env.code]; exact SquareParts.jump_row)
  simpa only [S, SquareL2.state, CiosCachedL2.state, SquareReduce.reduction, SquareReduce.tail,
    CarryRowModel.tailCarry, Monpro.tailMem1, storeWord, stateAt, framed, base, mu, c0,
    List.cons_append, List.nil_append, apply_ite UInt256.ofNat] using h

end Challenge.Modexp.Submission.Proofs.Fast.SquareReductionGas
