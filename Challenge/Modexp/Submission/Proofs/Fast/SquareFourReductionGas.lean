import Challenge.Modexp.Submission.Proofs.Fast.SquareFourL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
import Challenge.Modexp.Submission.Proofs.Fast.SquareParts

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourReductionGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

def qBlock : Block Artifact.submissionArtifact .Osaka 4500 CiosReadonly.cachedProduct :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3431 16 4500 CiosReadonly.cachedProduct
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_reduce (s : State) (mem : ByteArray) (f pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hinv : CiosCachedMidMemory.inverseInvariant mem 4)
    (hroute : MachineState.readWord mem 9280 = UInt256.ofNat 5191)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps
      (stateAt s mem 4500 (f :: base pbi pa pb tag (UInt256.ofNat 4661) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)))
      (stateAt s (SquareFourReduce.reduction mem f)
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then 5191 else 4794)
        (base (negative32+pbi) pa pb tag (UInt256.ofNat 4661) inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  let mu := rowMu mem 4
  let c0 := rowC0 mem 4
  let S := SquareFourL2.state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hq : Challenge.EvmProof.GasSteps
      (stateAt s mem 4500 (f :: base pbi pa pb tag (UInt256.ofNat 4661) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) (S 4516 0) := by
    apply qBlock.steps (s := stateAt s mem 4500 (f :: base pbi pa pb tag (UInt256.ofNat 4661) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) (env.transfer rfl rfl) rfl
    exact CiosReadonly.run_cachedProduct_model {s with memory := mem} f pbi pa pb tag (UInt256.ofNat 4661)
      tl inv m0 aEnd m96 m64 m32 dst ret 4 rest hcap (by decide) hact hc hinv
  refine hq.trans <| (SquareFourL2.gasSteps_loops s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest
    hcap hact he env).trans ?_
  apply CarryRowBlocks.tailLoop.steps (s := S 4765 3) (env.transfer rfl rfl) rfl
  have hr : MachineState.readWord (l2Step mem mu c0 4 3).memory 9280 = UInt256.ofNat 5191 :=
    (SquareFourReduce.read_l2_outside mem mu c0 9280 (Or.inr (by decide)) 3 (by decide)).trans hroute
  have h := CarryRowRun.run_tail {s with memory := (l2Step mem mu c0 4 3).memory}
    (l2Step mem mu c0 4 3).carry mu f pbi pa pb tag (UInt256.ofNat 4661) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact (UInt256.ofNat 5191) hr
    (by change Decode.isValidJumpDest s.executionEnv.code 5191 = true; rw [env.code]; exact SquareParts.jump_row)
  simpa only [S, SquareFourL2.state, CiosCachedL2.state, SquareFourReduce.reduction, SquareFourReduce.tail,
    CarryRowModel.tailCarry, Monpro.tailMem1, storeWord, stateAt, framed, base, mu, c0,
    List.cons_append, List.nil_append, apply_ite UInt256.ofNat] using h

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourReductionGas
