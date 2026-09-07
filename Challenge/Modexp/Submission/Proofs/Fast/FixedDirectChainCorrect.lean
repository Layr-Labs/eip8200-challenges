import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Direct fixed-exponent squaring chain

BASE is squared in place while the reduced normal-domain base remains in ACC.
The final mixed-domain multiplication is composed in `FixedDirectHitCorrect`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem jumpD3970 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3970).toNat = true :=
  Exp.jumpD 3970 (by decide) FixedDirectPaths.jumpDest3970

theorem jumpD3997 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3997).toNat = true :=
  Exp.jumpD 3997 (by decide) FixedDirectPaths.jumpDest3997

/-- Execute the remaining positive number of in-place BASE squares. -/
def gasSteps_squareLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hcount : 1 ≤ count)
    (hcount16 : count ≤ 16) (hbM : bM < mm)
    (hframe : Exp.Frame memory n bsize minv)
    (hinv : Inv memory n mm rawBase bM)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (square s memory n bsize esize msize count)
      (product s (fixedDirectMems sub.mpMem memory count)
        n bsize esize msize) := by
  induction count generalizing memory bM with
  | zero => omega
  | succ k ih =>
      have hcall := sub.monpro 2048 2048 2048 (UInt256.ofNat 3970)
        (UInt256.ofNat (k + 1) :: Exp.outer n bsize esize msize)
        memory bM bM (by simp [Exp.outer])
        (by omega) (by omega) (by omega) (by omega) (by omega)
        jumpD3970 hframe hinv.modulus hinv.squareBase hinv.squareBase hbM
      have hhead := FixedDirectChainTrace.gasSteps_squareCall
        s memory n bsize esize msize (k + 1) hcode hfork hrun hnp
      have hfirst : Challenge.EvmProof.GasSteps
          (square s memory n bsize esize msize (k + 1))
          (squareReturn s (sub.mpMem 2048 2048 2048 memory)
            n bsize esize msize (k + 1)) := hhead.trans hcall
      cases k with
      | zero =>
          exact hfirst.trans
            (FixedDirectChainTrace.gasSteps_squareReturnExit s
              (sub.mpMem 2048 2048 2048 memory) n bsize esize msize
              hcode hfork hrun hnp)
      | succ j =>
          have hnext := FixedDirectChainTrace.gasSteps_squareReturnLoop s
            (sub.mpMem 2048 2048 2048 memory) n bsize esize msize (j + 1)
            (by omega) (by omega) hcode hfork hrun hnp
          have hframe1 : Exp.Frame (sub.mpMem 2048 2048 2048 memory)
              n bsize minv :=
            sub.mpFrame 2048 2048 2048 memory (by omega) hframe
          have hinv1 := fixedDirectMems_inv sub spec memory hm hn32 hbM
            hframe hinv 1
          simp only [fixedDirectMems, fixedDirectValue] at hinv1
          have hrec := ih (memory := sub.mpMem 2048 2048 2048 memory)
            (bM := Model.montMul mm R bM bM) (by omega) (by omega)
            (Model.montMul_lt hm R bM bM) hframe1 hinv1
          have hall := (hfirst.trans hnext).trans hrec
          exact Challenge.EvmProof.GasSteps.cast hall rfl
            (by rw [fixedDirectMems_step_add])

/-- Enter the fixed chain without copying BASE over the retained raw ACC. -/
def gasSteps_fixedSquares (s : State) {n bsize mm minv R : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16) (hbM : bM < mm)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 2048 n bM)
    (hrawAcc : Model.FastRepresents memory 1024 n rawBase)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 3072 n one)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (product s (fixedDirectMems sub.mpMem memory count)
        n bsize esize msize) := by
  have hhead := FixedDirectChainTrace.gasSteps_start s memory
    n bsize esize msize count hn hn32 hactive hcode hfork hrun hnp
  have hloop := gasSteps_squareLoop s sub spec memory esize msize count
    bM rawBase hm hn32 hcount hcount16 hbM hframe
    ⟨hmod, hrawAcc, hbase, hone⟩ hcode hfork hrun hnp
  exact hhead.trans hloop

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect

#print axioms Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect.gasSteps_fixedSquares
