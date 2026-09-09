import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentLogic
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentChainTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Gas and invariant composition for the fixed-exponent square chain
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentLogic
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem jumpD3781 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3781).toNat = true :=
  Exp.jumpD 3781 (by decide) FixedExponentPaths.jumpDest3781

theorem jumpD3808 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3808).toNat = true :=
  Exp.jumpD 3772 (by decide) FixedExponentPaths.jumpDest3772

theorem jumpD3833 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3833).toNat = true :=
  Exp.jumpD 3833 (by decide) FixedExponentPaths.jumpDest3833

/-- Execute all remaining calls of the fixed squaring loop. -/
def gasSteps_squareLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (memory : ByteArray) (esize msize count bM acc : Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hcount : 1 ≤ count)
    (hcount16 : count ≤ 16) (_hbM : bM < mm) (hacc : acc < mm)
    (hframe : Exp.Frame memory n bsize minv)
    (hinv : Exp.EbInv memory n mm bM acc)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (square s memory n bsize esize msize count)
      (product s (squareMems sub.mpMem memory count)
        n bsize esize msize) := by
  induction count generalizing memory acc with
  | zero => omega
  | succ k ih =>
      have hcall := sub.monpro 1024 1024 1024 (UInt256.ofNat 3781)
        (UInt256.ofNat (k + 1) :: Exp.outer n bsize esize msize)
        memory acc acc (by simp [Exp.outer])
        (by omega) (by omega) (by omega) (by omega) (by omega)
        jumpD3781 hframe hinv.modulus hinv.accBlock hinv.accBlock hacc
      have hhead := FixedExponentChainTrace.gasSteps_squareCall
        s memory n bsize esize msize (k + 1) hcode hfork hrun hnp
      have hfirst : Challenge.EvmProof.GasSteps
          (square s memory n bsize esize msize (k + 1))
          (squareReturn s (sub.mpMem 1024 1024 1024 memory)
            n bsize esize msize (k + 1)) := hhead.trans hcall
      cases k with
      | zero =>
          exact hfirst.trans
            (FixedExponentChainTrace.gasSteps_squareReturnExit s
              (sub.mpMem 1024 1024 1024 memory) n bsize esize msize
              hcode hfork hrun hnp)
      | succ j =>
          have hnext := FixedExponentChainTrace.gasSteps_squareReturnLoop s
            (sub.mpMem 1024 1024 1024 memory) n bsize esize msize (j + 1)
            (by omega) (by omega) hcode hfork hrun hnp
          have hframe1 : Exp.Frame (sub.mpMem 1024 1024 1024 memory)
              n bsize minv :=
            sub.mpFrame 1024 1024 1024 memory (by omega) hframe
          have hinv1 := squareMems_inv sub spec memory hm hn32 hacc hframe hinv 1
          simp only [squareMems, squareValue] at hinv1
          have hrec := ih (memory := sub.mpMem 1024 1024 1024 memory)
            (acc := Model.montMul mm R acc acc) (by omega) (by omega)
            (Model.montMul_lt hm R acc acc) hframe1 hinv1
          have hall := (hfirst.trans hnext).trans hrec
          exact Challenge.EvmProof.GasSteps.cast hall rfl
            (by rw [squareMems_step_add])

/-- Copy BASE to ACC, then execute every squaring of a fixed chain. -/
def gasSteps_fixedSquares (s : State) {n bsize mm minv R : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (memory : ByteArray) (esize msize count bM : Nat)
    (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16) (hbM : bM < mm)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 2048 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 3072 n one)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (product s (fixedMems sub.mpMem n memory count)
        n bsize esize msize) := by
  let mem0 := Exp.mcopyMem memory 1024 2048 (32 * n)
  have hframe0 : Exp.Frame mem0 n bsize minv :=
    Exp.frame_mcopyMem (by omega) hframe
  have hinv0 : Exp.EbInv mem0 n mm bM bM := by
    simpa [mem0, fixedMems, fixedValue] using
      fixedMems_inv sub spec memory hm hn hn32 hbM hframe hmod hbase hone 0
  have hhead := FixedExponentChainTrace.gasSteps_start s memory
    n bsize esize msize count hn hn32 hactive hcode hfork hrun hnp
  have hhead' : Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (square s mem0 n bsize esize msize count) := by
    simpa [mem0, FixedExponentStates.initialSquareMem] using hhead
  have hcall := sub.monpro 1024 1024 1024 (UInt256.ofNat 3781)
    (UInt256.ofNat count :: Exp.outer n bsize esize msize)
    mem0 bM bM (by simp [Exp.outer])
    (by omega) (by omega) (by omega) (by omega) (by omega)
    jumpD3781 hframe0 hinv0.modulus hinv0.accBlock hinv0.accBlock hbM
  have hsquare := FixedExponentChainTrace.gasSteps_squareCall s mem0
    n bsize esize msize count hcode hfork hrun hnp
  have hfirst : Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (squareReturn s (sub.mpMem 1024 1024 1024 mem0)
        n bsize esize msize count) := (hhead'.trans hsquare).trans hcall
  rcases count with _ | k
  · omega
  · cases k with
    | zero =>
        exact hfirst.trans
          (FixedExponentChainTrace.gasSteps_squareReturnExit s
            (sub.mpMem 1024 1024 1024 mem0) n bsize esize msize
            hcode hfork hrun hnp)
    | succ j =>
        have hnext := FixedExponentChainTrace.gasSteps_squareReturnLoop s
          (sub.mpMem 1024 1024 1024 mem0) n bsize esize msize (j + 1)
          (by omega) (by omega) hcode hfork hrun hnp
        have hframe1 : Exp.Frame (sub.mpMem 1024 1024 1024 mem0)
            n bsize minv :=
          sub.mpFrame 1024 1024 1024 mem0 (by omega) hframe0
        have hinv1 := squareMems_inv sub spec mem0 hm hn32 hbM hframe0 hinv0 1
        simp only [squareMems, squareValue] at hinv1
        have hloop := gasSteps_squareLoop s sub spec
          (sub.mpMem 1024 1024 1024 mem0) esize msize (j + 1) bM
          (Model.montMul mm R bM bM) hm hn32 (by omega) (by omega) hbM
          (Model.montMul_lt hm R bM bM) hframe1 hinv1 hcode hfork hrun hnp
        have hall := (hfirst.trans hnext).trans hloop
        exact Challenge.EvmProof.GasSteps.cast hall rfl (by
          rw [fixedMems_eq_squareMems, squareMems_step_add])

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCorrect
