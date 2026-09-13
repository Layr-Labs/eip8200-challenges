import Challenge.Modexp.Submission.Proofs.Fast.FusedFinish
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Direct fixed-exponent squaring chain

BASE is squared in place by the `SQUARE` kernel while the reduced normal-domain
base remains in ACC.  The loop head stores the number of remaining squares in
memory word `0x2440 = 2624` and calls the kernel; from there the chain runs one
of two ways, and `Chain` is what both of them hand to the final product:

* `n ∈ {4, 8}`: the kernel keeps its row frame and performs all `count` squares
  itself (`Exp.Subroutines.squareLoop`), returning once to `after_sq` (pc 3360)
  with the pushed count still on the stack;
* other widths: the kernel returns after every square
  (`Exp.Subroutines.square`) and the caller's own loop at pc 3285 counts down,
  falling through to pc 3360 with the count at `0`.

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
    (UInt256.ofNat 2753).toNat = true :=
  Exp.jumpD 2753 (by decide) FixedDirectPaths.jumpDest3970

theorem jumpD3997 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1160).toNat = true :=
  Exp.jumpD 1160 (by decide) jumpDest1802

/-- The memory word the loop head writes holds the remaining square count. -/
theorem readWord_countStore (mem : ByteArray) (count : Nat) :
    MachineState.readWord (Exp.storeWord mem 2624 (UInt256.ofNat count)) 2624 =
      UInt256.ofNat count :=
  Challenge.EvmProof.Memory.readWord_writeWord mem 2624 (UInt256.ofNat count)

/-- Execute the remaining positive number of in-place BASE squares with the
kernel returning to the caller after each one (the unaccelerated widths). -/
def gasSteps_squareLoop (s : State) {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hslow : ¬ ((n = 4 ∨ n = 8) ∧ minv ≠ 1))
    (hm : 0 < mm) (hn32 : n ≤ 8) (hcount : 1 ≤ count)
    (hcount16 : count ≤ 16) (hbM : bM < mm)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame memory n bsize minv)
    (hinv : Inv memory n mm rawBase bM)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (square s memory n bsize esize msize count)
      (product s (fixedDirectMems sub.sqMem memory count)
        n bsize esize msize 0) := by
  induction count generalizing memory bM with
  | zero => omega
  | succ k ih =>
      have hframe0 := countStore_frame (k + 1) hframe
      have hinv0 := countStore_inv (k + 1) hn32 hinv
      have hcall := sub.square (UInt256.ofNat 2753)
        (UInt256.ofNat (k + 1) :: Exp.outer n bsize esize msize)
        (Exp.storeWord memory 2624 (UInt256.ofNat (k + 1))) bM
        hslow (by simp [Exp.outer])
        jumpD3970 hframe0 hinv0.modulus hinv0.squareBase hbM
      have hhead := FixedDirectChainTrace.gasSteps_squareCall
        s memory n bsize esize msize (k + 1) hactive hcode hfork hrun hnp
      have hfirst : Challenge.EvmProof.GasSteps
          (square s memory n bsize esize msize (k + 1))
          (squareReturn s
            (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat (k + 1))))
            n bsize esize msize (k + 1)) := hhead.trans hcall
      cases k with
      | zero =>
          exact hfirst.trans
            (FixedDirectChainTrace.gasSteps_squareReturnExit s
              (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat 1)))
              n bsize esize msize hcode hfork hrun hnp)
      | succ j =>
          have hnext := FixedDirectChainTrace.gasSteps_squareReturnLoop s
            (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat (j + 1 + 1))))
            n bsize esize msize (j + 1)
            (by omega) (by omega) hcode hfork hrun hnp
          have hframe1 : Exp.Frame
              (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat (j + 1 + 1))))
              n bsize minv := sub.sqFrame _ hframe0
          have hinv1 : Inv
              (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat (j + 1 + 1))))
              n mm rawBase (Model.montMul mm (Limbs.radix ^ n) bM bM) := by
            obtain ⟨one, honeLt, honeRep⟩ := hinv0.oneBlock
            exact ⟨sub.sqKeep 0 mm _ (by omega) (Or.inr (by omega)) hinv0.modulus,
              sub.sqKeep 256 rawBase _ (by omega) (Or.inr (by omega)) hinv0.rawAcc,
              sub.sqValue _ _ hframe0 hinv0.modulus hinv0.squareBase hbM,
              ⟨one, honeLt,
                sub.sqKeep 768 one _ (by omega) (Or.inl (by omega)) honeRep⟩⟩
          have hrec := ih (memory :=
              sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat (j + 1 + 1))))
            (bM := Model.montMul mm (Limbs.radix ^ n) bM bM) (by omega) (by omega)
            (Model.montMul_lt hm (Limbs.radix ^ n) bM bM) hframe1 hinv1
          exact (hfirst.trans hnext).trans hrec

/-- Execute all `count` in-place BASE squares inside the kernel (`n ∈ {4, 8}`),
which returns only once, to `after_sq`. -/
def gasSteps_squareLoopFast (s : State) {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hfast : (n = 4 ∨ n = 8) ∧ minv ≠ 1) (hcount : 1 ≤ count) (hcount16 : count ≤ 16)
    (hn32 : n ≤ 8) (hbM : bM < mm)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame memory n bsize minv)
    (hinv : Inv memory n mm rawBase bM)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (square s memory n bsize esize msize count)
      (Exp.retTo s
        (sub.sqLoopMem count (Exp.storeWord memory 2624 (UInt256.ofNat count)))
        (UInt256.ofNat 1158) (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  have hinv0 := countStore_inv count hn32 hinv
  (FixedDirectChainTrace.gasSteps_squareCall s memory
      n bsize esize msize count hactive hcode hfork hrun hnp).trans
    (sub.squareLoop count (UInt256.ofNat 2753)
      (UInt256.ofNat count :: Exp.outer n bsize esize msize)
      (Exp.storeWord memory 2624 (UInt256.ofNat count)) bM
      hfast hcount hcount16 (by simp [Exp.outer])
      (readWord_countStore memory count)
      (countStore_frame count hframe) hinv0.modulus hinv0.squareBase hbM)

/-- Both width routes deliver the final mixed-domain product at the output block. -/
structure Chain (s : State) {n bsize mm minv : Nat}
    (_sub : Exp.Subroutines s n bsize mm minv) (memory : ByteArray)
    (esize msize count bM rawBase : Nat) where
  mem : ByteArray
  trace : Challenge.EvmProof.GasSteps
    (special s memory n bsize esize msize count)
    (Exp.finHead s mem n bsize esize msize)
  value : Model.FastRepresents mem 256 n
    (Model.montMul mm (Limbs.radix^n) (fixedDirectValue mm (Limbs.radix^n) bM count) rawBase)

def chain_of_fixed (s : State) {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix^n) minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16) (hbM : bM < mm)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 512 n bM)
    (hrawAcc : Model.FastRepresents memory 256 n rawBase)
    (hone : ∃ one, one < Limbs.radix ∧ Model.FastRepresents memory 768 n one)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Chain s sub memory esize msize count bM rawBase := by
  have hinv : Inv memory n mm rawBase bM := ⟨hmod,hrawAcc,hbase,hone⟩
  have hhead := FixedDirectChainTrace.gasSteps_start s memory
    n bsize esize msize count hn hn32 hactive hcode hfork hrun hnp
  by_cases hfast : (n=4 ∨ n=8) ∧ minv ≠ 1
  · let out := sub.sqLoopMem count (Exp.storeWord memory 2624 (UInt256.ofNat count))
    have hf0 := countStore_frame count hframe
    have hi0 := countStore_inv count hn32 hinv
    have hv : Model.FastRepresents out 256 n
        (Model.montMul mm (Limbs.radix^n) (fixedDirectValue mm (Limbs.radix^n) bM count) rawBase) := by
      rw [fixedDirectValue_eq_iterate]
      exact sub.sqLoopValue count _ bM rawBase hfast.1 hcount hf0 hi0.modulus
        hi0.squareBase hi0.rawAcc hbM
    have hs := gasSteps_squareLoopFast s sub memory esize msize count bM rawBase hfast hcount
      hcount16 hn32 hbM hactive hframe hinv hcode hfork hrun hnp
    have hf := FusedFinish.gasSteps s out (UInt256.ofNat count) (Exp.outer n bsize esize msize)
      (by simp [Exp.outer]) hcode hfork hrun hnp
    exact ⟨out, (hhead.trans hs).trans hf, hv⟩
  · let memSq := fixedDirectMems sub.sqMem memory count
    let sqVal := fixedDirectValue mm (Limbs.radix^n) bM count
    have hfSq : Exp.Frame memSq n bsize minv := fixedDirectMems_frame sub count memory hframe
    have hiSq : Inv memSq n mm rawBase sqVal :=
      fixedDirectMems_inv sub hm hn32 rawBase count memory bM hbM hframe hinv
    have hsqLt : sqVal < mm := fixedDirectValue_lt hm hbM count
    have hs := gasSteps_squareLoop s sub memory esize msize count bM rawBase hfast hm hn32
      hcount hcount16 hbM hactive hframe hinv hcode hfork hrun hnp
    have hpc := FixedDirectChainTrace.gasSteps_product s memSq n bsize esize msize 0 hcode hfork hrun hnp
    have hmp := sub.monpro 512 256 256 (UInt256.ofNat 1160) (Exp.outer n bsize esize msize)
      memSq sqVal rawBase (by simp [Exp.outer]) (by omega) (by omega) (by omega) (by omega)
      (by omega) jumpD3997 hfSq hiSq.modulus hiSq.squareBase hiSq.rawAcc hsqLt
    have hv := spec.mpValueRaw 512 256 256 memSq sqVal rawBase
      (by omega) (by omega) (by omega) hiSq.modulus hfSq.minvW hiSq.squareBase hiSq.rawAcc hsqLt
    exact ⟨_, ((hhead.trans hs).trans hpc).trans hmp, hv⟩

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
#print axioms Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect.chain_of_fixed
