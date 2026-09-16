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

* `n ∈ {4, 8}` with `minv ≠ 1`: the kernel keeps its row frame and performs all
  `count` squares itself (`Exp.Subroutines.squareLoop`), returning once to
  pc 782 with the pushed count still on the stack, where `FusedFinish` drops the
  count and reaches `Exp.finHead` at pc 784.  This is `Chain`.
* **S1b, other widths**: this artifact has no caller-side count-down loop and no
  separate mixed-domain product block.  The return address the loop head pushes
  is 800 — the trampoline into `modexpBig` at pc 238 — so the class leaves the
  fast path after the first square (`gasSteps_squareBail`) and is finished by the
  generic path.  `FixedDirectHitCorrect` composes the two.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- **S1b.** The return address `squareCall` pushes.

`jumpD3970` (pc 2260, the caller-side count-down loop head) and `jumpD3997`
(pc 784, the return from the final `MonPro`) are DELETED.  Both named blocks the
loop head reached in the parent image; in this artifact the loop head's own
`PUSH2` at instruction index 2043 is `0x0320`, i.e. 800 — the bail trampoline. -/
theorem jumpD800 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 800).toNat = true :=
  Exp.jumpD 800 (by decide) FixedDirectPaths.jumpDestBail

/-- The memory word the loop head writes holds the remaining square count. -/
theorem readWord_countStore (mem : ByteArray) (count : Nat) :
    MachineState.readWord (Exp.storeWord mem 2624 (UInt256.ofNat count)) 2624 =
      UInt256.ofNat count :=
  Challenge.EvmProof.Memory.readWord_writeWord mem 2624 (UInt256.ofNat count)

/-- **S1b.** The widths the kernel does not accelerate leave the fast path after
the *first* square, at `modexpBig`.

`gasSteps_squareLoop` used to run the caller's own count-down loop here and hand
the result to the final mixed-domain product.  Both blocks are gone from this
artifact — `FixedDirectPaths.squareReturn`, `FixedDirectPaths.product` and
`Exp.mpCall` were all deleted rather than renumbered, because exact byte search
over the whole 5,428-byte image finds their shapes zero times (see
`Bytecode.FixedDirectChainTrace.run_bailFromSquare`).  What the artifact actually
pushes as the square call's return address is 800, the six-word trampoline into
`modexpBig` at pc 238, so this class is finished by the generic path exactly as
the three recogniser misses are.  Nothing is assumed: the trampoline step is the
located `FixedDirectPaths.bail` block. -/
def gasSteps_squareBail (s : State) {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hslow : ¬ ((n = 4 ∨ n = 8) ∧ minv ≠ 1))
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
      (Exp.retTo s (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
        (UInt256.ofNat 238)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  have hframe0 := countStore_frame count hframe
  have hinv0 := countStore_inv count hn32 hinv
  ((FixedDirectChainTrace.gasSteps_squareCall s memory
      n bsize esize msize count hactive hcode hfork hrun hnp).trans
    (sub.square (UInt256.ofNat 800)
      (UInt256.ofNat count :: Exp.outer n bsize esize msize)
      (Exp.storeWord memory 2624 (UInt256.ofNat count)) bM
      hslow (by simp [Exp.outer])
      jumpD800 hframe0 hinv0.modulus hinv0.squareBase hbM)).trans
    (FixedDirectChainTrace.gasSteps_bailFromSquare s
      (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
      n bsize esize msize count hcode hfork hrun hnp)

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
        (UInt256.ofNat 782) (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  have hinv0 := countStore_inv count hn32 hinv
  (FixedDirectChainTrace.gasSteps_squareCall s memory
      n bsize esize msize count hactive hcode hfork hrun hnp).trans
    (sub.squareLoop count (UInt256.ofNat 800)
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

/-- **S1b.** `hfast` is now a hypothesis rather than a `by_cases`.

It is NOT a weakening that hides an unproved case.  `Chain` asserts arrival at
`Exp.finHead`, i.e. that the fast path *completes*; in this artifact only the
accelerated widths do that.  The unaccelerated widths reach `modexpBig` instead
(`gasSteps_squareBail`), which is a different and equally total conclusion, and
`FixedDirectHitCorrect.handled_of_fixed` — the sole caller — discharges `hfast`
in one branch of its own `by_cases` and proves the other through the bail.  No
case is dropped.

`_spec` and `_hm` were consumed only by the deleted unaccelerated branch; they
are kept as parameters so the call sites stay positionally unchanged. -/
def chain_of_fixed (s : State) {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (_spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix^n) minv)
    (memory : ByteArray) (esize msize count bM rawBase : Nat)
    (hfast : (n = 4 ∨ n = 8) ∧ minv ≠ 1)
    (_hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16) (hbM : bM < mm)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 512 n bM)
    (hrawAcc : Model.FastRepresents memory 256 n rawBase)
    (hrawLt : rawBase < mm)
    (hone : ∃ one, one < Limbs.radix ∧ Model.FastRepresents memory 768 n one)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Chain s sub memory esize msize count bM rawBase := by
  have hinv : Inv memory n mm rawBase bM := ⟨hmod,hrawAcc,hbase,hone⟩
  have hhead := FixedDirectChainTrace.gasSteps_start s memory
    n bsize esize msize count hn hn32 hactive hcode hfork hrun hnp
  let out := sub.sqLoopMem count (Exp.storeWord memory 2624 (UInt256.ofNat count))
  have hf0 := countStore_frame count hframe
  have hi0 := countStore_inv count hn32 hinv
  have hv : Model.FastRepresents out 256 n
      (Model.montMul mm (Limbs.radix^n) (fixedDirectValue mm (Limbs.radix^n) bM count) rawBase) := by
    rw [fixedDirectValue_eq_iterate]
    exact sub.sqLoopValue count _ bM rawBase hfast.1 hcount hf0 hi0.modulus
      hi0.squareBase hi0.rawAcc hbM hrawLt
  have hs := gasSteps_squareLoopFast s sub memory esize msize count bM rawBase hfast hcount
    hcount16 hn32 hbM hactive hframe hinv hcode hfork hrun hnp
  have hf := FusedFinish.gasSteps s out (UInt256.ofNat count) (Exp.outer n bsize esize msize)
    (by simp [Exp.outer]) hcode hfork hrun hnp
  exact ⟨out, (hhead.trans hs).trans hf, hv⟩

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
#print axioms Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect.chain_of_fixed
