import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
-- S1b.  The unaccelerated widths bail into `modexpBig`; these are the same two
-- modules `FixedDirectRouteCorrect` imports for the recogniser-miss bail.
-- Neither depends on the FixedDirect subtree, so no cycle.
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMain
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUBlocks

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Correctness of a direct fixed-exponent hit

The retained normal-domain ACC supplies the last factor of the power. Its
mixed-domain product with squared Montgomery BASE needs no separate decode.
**S1b.** The two width classes no longer converge.  For `n ∈ {4, 8}` with
`minv ≠ 1` the kernel's in-kernel loop delivers a `FixedDirectChainCorrect.Chain`
and the mixed-domain product is read off it as before.  Every other width leaves
the fast path after the first square — the return address the loop head pushes is
the trampoline at pc 800 — and is finished by `modexpBig`, which re-reads the
header from calldata and is universal in the incoming memory and stack.  Both
branches end in `Handled`, so the caller sees no case split.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Exact correctness for either fixed chain, with arbitrary valid operands. -/
theorem handled_of_fixed (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize mm minv bM rawBase count : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input)
    (hstack : s.callStack = []) (hactive : 89 ≤ s.activeWords.toNat)
    -- S1b.  Needed only by the unaccelerated-width bail into `modexpBig`, which
    -- wants an UPPER bound on `activeWords` and the `size < 2 ^ 64` component of
    -- `ValidInput`.  Both already reach `FixedDirectRouteCorrect.route`.
    (hvalid : Challenge.Modexp.ValidInput input)
    (hactLe : s.activeWords.toNat ≤ 289)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmz : 32 < msize)
    (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hm : 0 < mm) (hcop : Nat.Coprime (Limbs.radix ^ n) mm) (_hradix : Limbs.radix ≤ mm)
    (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize *
      Limbs.radix ^ n [MOD mm])
    (hrawForm : rawBase ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm])
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16)
    (hexp : Precompile.bytesToNatPadded input (96 + bsize) esize =
      2 ^ count + 1)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 512 n bM)
    (hrawAcc : Model.FastRepresents memory 256 n rawBase)
    (hrawLt : rawBase < mm)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one) :
    FixedExponentRoute.Handled input
      (special s memory n bsize esize msize count) := by
  by_cases hfast : (n = 4 ∨ n = 8) ∧ minv ≠ 1
  case neg =>
    -- **S1b.**  The kernel does not accelerate this width, so it honours the
    -- return address `squareCall` pushed: 800, the trampoline into `modexpBig`
    -- at pc 238.  `bigC_correct` re-reads the header from calldata and is
    -- universal in the incoming memory and stack, so the frame the fast path
    -- built is simply discarded.
    have hhead := FixedDirectChainTrace.gasSteps_start s memory
      n bsize esize msize count hn hn32 hactive hcode hfork hrun hnp
    have hstep := gasSteps_squareBail s sub memory esize msize count bM rawBase
      hfast hn32 hbMlt hactive hframe ⟨hmod, hrawAcc, hbase, hone⟩ hcode hfork hrun hnp
    have hcd : (Exp.retTo s (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
      (UInt256.ofNat 238) (UInt256.ofNat count :: Exp.outer n bsize esize msize)).executionEnv.calldata
        = input := hdata
    have env : WindowTwentyOneBinding.Environment Artifact.submissionArtifact .Osaka
        (Exp.retTo s (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
          (UInt256.ofNat 238)
          (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
      { sizeBound := by
          change Challenge.Modexp.submissionBytecode.size < 2 ^ 256
          rw [Challenge.Modexp.submissionBytecode_size]
          decide
        code := by simpa [Exp.retTo, Artifact.submissionArtifact] using hcode
        forkEq := by simpa [Exp.retTo] using hfork
        running := by simpa [Exp.retTo] using hrun
        noPrecompile := by simpa [Exp.retTo] using hnp }
    obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
      BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
        BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks
        (Exp.retTo s (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
          (UInt256.ofNat 238)
          (UInt256.ofNat count :: Exp.outer n bsize esize msize))
        env rfl
        (by simp [Exp.retTo, Exp.outer])
        (show (Exp.retTo s (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
          (UInt256.ofNat 238) (UInt256.ofNat count :: Exp.outer n bsize esize msize)).activeWords.toNat
            ≤ 289 from hactLe)
        (show (Exp.retTo s (sub.sqMem (Exp.storeWord memory 2624 (UInt256.ofNat count)))
          (UInt256.ofNat 238) (UInt256.ofNat count :: Exp.outer n bsize esize msize)).callStack
            = [] from hstack)
        (by rw [hcd]; exact hvalid)
        (by rw [hcd, ← hmsz]; omega)
    exact ⟨final, ⟨(hhead.trans hstep).trans tail⟩, hdone, by rw [hres, hcd]⟩
  -- The accelerated widths complete the chain in the kernel, as before.
  let ch := chain_of_fixed s sub spec memory esize msize count bM rawBase
    hfast hm hn hn32 hcount hcount16 hbMlt hactive
    hframe hmod hbase hrawAcc hrawLt hone hcode hfork hrun hnp
  let sqVal := fixedDirectValue mm (Limbs.radix ^ n) bM count
  let prodVal := Model.montMul mm (Limbs.radix ^ n) sqVal rawBase
  let memOut := ch.mem
  have houtRep : Model.FastRepresents memOut 256 n prodVal := ch.value
  have htraceReturn := Exp.gasSteps_return s memOut n bsize esize msize
    hn hn32 hmz hm32 hactive hcode hfork hrun hnp
  have htrace : Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (Exp.returnedState s memOut n bsize esize msize) :=
    ch.trace.trans htraceReturn
  have houtEq : prodVal =
      Precompile.bytesToNatPadded input 96 bsize ^ (2 ^ count + 1) % mm :=
    directProduct_value hm hcop hbMform hrawForm
  refine Exp.handled_of_trace input
    (special s memory n bsize esize msize count) s memOut
    n bsize esize msize prodVal hstack htrace hn hm32 (by omega)
    hbsize hesize hmsz houtRep ?_
  rw [← hmm, Model.modPow_eq_pow_mod hm, hexp]
  exact houtEq

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect

#print axioms Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect.handled_of_fixed
