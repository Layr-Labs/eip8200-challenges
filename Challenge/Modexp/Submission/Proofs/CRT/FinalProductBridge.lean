import Challenge.Modexp.Submission.Proofs.CRT.LoopInvariant
import Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

noncomputable section

namespace HistoricalSearch.FinalProductBridge
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.LoopInvariant
open HistoricalSearch.PureLoop

theorem inverse {mem : ByteArray} {n : Nat → UInt256} {minv : UInt256}
    {f : CRTLoopFrames.Frame} {N : Nat} (hs : Static mem n minv f N) :
    CiosCachedMidMemory.inverseInvariant mem 8 := by
  have hlow : (MachineState.readWord mem 224).toNat = N%2^256 := by
    simpa [Limbs.radix] using Model.readLimb_of_fastRepresents hs.modulus (k:=0) (by decide)
  change ((MachineState.readWord mem 224).toNat * (MachineState.readWord mem 2720).toNat+1)%2^256=0
  rw [hlow, ←hs.cachedInverse]
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using hs.inverse

/-- The existing verified final mixed product consumes a completed CRT square.
Its saved control fields are arbitrary: the product entry overwrites them. -/
def product (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256)
    (f : CRTLoopFrames.Frame) (N A : Nat) (tn pbi ent : UInt256)
    (hs : Static mem n minv f N) (ha : Model.FastRepresents mem 2368 8 A)
    (hcap : f.rest.length ≤ 998)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256) :
    Challenge.EvmProof.GasSteps (atOld s mem 3256 tn pbi ent f)
      {s with pc := UInt256.ofNat 690, stack := f.rest, memory := StagedProduct.memory s mem 8} := by
  have hc : CiosReadonly.ReadonlyCache mem 8 f.tl f.inv f.m0 :=
    ⟨hs.tl.symm, hs.inv.symm, hs.m0.symm, hs.inverseGuard⟩
  have he : CiosReadonlyExtra.ExtraCache mem f.m96 f.m64 f.m32 :=
    ⟨hs.m96.symm, hs.m64.symm, hs.m32.symm⟩
  have g := FusedProductTrace.gasSteps_product tn s mem 6 A N pbi f.w3 ent f.tl f.inv
    f.m0 f.m96 f.m64 f.m32 f.aprev f.counter f.ret f.rest hcap (Or.inr rfl)
    hrun hcode hfork hnp hact hcds (inverse hs) hc he ha hs.modulus ha.1 hs.positive
    hs.ml hs.tlw hs.s32 (fun _ => hs.w3.symm)
  rw [hs.m128] at g
  exact g

/-- Value and preservation facts from the CRT round discharge every arithmetic
and cached-memory premise of the existing mixed-product execution theorem. -/
def round_product (s : State) (minv : UInt256) (n : Nat → UInt256) (mem : ByteArray)
    (f : CRTLoopFrames.Frame) (N k A : Nat) (tn pbi ent : UInt256)
    (h : Invariant mem n minv f N k A)
    (hcap : f.rest.length ≤ 998)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256) :
    Challenge.EvmProof.GasSteps (atOld s (finish s minv n mem) 3256 tn pbi ent f)
      {s with pc := UInt256.ofNat 690, stack := f.rest, memory := StagedProduct.memory s (finish s minv n mem) 8} := by
  have hr := one_round s minv n mem A N h.operand h.modulus h.positive h.odd
    h.toStatic.nlow h.toStatic.nhigh h.inverse
  exact product s (finish s minv n mem) n minv f N _ tn pbi ent
    (h.toStatic.transport (finish_live s minv n mem)) hr.1 hcap hrun hcode hfork hnp hact hcds

#print axioms inverse
#print axioms product
#print axioms round_product
end HistoricalSearch.FinalProductBridge
