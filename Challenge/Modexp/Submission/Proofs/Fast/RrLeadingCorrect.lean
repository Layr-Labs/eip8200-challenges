import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTrace
import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTail

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Complete direct RR-leading fast-path certificate

This module composes the unchanged setup and CCB hand-over, the concrete
direct-counter helper, and the generalized inherited RR suffix.  It restores
the public theorem names consumed by `Submission.Solution` without making
`Fast.Exp` depend on its own successor modules.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

/-- Everything after `Fast.Setup`: the hand-over, direct counter helper,
remaining RR suffix, exponent loop, and return. -/
theorem handled_of_handover (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hmpos : 0 < mm)
    (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0)
    (hxlt : Limbs.radix ^ (n - 1) < mm)
    (hframe0 : Frame mem n bsize minv)
    (hmod0 : Model.FastRepresents mem 0 n mm)
    (hr10 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hacc0 : Model.FastRepresents mem 1024 n 0)
    (hbase0 : Model.FastRepresents mem 2048 n 0)
    (hone0 : Model.FastRepresents mem 3072 n 0)
    (htz : Model.FastRepresents mem 8256 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (r1Call s mem 4096 (UInt256.ofNat 1526) n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hact296 : 296 ≤ s.activeWords.toNat :=
    Nat.le_trans (show 296 ≤ 298 by norm_num) hact
  let sub := subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
    hminvlt hminvA
  have hspec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv := by
    dsimp only [sub]
    exact specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32
      hmpos hminvlt hminvA hodd
  let directMem := setupToDirectMem (r1Mem n) (ccbMem n sub.mpMem sub.amMem) n mem
  have hframeDirect : Frame directMem n bsize minv := by
    dsimp only [directMem]
    exact setupToDirect_frame sub hn hn32 hframe0
  have hdirect := setupToDirect_facts n mm sub hspec hn hn32 hmpos hodd mem hframe0
    hmod0 hr10 hxlt htz
  have hmodDirect : Model.FastRepresents directMem 0 n mm := by
    simpa only [directMem] using hdirect.1
  have hr1Direct : Model.FastRepresents directMem 4096 n (Limbs.radix ^ n % mm) := by
    simpa only [directMem] using hdirect.2.1
  have hccDirect : Model.FastRepresents directMem 5120 n
      (Limbs.radix * Limbs.radix ^ n % mm) := by
    simpa only [directMem] using hdirect.2.2
  have haccDirect : Model.FastRepresents directMem 1024 n 0 := by
    dsimp only [directMem]
    exact setupToDirect_preserves sub hspec 1024 0 hn hn32 (by omega) (by omega) mem
      hacc0
  have hbaseDirect : Model.FastRepresents directMem 2048 n 0 := by
    dsimp only [directMem]
    exact setupToDirect_preserves sub hspec 2048 0 hn hn32 (by omega) (by omega) mem
      hbase0
  have honeDirect : Model.FastRepresents directMem 3072 n 0 := by
    dsimp only [directMem]
    exact setupToDirect_preserves sub hspec 3072 0 hn hn32 (by omega) (by omega) mem
      hone0
  have hhelper :=
    Bytecode.RrLeadingTrace.gasSteps_helper s directMem n bsize esize msize hn hn32
      hact hframeDirect.s32 hcode hfork hrun hnp
  obtain ⟨hexit, hframeCopy, hinvCopy, haccCopy, hbaseCopy, honeCopy, _⟩ :=
    RrLeadingExpBridge.direct_rejoin_facts s directMem n bsize esize msize mm
      (Limbs.radix ^ n) minv hn hn32 hact hframeDirect hmodDirect hr1Direct hccDirect
      haccDirect hbaseDirect honeDirect
  obtain ⟨final, ⟨trTail⟩, hdone, hres⟩ :=
    RrLeadingTail.handled_of_directRR input s (copiedMemory directMem n)
      n bsize esize msize mm minv sub hspec hcode hfork hrun hnp hdata hstack hact
      hn hn32 hb he hmz hm32 hbsize hesize hmsz hmm hodd hradix hframeCopy hinvCopy
      haccCopy hbaseCopy honeCopy
  have hhelper' : Challenge.EvmProof.GasSteps
      (entryState s directMem n bsize esize msize)
      (rrHead s (copiedMemory directMem n) n bsize esize msize
        (RrLeadingLogic.directCounter n)) :=
    Challenge.EvmProof.GasSteps.cast hhelper rfl hexit
  exact ⟨final, ⟨((gasSteps_handover s mem n bsize esize msize mm minv sub hspec
    hcode hfork hrun hnp hact hn hn32 hmpos hodd hmod0 hr10 hxlt htz hframe0).trans
      hhelper').trans trTail⟩, hdone, hres⟩

/- The fast-path certificate now lives in `Fast.ShiftCorrect`, which dispatches
between the shift-reduce base conversion and this RR-leading chain. -/

end Challenge.Modexp.Submission.Proofs.Fast.Exp
