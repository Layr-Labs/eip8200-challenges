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
        (r1Call s mem 4096 (UInt256.ofNat 1533) n bsize esize msize) final) ∧
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
  let directMem := setupToDirectMem (r1Mem n) (ccbMem sub.mpMem sub.amMem) n mem
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

/-- **Fast-path certificate.** Every `ValidInput` on the fast path runs from
the retargeted entry to the MODEXP result. -/
theorem gasSteps_handled (input : ByteArray)
    (hvalid : Challenge.Modexp.ValidInput input)
    (hpath : Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Main.trampolineState input 1314) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hsize : input.size < 2 ^ 256 := lt_trans hvalid.1 (by norm_num)
  have hn : 2 ≤ Setup.limbs input := Setup.limbs_ge_two input hpath.1
  have hn32 : Setup.limbs input ≤ 32 := Setup.fastSetup_limbs_le_32 input hpath
  have hodd : Setup.modulus input % 2 = 1 := hpath.2.2.2
  have hradix : Limbs.radix ≤ Setup.modulus input := by
    have h1 : Limbs.radix ^ 1 ≤ Limbs.radix ^ (Setup.limbs input - 1) :=
      Nat.pow_le_pow_right (le_of_lt Limbs.radix_gt_one) (by omega)
    have h2 := hpath.2.2.1
    rw [pow_one] at h1
    omega
  have hmpos : 0 < Setup.modulus input := lt_of_lt_of_le Limbs.radix_pos hradix
  have hminvlt : Setup.minvValue input < 2 ^ 256 := Setup.negWord_lt _
  have hminvA : (Setup.modulus input % Limbs.radix * Setup.minvValue input + 1)
      % 2 ^ 256 = 0 := by
    have h := Setup.fastSetup_minv input hpath
    rw [Setup.fastSetup_lowLimb input hpath] at h
    exact h
  have hxlt : Limbs.radix ^ (Setup.limbs input - 1) < Setup.modulus input :=
    Model.radix_pow_lt_of_odd hn hpath.2.2.1 hodd
  have hact : 298 ≤ (Setup.fastSetupState input).activeWords.toNat := by
    rw [Setup.fastSetup_activeWords input hpath, toNat_ofNat_self (by norm_num)]
  have hcds : (Setup.fastSetupState input).executionEnv.calldata.size < 2 ^ 256 := by
    rw [fastSetup_calldata input]
    exact hsize
  obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
    handled_of_handover input (Setup.fastSetupState input) (Setup.fastSetupMemory input)
      (Setup.limbs input) (Challenge.Modexp.baseSize input)
      (Challenge.Modexp.exponentSize input) (Challenge.Modexp.modulusSize input)
      (Setup.modulus input) (Setup.minvValue input)
      (fastSetup_code input) (fastSetup_fork input) (fastSetup_halt input)
      (fastSetup_notPrecompile input) (fastSetup_calldata input)
      (fastSetup_callStack input) hact hcds hn hn32 hpath.2.1.1 hpath.2.1.2.1 hpath.1
      (Setup.modulusSize_le_s32 input) rfl rfl rfl (Setup.fastSetup_modulus_eq input)
      hodd hradix hmpos hminvlt hminvA hxlt
      ⟨Setup.fastSetup_V_S32 input hpath, Setup.fastSetup_V_MINV input,
       Setup.fastSetup_V_ML input hpath, Setup.fastSetup_V_TL input hpath,
       Setup.fastSetup_V_EOFF input hpath⟩
      (Setup.fastSetup_modulus input hpath) (Setup.fastSetup_R1 input hpath)
      (fastSetup_zero_block input hpath 1024 (by omega) (by omega))
      (fastSetup_zero_block input hpath 2048 (by omega) (by omega))
      (fastSetup_zero_block input hpath 3072 (by omega) (by omega))
      (fastSetup_tblock_zero input hpath hn32)
  exact ⟨final, ⟨(Challenge.EvmProof.GasSteps.cast
    (Setup.gasSteps_fastSetup input hsize hpath) rfl (fastSetup_entry_eq input)).trans
    tr⟩, hdone, hres⟩

#print axioms gasSteps_handled

end Challenge.Modexp.Submission.Proofs.Fast.Exp

