import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTrace
import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTail
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace5

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Fast-path certificate with the shift-reduce base conversion

After `Fast.Setup` and the `R1B` guard, execution reaches the dispatcher at
pc 3841.  When the base is exactly `n` words wide and the modulus has its top
bit set, the shift-reduce routine converts the base and rejoins the exponent
phase at `BDONE`; otherwise the old `r0` block runs the unchanged RR-leading
chain.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

theorem jumpD4643 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 3799).toNat = true :=
  Exp.jumpD 3799 (by decide) jumpDest4643

/-! ## Facts at `BDONE` on the hit path -/

theorem hitMem_acc (mem input : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    Model.FastRepresents (hitMem mem input n) 1024 n
      (Precompile.bytesToNatPadded input 96 (32 * n)) := by
  unfold hitMem Exp.storeWord
  refine Model.fastRepresents_writeWord_disjoint _ 8224 1024 n _ _ (Or.inr (by omega)) ?_
  refine Model.fastRepresents_writeBytes_disjoint _ _ 8256 1024 n _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega) ?_
  exact FullBase.copyBaseMem_represents mem input n

/-- The words the whole hit path leaves alone: everything outside `ACC`, `BASE`,
`NEG`, the estimator words, `SUBB` and the `t` area. -/
theorem hitFinal_readWord_disjoint (mem input : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdisj : (addr + 32 ≤ 1024 ∨ 1024 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ NEG ∨ NEG + 32 * n ≤ addr) ∧
      (addr + 32 ≤ PRE_L ∨ PRE_DINV + 32 ≤ addr) ∧
      (addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr)) :
    MachineState.readWord (hitFinalMem mem input n mm) addr = MachineState.readWord mem addr := by
  unfold hitFinalMem
  rw [stepMems_readWord_disjoint _ n mm addr hn ⟨hdisj.2.1, hdisj.2.2.2.2.1, hdisj.2.2.2.2.2⟩ n]
  exact m2_readWord_disjoint mem input n addr hn hn32 hdisj

theorem hitFinal_preserves (mem input : ByteArray) (n mm ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdisj : (ptr + 32 * cnt ≤ 1024 ∨ 1024 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 2048 ∨ 2048 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ NEG ∨ NEG + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ PRE_L ∨ PRE_DINV + 32 ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (hitFinalMem mem input n mm) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact hitFinal_readWord_disjoint mem input n mm _ hn hn32 (by omega)

/-- `ACC` still holds the raw base at `BDONE`. -/
theorem hitFinal_acc (mem input : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    Model.FastRepresents (hitFinalMem mem input n mm) 1024 n
      (Precompile.bytesToNatPadded input 96 (32 * n)) := by
  have h1 : Model.FastRepresents (m1Of mem input n) 1024 n
      (Precompile.bytesToNatPadded input 96 (32 * n)) := by
    unfold m1Of Csub.csResultMemory
    refine Csub.fastRepresents_mcopy_disjoint _ _ 2048 (32 * n) 1024 n _ (Or.inr (by omega)) ?_
    exact Csub.fastRepresents_csStep _ n 1024 n _ (by omega) (Or.inl (by omega))
      (hitMem_acc mem input n hn32) n le_rfl
  have h2 : Model.FastRepresents (m2Of mem input n) 1024 n
      (Precompile.bytesToNatPadded input 96 (32 * n)) := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ 1024 n _ (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 1024 n _ (Or.inl (by unfold NEG; omega)) h1 n le_rfl)
  unfold hitFinalMem
  refine (Model.fastRepresents_congr ?_ _).2 h2
  intro i hi
  exact stepMems_readWord_disjoint _ n mm _ hn
    ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩ n

/-- `BASE` holds the Montgomery residue of the base at `BDONE`. -/
theorem hitFinal_base (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hodd : mm % 2 = 1)
    (hmm : mm < Limbs.radix ^ n) (htop : R1.TopBitSet mem)
    (hmod : Model.FastRepresents mem 0 n mm) :
    Model.FastRepresents (hitFinalMem mem input n mm) 2048 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm * Limbs.radix ^ n % mm) := by
  have htop' : Limbs.radix ^ n < 2 * mm := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have hmod1 : Model.FastRepresents (m1Of mem input n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact m1_readWord_disjoint mem input n _ (by omega) hn32
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩
  have hmod2 : Model.FastRepresents (m2Of mem input n) 0 n mm := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ 0 n mm (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 0 n mm (Or.inl (by unfold NEG; omega)) hmod1 n le_rfl)
  have hneg2 : Model.FastRepresents (m2Of mem input n) NEG n (Limbs.radix ^ n - mm) := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ NEG n _ (Or.inl (by unfold NEG PRE_L; omega))
      (neg_represents (m1Of mem input n) n mm (by omega) hn32 hmpos hmod1)
  have hbase2 : Model.FastRepresents (m2Of mem input n) 2048 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ 2048 n _ (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 2048 n _ (Or.inl (by unfold NEG; omega))
        (m1_base mem input n mm hn hn32 hmpos hodd hmod htop) n le_rfl)
  exact stepMems_represents (m2Of mem input n) n mm _ hn hn32 hmpos hmm htop' hmod2 hneg2
    hbase2 (Nat.mod_lt _ hmpos) n

/-! ## The dispatcher case split -/

/-- Everything after `R1B` returns to the dispatcher. -/
theorem handled_of_dispatch (input : ByteArray) (s : State) (mem : ByteArray)
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
    (hframe0 : Exp.Frame mem n bsize minv)
    (hmod0 : Model.FastRepresents mem 0 n mm)
    (hr10 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hacc0 : Model.FastRepresents mem 1024 n 0)
    (hbase0 : Model.FastRepresents mem 2048 n 0)
    (hone0 : Model.FastRepresents mem 3072 n 0)
    (htz : Model.FastRepresents mem 8256 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Exp.r1Call s mem 4096 (UInt256.ofNat 3799) n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hact296 : 296 ≤ s.activeWords.toNat :=
    Nat.le_trans (show 296 ≤ 298 by norm_num) hact
  have e : Env s := ⟨hcode, hfork, hrun, hnp, hact⟩
  let sub := Exp.subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
    hminvlt hminvA
  have hspec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv := by
    dsimp only [sub]
    exact Exp.specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32
      hmpos hminvlt hminvA hodd
  have hbword : bsize < 2 ^ 256 := lt_of_le_of_lt hb (by norm_num)
  -- the R1B call
  set mem1 := Exp.r1Mem n 4096 mem with hmem1
  have hr1 : Challenge.EvmProof.GasSteps
      (Exp.r1Call s mem 4096 (UInt256.ofNat 3799) n bsize esize msize)
      (dispState s mem1 n bsize esize msize) :=
    Exp.gasSteps_r1Block s esize msize hcode hfork hrun hnp hact296 hn hn32
      (UInt256.ofNat 3799) mem jumpD4643 hframe0
  have hframe1 : Exp.Frame mem1 n bsize minv := Exp.r1Mem_frame hn hn32 hframe0
  have hmod1 : Model.FastRepresents mem1 0 n mm :=
    Exp.r1Mem_modulus hn hn32 hmpos mem hmod0 hr10 hxlt
  have hr1v : Model.FastRepresents mem1 4096 n (Limbs.radix ^ n % mm) :=
    Exp.r1Mem_represents hn hn32 hmpos hodd mem hmod0 hr10 hxlt htz
  have hacc1 : Model.FastRepresents mem1 1024 n 0 :=
    Exp.r1Mem_preserves hn hn32 (by omega) (by omega) mem hacc0
  have hbase1 : Model.FastRepresents mem1 2048 n 0 :=
    Exp.r1Mem_preserves hn hn32 (by omega) (by omega) mem hbase0
  have hone1 : Model.FastRepresents mem1 3072 n 0 :=
    Exp.r1Mem_preserves hn hn32 (by omega) (by omega) mem hone0
  have hmmlt : mm < Limbs.radix ^ n := Model.fastRepresents_lt hmod0
  by_cases hmatch : FullBase.Matches mem1 n bsize
  · -- the shift-reduce hit
    have hbEq : bsize = 32 * n := hmatch.1
    set final := hitFinalMem mem1 input n mm with hfinal
    have htrace := gasSteps_hitPath s mem1 input n bsize esize msize mm minv hn hn32 e hdata
      hbword hmatch hmpos hodd hmmlt hframe1 hmod1
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    let baseM := base % mm * Limbs.radix ^ n % mm
    have hframeF : Exp.Frame final n bsize minv :=
      (stepInv_stepMems (by omega) hn32
        (m2_stepInv mem1 input n bsize mm minv hn hn32 hmpos hframe1 hmod1) n).frame
    have hmodF : Model.FastRepresents final 0 n mm :=
      hitFinal_preserves mem1 input n mm 0 n mm (by omega) hn32
        ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by unfold NEG; omega),
          Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩ hmod1
    have hbaseF : Model.FastRepresents final 2048 n baseM :=
      hitFinal_base mem1 input n mm hn hn32 hmpos hodd hmmlt hmatch.2 hmod1
    have honeF : Model.FastRepresents final 3072 n 0 :=
      hitFinal_preserves mem1 input n mm 3072 n 0 (by omega) hn32
        ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by unfold NEG; omega),
          Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩ hone1
    have hr1F : Model.FastRepresents final 4096 n (Limbs.radix ^ n % mm) :=
      hitFinal_preserves mem1 input n mm 4096 n _ (by omega) hn32
        ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by unfold NEG; omega),
          Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩ hr1v
    have haccF : Model.FastRepresents final 1024 n base := hitFinal_acc mem1 input n mm (by omega) hn32
    have hEb : Exp.EbInv (Exp.mcopyMem final 1024 4096 (32 * n)) n mm baseM
        (Exp.expAcc mm (Limbs.radix ^ n) baseM (Exp.expBits input bsize) 0) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 0 n mm (by omega) hmodF
      · exact Csub.fastRepresents_mcopy _ 4096 1024 n (Limbs.radix ^ n % mm) (by omega) hr1F
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 2048 n baseM
          (by omega) hbaseF
      · exact ⟨0, Limbs.radix_pos,
          Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 3072 n 0 (by omega) honeF⟩
    have hbaseForm : baseM ≡
        Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n [MOD mm] := by
      dsimp only [baseM, base]
      rw [hbEq]
      exact (Nat.mod_modEq
          (Precompile.bytesToNatPadded input 96 (32 * n) % mm * Limbs.radix ^ n) mm).trans
        (Nat.ModEq.mul_right (Limbs.radix ^ n)
          (Nat.mod_modEq (Precompile.bytesToNatPadded input 96 (32 * n)) mm))
    have hrawForm : base ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm] := by
      simp only [base, hbEq]
      exact Nat.ModEq.refl _
    obtain ⟨fin, ⟨tr⟩, hdone, hres⟩ :=
      FixedDirectCorrect.handled_of_bDoneConcrete input s final
        n bsize esize msize mm minv baseM sub hspec
        hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize hesize
        hmsz hmm hodd hradix (Nat.mod_lt _ hmpos) hbaseForm hframeF hmodF
        hbaseF ⟨0, Limbs.radix_pos, honeF⟩ hEb ⟨base, haccF, hrawForm⟩
    exact ⟨fin, ⟨(hr1.trans htrace).trans tr⟩, hdone, hres⟩
  · -- the miss: the unchanged RR-leading chain from `r0`
    have hmiss := gasSteps_missPath s mem1 n bsize esize msize hn32 e hbword hmatch
    let directMem := Exp.setupToDirectMem (Exp.r1Mem n) (Exp.ccbMem n sub.mpMem sub.amMem) n mem
    have hf2 : Exp.Frame (Exp.mcopyMem mem1 5120 4096 (32 * n)) n bsize minv :=
      Exp.frame_mcopyMem (by omega) hframe1
    have hcc := Exp.setupToCC_facts n mm hn hn32 hmpos hodd mem hmod0 hr10 hxlt htz
    have hr0 : Challenge.EvmProof.GasSteps (Exp.r0State s mem1 n bsize esize msize)
        (entryState s directMem n bsize esize msize) :=
      (Exp.gasSteps_r0 s mem1 n bsize esize msize hn hn32 hact hframe1.s32 hcode hfork hrun
        hnp).trans
      (Exp.gasSteps_ccbFull s sub hspec esize msize hmpos hn hn32 5120 (by omega) (by omega)
        (UInt256.ofNat 3314) (Exp.mcopyMem mem1 5120 4096 (32 * n)) (Limbs.radix ^ n % mm)
        Exp.jumpD3571 hf2 hcc.1 hcc.2 (Nat.mod_lt _ hmpos) hact296 hcode hfork hrun hnp)
    have hframeDirect : Exp.Frame directMem n bsize minv := by
      dsimp only [directMem]
      exact Exp.setupToDirect_frame sub hn hn32 hframe0
    have hdirect := Exp.setupToDirect_facts n mm sub hspec hn hn32 hmpos hodd mem hframe0
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
      exact Exp.setupToDirect_preserves sub hspec 1024 0 hn hn32 (by omega) (by omega) mem
        hacc0
    have hbaseDirect : Model.FastRepresents directMem 2048 n 0 := by
      dsimp only [directMem]
      exact Exp.setupToDirect_preserves sub hspec 2048 0 hn hn32 (by omega) (by omega) mem
        hbase0
    have honeDirect : Model.FastRepresents directMem 3072 n 0 := by
      dsimp only [directMem]
      exact Exp.setupToDirect_preserves sub hspec 3072 0 hn hn32 (by omega) (by omega) mem
        hone0
    have hhelper :=
      Bytecode.RrLeadingTrace.gasSteps_helper s directMem n bsize esize msize hn hn32
        hact hframeDirect.s32 hcode hfork hrun hnp
    obtain ⟨hexit, hframeCopy, hinvCopy, haccCopy, hbaseCopy, honeCopy, _⟩ :=
      RrLeadingExpBridge.direct_rejoin_facts s directMem n bsize esize msize mm
        (Limbs.radix ^ n) minv hn hn32 hact hframeDirect hmodDirect hr1Direct hccDirect
        haccDirect hbaseDirect honeDirect
    obtain ⟨fin, ⟨trTail⟩, hdone, hres⟩ :=
      RrLeadingTail.handled_of_directRR input s (copiedMemory directMem n)
        n bsize esize msize mm minv sub hspec hcode hfork hrun hnp hdata hstack hact
        hn hn32 hb he hmz hm32 hbsize hesize hmsz hmm hodd hradix hframeCopy hinvCopy
        haccCopy hbaseCopy honeCopy
    have hhelper' : Challenge.EvmProof.GasSteps
        (entryState s directMem n bsize esize msize)
        (Exp.rrHead s (copiedMemory directMem n) n bsize esize msize
          (RrLeadingLogic.directCounter n)) :=
      Challenge.EvmProof.GasSteps.cast hhelper rfl hexit
    exact ⟨fin, ⟨(((hr1.trans hmiss).trans hr0).trans hhelper').trans trTail⟩, hdone, hres⟩

/-- **Fast-path certificate.** Every `ValidInput` on the fast path runs from
the retargeted entry to the MODEXP result. -/
theorem gasSteps_handled (input : ByteArray)
    (hvalid : Challenge.Modexp.ValidInput input)
    (hpath : Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Main.trampolineState input 1307) final) ∧
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
    rw [Setup.fastSetup_activeWords input hpath, Exp.toNat_ofNat_self (by norm_num)]
  have hcds : (Setup.fastSetupState input).executionEnv.calldata.size < 2 ^ 256 := by
    rw [Exp.fastSetup_calldata input]
    exact hsize
  obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
    handled_of_dispatch input (Setup.fastSetupState input) (Setup.fastSetupMemory input)
      (Setup.limbs input) (Challenge.Modexp.baseSize input)
      (Challenge.Modexp.exponentSize input) (Challenge.Modexp.modulusSize input)
      (Setup.modulus input) (Setup.minvValue input)
      (Exp.fastSetup_code input) (Exp.fastSetup_fork input) (Exp.fastSetup_halt input)
      (Exp.fastSetup_notPrecompile input) (Exp.fastSetup_calldata input)
      (Exp.fastSetup_callStack input) hact hcds hn hn32 hpath.2.1.1 hpath.2.1.2.1 hpath.1
      (Setup.modulusSize_le_s32 input) rfl rfl rfl (Setup.fastSetup_modulus_eq input)
      hodd hradix hmpos hminvlt hminvA hxlt
      ⟨Setup.fastSetup_V_S32 input hpath, Setup.fastSetup_V_MINV input,
       Setup.fastSetup_V_ML input hpath, Setup.fastSetup_V_TL input hpath,
       Setup.fastSetup_V_EOFF input hpath⟩
      (Setup.fastSetup_modulus input hpath) (Setup.fastSetup_R1 input hpath)
      (Exp.fastSetup_zero_block input hpath 1024 (by omega) (by omega))
      (Exp.fastSetup_zero_block input hpath 2048 (by omega) (by omega))
      (Exp.fastSetup_zero_block input hpath 3072 (by omega) (by omega))
      (Exp.fastSetup_tblock_zero input hpath hn32)
  exact ⟨final, ⟨(Challenge.EvmProof.GasSteps.cast
    (Setup.gasSteps_fastSetup input hsize hpath) rfl (Exp.fastSetup_entry_eq input)).trans
    tr⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.Shift
