import Challenge.Modexp.Submission.Proofs.Fast.RootE3Correct
import Challenge.Modexp.Submission.Proofs.Fast.RootE3Bindings
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace5
import Challenge.Modexp.Submission.Proofs.Fast.ExpSubs
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMain
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUBlocks

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Fast-path certificate with the shift-reduce base conversion

After `Fast.Setup` and the `R1B` guard, execution reaches the dispatcher at
pc 4022.  When the base is exactly `n` words wide and the modulus has its top
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
    (UInt256.ofNat 2474).toNat = true :=
  Exp.jumpD 2474 (by decide) jumpDest4608

/-! ## Facts at `BDONE` on the hit path -/



/-- The words the whole hit path leaves alone: everything outside `ACC`, `BASE`,
`NEG`, the estimator words, `SUBB` and the `t` area. -/
theorem hitFinal_readWord_disjoint (mem input : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hdisj : (addr + 32 ≤ 256 ∨ 256 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ NEG ∨ NEG + 32 * n ≤ addr) ∧
      (addr + 32 ≤ PRE_L ∨ PRE_DINV + 66 ≤ addr) ∧
      (addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr)) :
    MachineState.readWord (hitFinalMem mem input n mm) addr = MachineState.readWord mem addr := by
  unfold hitFinalMem
  rw [stepMems_readWord_disjoint _ n mm addr hn ⟨hdisj.2.1, hdisj.2.2.2.2.1, hdisj.2.2.2.2.2⟩ n]
  exact m2_readWord_disjoint mem input n addr hn hn32 hdisj

theorem hitFinal_preserves (mem input : ByteArray) (n mm ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hdisj : (ptr + 32 * cnt ≤ 256 ∨ 256 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ NEG ∨ NEG + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ PRE_L ∨ PRE_DINV + 66 ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (hitFinalMem mem input n mm) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact hitFinal_readWord_disjoint mem input n mm _ hn hn32 (by omega)

/-- `ACC` still holds the raw base at `BDONE`. -/
theorem hitFinal_acc (mem input : ByteArray) (n mm : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem) :
    Model.FastRepresents (hitFinalMem mem input n mm) 256 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) :=
  RootE3Phase.represents_acc_after_steps _ n mm _ n (by omega) hn32
    (RootE3Phase.m2_acc_value mem input n mm hn hn32 hm hodd hmod htop)

/-- The retained `TS` holds the Montgomery residue of the base at `BDONE`. -/
theorem hitFinal_base (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hodd : mm % 2 = 1)
    (hmm : mm < Limbs.radix ^ n) (htop : R1.TopBitSet mem)
    (hmod : Model.FastRepresents mem 0 n mm) :
    Model.FastRepresents (hitFinalMem mem input n mm) 2112 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm * Limbs.radix ^ n % mm) := by
  have htop' : Limbs.radix ^ n < 2 * mm := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have hmod1 : Model.FastRepresents (m1Of mem input n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact m1_readWord_disjoint mem input n _ (by omega) hn32
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩
  have hmod2 : Model.FastRepresents (m2Of mem input n) 0 n mm := by
    unfold m2Of preMem
    refine ShiftCacheModel.represents_cache _ n 0 n _ (Or.inl (by omega)) ?_
    exact fastRepresents_preMemOf _ _ 0 n mm (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 0 n mm (Or.inl (by unfold NEG; omega)) hmod1 n le_rfl)
  have hneg2 : Model.FastRepresents (m2Of mem input n) NEG n (Limbs.radix ^ n - mm) := by
    unfold m2Of preMem
    refine ShiftCacheModel.represents_cache _ n NEG n _ (Or.inl (by unfold NEG; omega)) ?_
    exact fastRepresents_preMemOf _ _ NEG n _ (Or.inl (by unfold NEG PRE_L; omega))
      (neg_represents (m1Of mem input n) n mm (by omega) (by omega) hmpos hmod1)
  have hbase2 : Model.FastRepresents (m2Of mem input n) 2112 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
    unfold m2Of preMem
    refine ShiftCacheModel.represents_cache _ n 2112 n _ (Or.inr (by omega)) ?_
    exact fastRepresents_preMemOf _ _ 2112 n _ (Or.inr (by unfold PRE_DINV; omega))
      (fastRepresents_negStep _ n 2112 n _ (Or.inr (by unfold NEG; omega))
        (m1_base mem input n mm hn hn32 hmpos hodd hmod htop) n le_rfl)
  exact stepMems_represents (m2Of mem input n) n mm _ hn hn32 hmpos hmm htop' hmod2 hneg2
    hbase2 (Nat.mod_lt _ hmpos)
    (PreOK_cacheMem _ n (PreOK_preMem _)) n

private theorem readWord_setupMem_operand (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 256)
    (hlo : 256 ≤ target) (hhi : target + 32 ≤ 2688) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_256 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  -- `setupMem` does not store the R1 seed, so this read-through peels one
  -- `mstoreAt` fewer before the two `writeBytes`.
  rw [Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

private theorem fastSetup_R1_zero_compact (input : ByteArray) (hpath : Setup.FastPath input) :
    Model.FastRepresents (Setup.fastSetupMemory input) 1024 (Setup.limbs input) 0 := by
  have hn := Setup.fastSetup_limbs_le_8 input hpath
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_operand input (Setup.lowLimb input) (1024 + 32 * j)
      hpath.2.1.2.2 (by omega) (by omega),
    Exp.toNat_ofNat_self (by norm_num)]

/-- The seed store: writing the word 1 at `R1 = 0x0400` over a zeroed block represents
`radix^(n-1)`, which is the Montgomery-form conversion's precondition.  In the previous layout this
fact came from the store the setup path made (`Setup.fastSetup_R1`); the store now happens in the
recogniser-miss arm, so the fact is established here. -/
theorem fastRepresents_seed (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hz : Model.FastRepresents mem 1024 n 0) :
    Model.FastRepresents (Exp.storeWord mem 1024 (UInt256.ofNat 1)) 1024 n
      (Limbs.radix ^ (n - 1)) := by
  have hzero := (Model.fastRepresents_zero_iff mem 1024 n).1 hz
  have hrpos : 0 < Limbs.radix := Limbs.radix_pos
  have hsw : Exp.storeWord mem 1024 (UInt256.ofNat 1) = Setup.mstoreAt mem 1024 1 := by
    unfold Exp.storeWord Setup.mstoreAt
    rw [Exp.toNat_ofNat_self (show (1 : Nat) < 2 ^ 256 by norm_num)]
  apply Model.fastRepresents_of_limbs
  · exact Nat.pow_lt_pow_right Limbs.radix_gt_one (by omega)
  · intro k hk
    by_cases hkt : k = n - 1
    · subst hkt
      rw [show n - 1 - (n - 1) = 0 from by omega, Nat.mul_zero, Nat.add_zero, hsw,
        Setup.readWord_mstoreAt_self _ _ _ (by norm_num),
        Exp.toNat_ofNat_self (show (1 : Nat) < 2 ^ 256 by norm_num),
        Nat.div_self (Nat.pow_pos hrpos), Nat.mod_eq_of_lt Limbs.radix_gt_one]
    · have hjpos : 1 ≤ n - 1 - k := by omega
      have hz0 : Limbs.radix ^ (n - 1 - k) % Limbs.radix = 0 := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hjpos
        rw [hj, pow_add, pow_one, Nat.mul_mod_right]
      rw [Exp.storeWord_readWord_disjoint mem 1024 (1024 + 32 * (n - 1 - k))
          (UInt256.ofNat 1) (Or.inr (by omega)),
        hzero (n - 1 - k) (by omega),
        Nat.pow_div (show k ≤ n - 1 by omega) hrpos, hz0]

/-! ## The dispatcher case split -/

/-- Everything after `R1B` returns to the dispatcher. -/
theorem handled_of_dispatch (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 89 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
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
    (hr1z : Model.FastRepresents mem 1024 n 0)
    (hacc0 : Model.FastRepresents mem 256 n 0)
    (hbase0 : Model.FastRepresents mem 512 n 0)
    (hone0 : Model.FastRepresents mem 768 n 0)
    (htz : Model.FastRepresents mem 2112 n 0)
    -- The two conditions the rewritten dispatcher enforces. They are what makes the narrowed
    -- kernel composition applicable, so they travel with the dispatch rather than being
    -- rediscovered inside it.
    (hfast : n = 4 ∨ n = 8) (hminv1 : minv ≠ 1)
    -- S1.  Both are needed only on the diverted miss arm, and both are free where
    -- they are produced.  `bigC_correct` wants `ValidInput`, whose `size < 2 ^ 64`
    -- component `handled_of_dispatch` cannot derive (`hcds` only gives `< 2 ^ 256`);
    -- `gasSteps_handled` has it as a hypothesis.  And it wants an UPPER bound on
    -- `activeWords`, where every bound in this tree is a lower one -- but the carrier
    -- is `Setup.fastSetupState input`, whose `activeWords` is proved to be exactly
    -- 89, and every named fast-path state is a record update of it touching only
    -- `pc`/`stack`/`memory`, so the bound crosses definitionally and 89 <= 289 has
    -- 200 words of slack.
    (hvalid : Challenge.Modexp.ValidInput input)
    (hactLe : s.activeWords.toNat ≤ 289) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (dispState s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hact296 : 88 ≤ s.activeWords.toNat :=
    Nat.le_trans (show 88 ≤ 89 by norm_num) hact
  have e : Env s := ⟨hcode, hfork, hrun, hnp, hact⟩
  let sub := Exp.subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
    hminvlt hminvA hfast hminv1
  have hspec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv := by
    dsimp only [sub]
    exact Exp.specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32
      hmpos hminvlt hminvA hodd hfast hminv1
  have hbword : bsize < 2 ^ 256 := lt_of_le_of_lt hb (by norm_num)
  have hmmlt : mm < Limbs.radix ^ n := Model.fastRepresents_lt hmod0
  -- The setup path reaches the dispatcher WITHOUT converting, so the dispatcher's
  -- case split is on the unconverted memory and each arm establishes `R1 = 0x0400` itself --
  -- the hit arm from `NEG` through the shift loop's own `MCOPY` (sound because that arm
  -- carries `TopBitSet`), the miss arm by making the conversion call the setup path used to
  -- make.  In the previous layout both arms inherited `R1` from one call before the split.
  by_cases hmatch : FullBase.Matches mem n bsize
  · exact RootE3Correct.handled_of_bound_shift_hit input s mem n bsize esize msize mm minv
      sub hspec hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32
      hbsize hesize hmsz hmm hodd hradix hmpos hframe0 hmod0 hone0 hmatch hfast
      hvalid hactLe
      (RootE3Bindings.build s mem input n bsize esize msize minv hn hn32 hb he e hdata hframe0 hmatch
        hfast)
  · -- **S1: the diverted miss.**  The dispatcher's `PUSH2` operand no longer names
    -- the `r0` seeding block, so this whole class leaves the fast path at the bail
    -- trampoline and enters `modexpBig` at pc 238.  `bigC_correct` re-reads the
    -- header from calldata and is universal in the incoming memory and stack, so
    -- the frame the fast path built is simply discarded; nothing about it has to be
    -- carried across.
    --
    -- The `r0 -> RR-leading -> FullBase -> RrLeadingTail` subtree that used to
    -- discharge this arm is dead from here.  It is retired by track S2, not by this
    -- edit: deleting it before the bail exists would destroy the evidence that it
    -- is dead.
    have hbail := gasSteps_missPath s mem n bsize esize msize hn32 e hbword hmatch
    -- `bigCState` is a record update of `s` touching only `pc`, `stack` and
    -- `memory`, so every environment field is `s`'s DEFINITIONALLY.  Naming that
    -- once, as a hypothesis carrying the bail state's spelling, is what lets `rw`
    -- fire below: `hdata` is stated about `s`, and `rw` is syntactic, not up to
    -- defeq.  `▸` would have to guess the motive here; this does not.
    have hcd : (bigCState s mem n bsize esize msize).executionEnv.calldata = input := hdata
    have hpos : 0 < Challenge.Modexp.modulusSize input := by omega
    obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
      BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
        BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks
        (bigCState s mem n bsize esize msize)
        (bindingEnv e) rfl
        (by simp [bigCState, frameState, Exp.outer])
        (show (bigCState s mem n bsize esize msize).activeWords.toNat ≤ 289 from hactLe)
        (show (bigCState s mem n bsize esize msize).callStack = [] from hstack)
        (by rw [hcd]; exact hvalid)
        (by rw [hcd]; exact hpos)
    refine ⟨final, ⟨hbail.trans tail⟩, hdone, ?_⟩
    rw [hres, hcd]

/-- **Fast-path certificate.** Every `ValidInput` on the fast path runs from
the retargeted entry to the MODEXP result. -/
theorem gasSteps_handled (input : ByteArray)
    (hvalid : Challenge.Modexp.ValidInput input)
    (hpath : Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Main.trampolineState input 599) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hsize : input.size < 2 ^ 256 := lt_trans hvalid.1 (by norm_num)
  have hn : 2 ≤ Setup.limbs input := Setup.limbs_ge_two input hpath.1
  have hn32 : Setup.limbs input ≤ 8 := Setup.fastSetup_limbs_le_8 input hpath
  have hodd : Setup.modulus input % 2 = 1 := Setup.fastPath_odd input hpath
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
  have hact : 89 ≤ (Setup.fastSetupState input).activeWords.toNat := by
    rw [Setup.fastSetup_activeWords input hpath, Exp.toNat_ofNat_self (by norm_num)]
  have hcds : (Setup.fastSetupState input).executionEnv.calldata.size < 2 ^ 256 := by
    rw [Exp.fastSetup_calldata input]
    exact hsize
  -- S1.  The upper bound the bail needs, from the same lemma as the lower one.
  have hactLe : (Setup.fastSetupState input).activeWords.toNat ≤ 289 := by
    rw [Setup.fastSetup_activeWords input hpath, Exp.toNat_ofNat_self (by norm_num)]
    norm_num
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
      (Setup.fastSetup_modulus input hpath) (fastSetup_R1_zero_compact input hpath)
      (Exp.fastSetup_zero_block input hpath 256 (by omega) (by omega))
      (Exp.fastSetup_zero_block input hpath 512 (by omega) (by omega))
      (Exp.fastSetup_zero_block input hpath 768 (by omega) (by omega))
      (Exp.fastSetup_tblock_zero input hpath hn32)
      -- the two dispatcher conditions, discharged from the strengthened fast path
      (Setup.limbs_four_or_eight input hpath.1 hpath.2.1.2.2 (Setup.fastPath_width input hpath))
      (Setup.minv_ne_one_of_entry input (Setup.minvValue input) hpath.1
        (Setup.fastPath_nprime input hpath) hminvA)
      hvalid hactLe
  exact ⟨final, ⟨(Challenge.EvmProof.GasSteps.cast
    (Setup.gasSteps_fastSetup input hsize hpath) rfl (Exp.fastSetup_entry_eq input)).trans
    tr⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.Shift
