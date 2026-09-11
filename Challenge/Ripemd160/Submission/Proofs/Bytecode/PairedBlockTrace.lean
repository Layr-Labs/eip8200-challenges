import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Site
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Semantics
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRoundSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SStartupPremises
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadBlockModel

set_option warningAsError true
set_option maxRecDepth 50000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PairedBlockModel PairedHelperBooleanTrace CachedCoreCommon

theorem terminal_eval (memory : ByteArray) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hready : NormalizedScheduleReady memory words) :
    PairedAllInlineCoreTrace.inline79Block.eval memory
      (PairedAllInlineCoreTrace.corePrefixChain.eval memory
        ⟨PairedLaneWordRound.packCrypto left right, 0⟩) =
      coreCryptoResult words left right := by
  rw [PairedAllInlineCoreTrace.corePrefixChain_eval,
    PairedAllInlineCoreTrace.inline79Block_eval]
  have h := PairedSynthCoreTrace.hoistedAlgorithmFold_crypto memory words 80
    (by decide) left right (algorithmMessage_of_normalized memory words hready)
  exact congrArg (fun lane => CoreFrame.mk lane (algorithmKey 4)) h

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

theorem startup_stack (memory : ByteArray) (rho : List UInt256) :
    PairedStartupTrace.resultStack memory rho =
      coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower]
        ⟨PairedLaneWordRound.packCrypto (PairedBlockMath.readLane memory)
          (PairedBlockMath.readLane memory), 0⟩ rho := by
  simp only [PairedStartupTrace.resultStack, PairedBlockMath.startup_packedHash]
  rfl

theorem scheduled_readLane (s : State) (i : Nat) :
    PairedBlockMath.readLane (scheduledState s i).memory = PairedBlockMath.readLane s.memory := by
  exact congrArg (fun h : Compression.EvmHashState =>
    (⟨Challenge.EvmProof.Word.toUInt32 h.h0, Challenge.EvmProof.Word.toUInt32 h.h1,
      Challenge.EvmProof.Word.toUInt32 h.h2, Challenge.EvmProof.Word.toUInt32 h.h3,
      Challenge.EvmProof.Word.toUInt32 h.h4⟩ : PairedLaneCryptoBridge.CryptoLane))
    (scheduled_hashWords s i)

theorem tail_stack (s : State) (input : ByteArray) (i : Nat) :
    coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower]
      (coreCryptoResult (blockWords input i) (PairedBlockMath.readLane s.memory)
        (PairedBlockMath.readLane s.memory))
      (UInt256.ofNat 451 :: driverRest input i) =
      PairedAllInlineTail.entryStack (resultFrame s input i)
        (UInt256.ofNat 451) (driverRest input i) := by
  rfl

theorem valid_return (s : State) (hcode : s.executionEnv.code = submissionBytecode) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 451).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 274 = 451 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 274 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 451 = true
  rw [hcode]
  exact h

def gasSteps_compress (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned (resultState s input i) input i) := by
  let q := scheduledState s i
  let rho := UInt256.ofNat 451 :: driverRest input i
  let lane := PairedBlockMath.readLane s.memory
  have qactive : 23 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have qcode : q.executionEnv.code = submissionBytecode := hcode
  have qfork : q.fork = .Osaka := hfork
  have qrun : q.halt = .Running := hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := hnp
  have hstack : rho.length ≤ 996 := by simp [rho, driverRest]
  have hcstack : (cache q.memory ++ rho).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  have gschedule' : GasSteps (DriverTrace.compressEntry s input i)
      {q with pc := UInt256.ofNat 713, stack := cache q.memory ++ rho} := by
    have gmerge := PadSites.gasSteps_merge q (cache q.memory ++ rho)
      (by simp only [List.length_append, cache_length]; omega) qrun qcode qfork qnp
    have hfit256 : s.executionEnv.calldata.size < 2^256 := by
      rw [ctx.calldata]
      exact PadBlockModel.calldata_lt_uint256 input hfit
    have hoff := PadBlockModel.blockOffsetWord_toNat input hfit i hi
    have gprefix : GasSteps (DriverTrace.compressEntry s input i)
        {q with pc := UInt256.ofNat 712, stack := cache q.memory ++ rho} := by
      by_cases hhit : input.size = DriverTrace.blockOffset i
      · have heq : s.executionEnv.calldata.size = (DriverTrace.blockOffsetWord i).toNat := by
          rw [ctx.calldata, hoff]
          exact hhit
        have ghit := PadSites.gasSteps_hit s (DriverTrace.messageOffsetWord i)
          (UInt256.ofNat 451) (DriverTrace.blockOffsetWord i) [Padding.paddedWord input]
          (by simp) hrun hfit256 heq hcode hfork hnp
        have gtouch := PadSites.gasSteps_prefix s (UInt256.ofNat 451) (messagePointer i)
          (driverRest input i) (by simp [driverRest]) hrun
          (messagePointer_bound input hfit i hi) (PadBlockModel.messagePointer_aligned i)
          hcode hfork hnp
        let a : State := {s with activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}
        have ga : GasSteps (DriverTrace.compressEntry s input i)
            {a with pc := UInt256.ofNat 402, stack := rho} := ghit.trans gtouch
        have gbody := PadSites.gasSteps_body a (UInt256.ofNat 451) (driverRest input i)
          (by simp [driverRest]) hrun qactive hfit256 hcode hfork hnp
        have hmem : PadOnlySchedule.resultMemory a.memory
            (UInt256.ofNat a.executionEnv.calldata.size) = q.memory :=
          PadBlockModel.scheduled_memory_calldata s input i h hfit hi ctx hhit
        have hcache : cache q.memory = [UInt256.ofNat 22, UInt256.ofNat 0,
            UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0] := by
          exact PadBlockModel.scheduled_cache22 s input i h hfit hi ctx hhit
        have gb : GasSteps {a with pc := UInt256.ofNat 402, stack := rho}
            {q with pc := UInt256.ofNat 447, stack := cache q.memory ++ rho} := by
          apply gbody.cast rfl
          rw [hmem, hcache]
          rfl
        have gjump := PadSites.gasSteps_jump q (cache q.memory ++ rho)
          (by simp only [List.length_append, cache_length]; omega) qrun qcode qfork qnp
        exact ga.trans (gb.trans gjump)
      · have hne : s.executionEnv.calldata.size ≠ (DriverTrace.blockOffsetWord i).toNat := by
          rw [ctx.calldata, hoff]
          exact hhit
        have gmiss := PadSites.gasSteps_miss s (DriverTrace.messageOffsetWord i)
          (UInt256.ofNat 451) (DriverTrace.blockOffsetWord i) [Padding.paddedWord input]
          (by simp) hrun hfit256 hne hcode hfork hnp
        have gold := PairedAllInlineBoundarySites.gasSteps_schedule s (UInt256.ofNat 451)
          (messagePointer i) (driverRest input i) (by simp [driverRest]) hrun
          (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp ctx.sentinel
        exact gmiss.trans gold
    exact gprefix.trans gmerge
  have hcanonical := SStartupPremises.scheduled_canonical s input i h ctx
  have gstartup := PairedAllInlineBoundarySites.gasSteps_startup q (cache q.memory ++ rho) hcstack qrun qactive
    hcanonical.1 hcanonical.2.1 hcanonical.2.2.1 hcanonical.2.2.2.1 hcanonical.2.2.2.2
    qcode qfork qnp
  let initial : CoreFrame := ⟨PairedLaneWordRound.packCrypto lane lane, 0⟩
  let before78 := Strip78Prefix.corePrefix77Chain.eval q.memory initial
  let terminal := PairedAllInlineCoreTrace.corePrefixChain.eval q.memory initial
  let dirty := Strip78Round.dirtyFrame q.memory before78
  have gcore := PairedAllInlineCoreSites.gasSteps_core_prefix q initial rho
    hstack qrun qactive qcode qfork qnp
  have hentry :
      {q with pc := UInt256.ofNat 766, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto lane lane, 0⟩ (cache q.memory ++ rho)} =
      {q with pc := UInt256.ofNat 766, stack := PairedStartupTrace.resultStack q.memory (cache q.memory ++ rho)} := by
    rw [startup_stack, scheduled_readLane]
  have hterminal : TerminalRound.canonicalFrame q.memory terminal.frame =
      resultFrame s input i := by
    rw [TerminalRound.canonicalFrame_eval]
    unfold TerminalRound.evaluatedTailFrame
    rw [terminal_eval q.memory (blockWords input i) lane lane
      (scheduled_ready s input i h hfit hi ctx)]
    rfl
  have hmemory : PairedTailTrace.resultMemory q.memory
      (TerminalRound.modifiedFrame q.memory terminal.frame) =
      PairedTailTrace.resultMemory q.memory (resultFrame s input i) := by
    rw [TerminalRound.resultMemory_modified_eq_canonical _ _ rfl rfl, hterminal]
  have hmemoryDirty : PairedTailTrace.resultMemory q.memory
      (TerminalRound.modifiedFrame q.memory dirty) =
      PairedTailTrace.resultMemory q.memory (resultFrame s input i) := by
    exact (Strip78Semantics.resultMemory_prefix_strip q.memory (blockWords input i) lane lane
      (scheduled_ready s input i h hfit hi ctx)).trans hmemory
  have gstrip := Strip78Site.gasSteps q before78 rho
    hstack qrun qactive qcode qfork qnp
  have gsuffix := TerminalRoundSite.gasSteps_suffix q dirty
    (UInt256.ofNat 451) (driverRest input i) hstack qrun qactive
    (valid_return q qcode) qcode qfork qnp
  rw [hmemoryDirty] at gsuffix
  have gsuffix' : GasSteps
      {q with pc := UInt256.ofNat 4559, stack := PairedAllInlineCoreTrace.inline79Entry dirty (cache q.memory ++ rho)}
      (DriverTrace.compressReturned (resultState s input i) input i) := gsuffix
  exact gschedule'.trans (gstartup.trans ((gcore.cast hentry rfl).trans (gstrip.trans gsuffix')))

#print axioms startup_stack
#print axioms scheduled_readLane
#print axioms tail_stack
#print axioms valid_return
#print axioms gasSteps_compress

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
