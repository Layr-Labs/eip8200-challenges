import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Site
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Semantics
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SelectedGarbageFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRoundSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SStartupPremises
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGarbageSchedule

set_option warningAsError true
set_option maxRecDepth 50000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PairedBlockModel PairedHelperBooleanTrace CachedCoreCommon

/-- The schedule the candidate actually leaves in memory: the exact words
plus the garbage the four dropped masks no longer clear. -/
theorem scheduled_ready_garbage (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    GarbageScheduleReady (scheduledState s i).memory (blockWords input i)
      (selectedGarbage s i) := by
  by_cases hclean : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · simp only [selectedGarbage, if_pos hclean]
    exact garbageScheduleReady_of_normalized _ _ (scheduled_ready s input i h hfit hi ctx hclean)
  · simp only [selectedGarbage, if_neg hclean]

    have hsplit (k : Nat) := PairedScheduleData.extractedWordG_eq_add s.memory (messagePointer i) k
    have hcell (k : Nat) (hk : k < 16) :
        (PairedScheduleData.extractedWordG s.memory (messagePointer i) k) =
          UInt256.ofNat ((blockWords input i k).toNat
            + PairedScheduleData.extractedGarbage s.memory (messagePointer i) k) := by
      apply Challenge.EvmProof.Word.word_ext
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, (hsplit k).1,
        extracted_words s input i h hfit hi ctx k hk]
      have hb : (blockWords input i k).toNat < 2 ^ 32 := (blockWords input i k).toNat_lt_size
      have hg := (hsplit k).2.2
      rw [Challenge.EvmProof.Word.ofUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨fun k hk => ⟨(hsplit k).2.1, (hsplit k).2.2⟩, fun k hk => ?_, fun k hk => ?_⟩
    · rw [scheduled_memory_miss s i hclean]
      change MachineState.readWord
        (PairedScheduleMemory.normalizedMemory s.memory
          (PairedScheduleData.extractedWordG s.memory (messagePointer i)))
          (PairedScheduleMemory.cell k) = _
      rw [PairedScheduleMemory.read_normalized_cell _ _ _ (by omega), if_neg (by omega)]
      exact hcell k hk
    · rw [scheduled_memory_miss s i hclean]
      change MachineState.readWord
        (PairedScheduleMemory.normalizedMemory s.memory
          (PairedScheduleData.extractedWordG s.memory (messagePointer i)))
          (PairedScheduleMemory.cell k + 16) = _
      rw [PairedScheduleMemory.read_normalized_upper_wide _ _
        (fun j _ => by
          have hb := PairedScheduleData.chunkG_lt
            (MachineState.readWord s.memory (messagePointer i + 32 * (j / 8))) (j % 8)
            (Nat.mod_lt _ (by decide))
          show (PairedScheduleData.extractedWordG s.memory (messagePointer i) j).toNat < 2 ^ 128
          simp only [PairedScheduleData.extractedWordG]
          omega) _ hk]
      rw [hcell k hk]

#print axioms scheduled_ready_garbage

/-- The garbage-tolerant tail: the whole core chain still evaluates to the
exact `coreCryptoResult`. -/
theorem terminal_eval_garbage (memory : ByteArray) (words : Nat → UInt32)
    (g : Nat → Nat) (left right : PairedLaneCryptoBridge.CryptoLane)
    (hready : GarbageScheduleReady memory words g) :
    PairedAllInlineCoreTrace.inline79Block.eval memory
      (PairedAllInlineCoreTrace.corePrefixChain.eval memory
        ⟨PairedLaneWordRound.packCrypto left right, 0⟩) =
      coreCryptoResult words left right := by
  rw [PairedAllInlineCoreTrace.corePrefixChain_eval,
    PairedAllInlineCoreTrace.inline79Block_eval]
  have hbound (k : Nat) (hk : k < 80) :
      g Crypto.Ripemd160.r[k]! % 2 ^ 32 = 0 ∧ g Crypto.Ripemd160.r[k]! < 2 ^ 96 ∧
        g Crypto.Ripemd160.rP[k]! / 2 ^ 32 < 2 ^ 64 := by
    have hb := PairedHelperBooleanTrace.algorithmIndex_bounds ⟨k, hk⟩
    have hlo := hready.1 Crypto.Ripemd160.r[k]! hb.1
    have hhi := hready.1 Crypto.Ripemd160.rP[k]! hb.2
    refine ⟨hlo.1, hlo.2, ?_⟩
    have : g Crypto.Ripemd160.rP[k]! < 2 ^ 96 := hhi.2
    omega
  have hfold := PairedSynthCoreTrace.hoistedAlgorithmFold_crypto_garbage memory words
    (fun k => g Crypto.Ripemd160.r[k]!)
    (fun k => g Crypto.Ripemd160.rP[k]! / 2 ^ 32) 80 (by decide) left right
    (fun k hk => ⟨(hbound k hk).1, (hbound k hk).2.1, (hbound k hk).2.2⟩)
    (fun k hk => PairedHelperBooleanTrace.algorithmMessage_of_garbage_add memory words g
      hready k hk)
  exact congrArg (fun lane => CoreFrame.mk lane (algorithmKey 4)) hfold

#print axioms terminal_eval_garbage

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
      (UInt256.ofNat 448 :: driverRest input i) =
      PairedAllInlineTail.entryStack (resultFrame s input i)
        (UInt256.ofNat 448) (driverRest input i) := by
  rfl

theorem valid_return (s : State) (hcode : s.executionEnv.code = submissionBytecode) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 448).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 274 = 448 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 274 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 448 = true
  rw [hcode]
  exact h

opaque gasSteps_prepare (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      {scheduledState s i with pc := UInt256.ofNat 702, stack := cache (scheduledState s i).memory ++ (UInt256.ofNat 448 :: driverRest input i)} := by
  let q := scheduledState s i
  let rho := UInt256.ofNat 448 :: driverRest input i
  have qactive : 23 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have qcode : q.executionEnv.code = submissionBytecode := hcode
  have qfork : q.fork = .Osaka := hfork
  have qrun : q.halt = .Running := hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := hnp
  have hstack : rho.length ≤ 996 := by simp [rho, driverRest]
  have hcstack : (cache q.memory ++ rho).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  have gschedule' : GasSteps (DriverTrace.compressEntry s input i)
      {q with pc := UInt256.ofNat 702, stack := cache q.memory ++ rho} := by
    have gmerge := PadSites.gasSteps_merge q (cache q.memory ++ rho)
      (by simp only [List.length_append, cache_length]; omega) qrun qcode qfork qnp
    have hfit256 : s.executionEnv.calldata.size < 2^256 := by
      rw [ctx.calldata]
      exact PadBlockModel.calldata_lt_uint256 input hfit
    have hoff := PadBlockModel.blockOffsetWord_toNat input hfit i hi
    have gprefix : GasSteps (DriverTrace.compressEntry s input i)
        {q with pc := UInt256.ofNat 701, stack := cache q.memory ++ rho} := by
      by_cases hhit : input.size = DriverTrace.blockOffset i
      · have heq : s.executionEnv.calldata.size = (DriverTrace.blockOffsetWord i).toNat := by
          rw [ctx.calldata, hoff]
          exact hhit
        have ghit := PadSites.gasSteps_hit s (DriverTrace.messageOffsetWord i)
          (UInt256.ofNat 448) (DriverTrace.blockOffsetWord i) [Padding.paddedWord input]
          (by simp) hrun hfit256 heq hcode hfork hnp
        have gtouch := PadSites.gasSteps_prefix s (UInt256.ofNat 448) (messagePointer i)
          (driverRest input i) (by simp [driverRest]) hrun
          (messagePointer_bound input hfit i hi) (PadBlockModel.messagePointer_aligned i)
          hcode hfork hnp
        let a : State := {s with activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}
        have ga : GasSteps (DriverTrace.compressEntry s input i)
            {a with pc := UInt256.ofNat 402, stack := rho} := ghit.trans gtouch
        have gbody := PadSites.gasSteps_body a (UInt256.ofNat 448) (driverRest input i)
          (by simp [driverRest]) hrun qactive hfit256 hcode hfork hnp
        have hmem : PadOnlySchedule.resultMemory a.memory
            (UInt256.ofNat a.executionEnv.calldata.size) = q.memory :=
          PadBlockModel.scheduled_memory_calldata s input i h hfit hi ctx hhit
        have hcache : cache q.memory = [UInt256.ofNat 22, UInt256.ofNat 0,
            UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0] := by
          exact PadBlockModel.scheduled_cache22 s input i h hfit hi ctx hhit
        have gb : GasSteps {a with pc := UInt256.ofNat 402, stack := rho}
            {q with pc := UInt256.ofNat 444, stack := cache q.memory ++ rho} := by
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
          (UInt256.ofNat 448) (DriverTrace.blockOffsetWord i) [Padding.paddedWord input]
          (by simp) hrun hfit256 hne hcode hfork hnp
        have gold := PairedAllInlineBoundarySites.gasSteps_schedule s (UInt256.ofNat 448)
          (messagePointer i) (driverRest input i) (by simp [driverRest]) hrun
          (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp ctx.sentinel
        have hdirty : s.executionEnv.calldata.size ≠ DriverTrace.blockOffset i := by
          rw [ctx.calldata]
          exact hhit
        have gold' : GasSteps
            {s with pc := UInt256.ofNat 475, stack := DriverTrace.messageOffsetWord i :: rho}
            {q with pc := UInt256.ofNat 701, stack := cache q.memory ++ rho} := by
          apply gold.cast rfl
          simp only [q, scheduledState, selectedWords, if_neg hdirty]
          all_goals rfl
        exact gmiss.trans gold'
    exact gprefix.trans gmerge
  exact gschedule'


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
  let rho := UInt256.ofNat 448 :: driverRest input i
  let lane := PairedBlockMath.readLane s.memory
  have qactive : 23 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have qcode : q.executionEnv.code = submissionBytecode := hcode
  have qfork : q.fork = .Osaka := hfork
  have qrun : q.halt = .Running := hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := hnp
  have hstack : rho.length ≤ 996 := by simp [rho, driverRest]
  have hcstack : (cache q.memory ++ rho).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  have gschedule' := gasSteps_prepare s input i h hfit hi ctx hcode hfork hrun hnp
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
      {q with pc := UInt256.ofNat 755, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto lane lane, 0⟩ (cache q.memory ++ rho)} =
      {q with pc := UInt256.ofNat 755, stack := PairedStartupTrace.resultStack q.memory (cache q.memory ++ rho)} := by
    rw [startup_stack, scheduled_readLane]
  have hterminal : TerminalRound.canonicalFrame q.memory terminal.frame =
      resultFrame s input i := by
    rw [TerminalRound.canonicalFrame_eval]
    unfold TerminalRound.evaluatedTailFrame
    rw [terminal_eval_garbage q.memory (blockWords input i) (selectedGarbage s i) lane lane
      (scheduled_ready_garbage s input i h hfit hi ctx)]
    rfl
  have hmemory : PairedTailTrace.resultMemory q.memory
      (TerminalRound.modifiedFrame q.memory terminal.frame) =
      PairedTailTrace.resultMemory q.memory (resultFrame s input i) := by
    rw [TerminalRound.resultMemory_modified_eq_canonical _ _ rfl rfl, hterminal]
  have hmemoryDirty : PairedTailTrace.resultMemory q.memory
      (TerminalRound.modifiedFrame q.memory dirty) =
      PairedTailTrace.resultMemory q.memory (resultFrame s input i) := by
    exact (Strip78Semantics.resultMemory_prefix_strip_garbage q.memory (blockWords input i) lane lane
      (selectedGarbage s i) (scheduled_ready_garbage s input i h hfit hi ctx)
      (selectedGarbage_thirteen s i) (selectedGarbage_eleven s i)).trans hmemory
  have gstrip := Strip78Site.gasSteps q before78 rho
    hstack qrun qactive qcode qfork qnp
  have gsuffix := TerminalRoundSite.gasSteps_suffix q dirty
    (UInt256.ofNat 448) (driverRest input i) hstack qrun qactive
    (valid_return q qcode) qcode qfork qnp
  have gsuffix' : GasSteps
      {q with pc := UInt256.ofNat 4561, stack := PairedAllInlineCoreTrace.inline79Entry dirty (cache q.memory ++ rho)}
      (DriverTrace.compressReturned (resultState s input i) input i) := by
    apply gsuffix.cast rfl
    rw [hmemoryDirty]
    rfl
  exact gschedule'.trans (gstartup.trans ((gcore.cast hentry rfl).trans (gstrip.trans gsuffix')))

#print axioms startup_stack
#print axioms scheduled_readLane
#print axioms tail_stack
#print axioms valid_return
#print axioms gasSteps_compress

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
