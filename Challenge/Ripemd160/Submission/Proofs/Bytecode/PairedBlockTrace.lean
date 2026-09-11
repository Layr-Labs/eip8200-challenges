import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRoundSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SStartupPremises

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
      (UInt256.ofNat 587 :: driverRest input i) =
      PairedAllInlineTail.entryStack (resultFrame s input i)
        (UInt256.ofNat 587) (driverRest input i) := by
  rfl

theorem valid_return (s : State) (hcode : s.executionEnv.code = submissionBytecode) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 587).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 355 = 587 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 355 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 587 = true
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
  let rho := UInt256.ofNat 587 :: driverRest input i
  let lane := PairedBlockMath.readLane s.memory
  have qactive : 23 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have qcode : q.executionEnv.code = submissionBytecode := hcode
  have qfork : q.fork = .Osaka := hfork
  have qrun : q.halt = .Running := hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := hnp
  have hstack : rho.length ≤ 996 := by simp [rho, driverRest]
  have hcstack : (cache q.memory ++ rho).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  have gschedule := PairedAllInlineBoundarySites.gasSteps_schedule s (UInt256.ofNat 587)
    (messagePointer i) (driverRest input i) (by simp [driverRest]) hrun
    (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp
  have gschedule' : GasSteps (DriverTrace.compressEntry s input i)
      {q with pc := UInt256.ofNat 850, stack := PairedDerivedStartup.lowerWord :: cache q.memory ++ rho} := gschedule
  have hcanonical := SStartupPremises.scheduled_canonical s input i h ctx
  have gstartup := PairedAllInlineBoundarySites.gasSteps_startup q (cache q.memory ++ rho) hcstack qrun qactive
    hcanonical.1 hcanonical.2.1 hcanonical.2.2.1 hcanonical.2.2.2.1 hcanonical.2.2.2.2
    qcode qfork qnp
  let initial : CoreFrame := ⟨PairedLaneWordRound.packCrypto lane lane, 0⟩
  let terminal := PairedAllInlineCoreTrace.corePrefixChain.eval q.memory initial
  have gcore := PairedAllInlineCoreSites.gasSteps_core_prefix q initial rho
    hstack qrun qactive qcode qfork qnp
  have hentry :
      {q with pc := UInt256.ofNat 891, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto lane lane, 0⟩ (cache q.memory ++ rho)} =
      {q with pc := UInt256.ofNat 891, stack := PairedStartupTrace.resultStack q.memory (cache q.memory ++ rho)} := by
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
  have gsuffix := TerminalRoundSite.gasSteps_suffix q terminal.frame
    (UInt256.ofNat 587) (driverRest input i) hstack qrun qactive
    (valid_return q qcode) qcode qfork qnp
  rw [hmemory] at gsuffix
  have gsuffix' : GasSteps
      {q with pc := UInt256.ofNat 4802, stack := coreStack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] terminal (cache q.memory ++ rho)}
      (DriverTrace.compressReturned (resultState s input i) input i) := gsuffix
  exact gschedule'.trans (gstartup.trans ((gcore.cast hentry rfl).trans gsuffix'))

#print axioms startup_stack
#print axioms scheduled_readLane
#print axioms tail_stack
#print axioms valid_return
#print axioms gasSteps_compress

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
