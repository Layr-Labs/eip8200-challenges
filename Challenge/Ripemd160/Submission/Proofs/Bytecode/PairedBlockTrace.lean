import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PairedBlockModel PairedHelperBooleanTrace

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
      (UInt256.ofNat 102 :: driverRest input i) =
      PairedAllInlineTail.entryStack (resultFrame s input i)
        (UInt256.ofNat 102) (driverRest input i) := by
  rfl

theorem valid_return (s : State) (hcode : s.executionEnv.code = submissionBytecode) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 102).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 64 = 102 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 102 = true
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
  let rho := UInt256.ofNat 102 :: driverRest input i
  let lane := PairedBlockMath.readLane s.memory
  have qactive : 23 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have qcode : q.executionEnv.code = submissionBytecode := hcode
  have qfork : q.fork = .Osaka := hfork
  have qrun : q.halt = .Running := hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := hnp
  have hstack : rho.length ≤ 1002 := by simp [rho, driverRest]
  have gschedule := PairedAllInlineBoundarySites.gasSteps_schedule s (UInt256.ofNat 102)
    (messagePointer i) (driverRest input i) (by simp [driverRest]) hrun
    (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp
  have gschedule' : GasSteps (DriverTrace.compressEntry s input i)
      {q with pc := UInt256.ofNat 745, stack := rho} := gschedule
  -- Historical invariant-based mask omission: ercumentyildirim/e63fc232.
  -- The five premises are derived here; the arbitrary-memory startup contract is not weakened.
  have hhash : PairedBlockMath.hashWords q.memory = Compression.embedHash h := by
    change PairedBlockMath.hashWords (scheduledState s i).memory = Compression.embedHash h
    rw [scheduled_hashWords]
    exact ctx.hash
  have hn (a : Nat) (proj : Compression.EvmHashState → UInt256)
      (hproj : proj (PairedBlockMath.hashWords q.memory) = MachineState.readWord q.memory a)
      (x : UInt32) (hx : proj (Compression.embedHash h) = Challenge.EvmProof.Word.ofUInt32 x) :
      UInt256.land PairedDerivedStartup.lowerWord (MachineState.readWord q.memory a) =
        MachineState.readWord q.memory a := by
    rw [← hproj, hhash, hx]
    exact PairedNormalizedStartup.mask_identity_ofUInt32 x
  have h32 := hn 32 Compression.EvmHashState.h0 rfl _ rfl
  have h64 := hn 64 Compression.EvmHashState.h1 rfl _ rfl
  have h96 := hn 96 Compression.EvmHashState.h2 rfl _ rfl
  have h128 := hn 128 Compression.EvmHashState.h3 rfl _ rfl
  have h160 := hn 160 Compression.EvmHashState.h4 rfl _ rfl
  have gstartup := PairedAllInlineBoundarySites.gasSteps_startup q rho hstack qrun qactive
    qcode qfork qnp h32 h64 h96 h128 h160
  have gcore := PairedAllInlineCoreSites.gasSteps_core_normalized q (blockWords input i) lane lane rho
    hstack qrun qactive qcode qfork qnp (scheduled_ready s input i h hfit hi ctx)
  have hentry :
      {q with
        pc := UInt256.ofNat 803
        stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower]
          ⟨PairedLaneWordRound.packCrypto lane lane, 0⟩ rho} =
      {q with pc := UInt256.ofNat 803, stack := PairedStartupTrace.resultStack q.memory rho} := by
    rw [startup_stack, scheduled_readLane]
  have htail :
      {q with
        pc := UInt256.ofNat 5066
        stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower]
          (coreCryptoResult (blockWords input i) lane lane) rho} =
      {q with
        pc := UInt256.ofNat 5066
        stack := PairedAllInlineTail.entryStack (resultFrame s input i)
          (UInt256.ofNat 102) (driverRest input i)} := by
    rw [show coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower]
        (coreCryptoResult (blockWords input i) lane lane) rho =
      PairedAllInlineTail.entryStack (resultFrame s input i) (UInt256.ofNat 102)
        (driverRest input i) from tail_stack s input i]
  have gtail := PairedAllInlineBoundarySites.gasSteps_tail q (UInt256.ofNat 102) (resultFrame s input i)
    (driverRest input i) (by simp [driverRest]) qrun qactive
    (valid_return q qcode) qcode qfork qnp
  have gtail' : GasSteps
      {q with
        pc := UInt256.ofNat 5066
        stack := PairedAllInlineTail.entryStack (resultFrame s input i)
          (UInt256.ofNat 102) (driverRest input i)}
      (DriverTrace.compressReturned (resultState s input i) input i) := gtail
  exact gschedule'.trans (gstartup.trans ((gcore.cast hentry htail).trans gtail'))

#print axioms startup_stack
#print axioms scheduled_readLane
#print axioms tail_stack
#print axioms valid_return
#print axioms gasSteps_compress

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
