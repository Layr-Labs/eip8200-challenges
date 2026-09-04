import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# H24 compression frame

This module certifies the frame around the scheduled compression body.  The
compression body itself starts at the load-entry seam.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame

open Challenge.Ripemd160
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Stepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def prefixPath : List Located :=
  [⟨979, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨980, .push ⟨2, by decide⟩ (UInt256.ofNat 0x72f), by rfl, by decide⟩,
   ⟨981, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨982, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1164), by rfl, by decide⟩,
   ⟨983, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def exitPath : List Located :=
  [⟨984, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨985, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def loadSite986 : GenericRoundSite Artifact.submissionArtifact .Osaka
    StackLoadTrace.loadTemplate :=
  StackSiteBuilder.ofSlice (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    StackLoadTrace.loadTemplate 986 (by rfl) (by decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := StackLoadTrace.loadTemplate) (by decide))
    (by simp [StackLoadTrace.loadTemplate])

def loadSite1476 : GenericRoundSite Artifact.submissionArtifact .Osaka
    StackLoadTrace.loadTemplate :=
  StackSiteBuilder.ofSlice (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    StackLoadTrace.loadTemplate 1316 (by rfl) (by decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := StackLoadTrace.loadTemplate) (by decide))
    (by simp [StackLoadTrace.loadTemplate])

@[simp] theorem loadSite986_startPC : loadSite986.startPC = UInt256.ofNat 0x731 := by
  rfl

@[simp] theorem loadSite1476_startPC : loadSite1476.startPC = UInt256.ofNat 0xa10 := by
  rfl

def frameRest (input : ByteArray) (i : Nat) : List UInt256 :=
  UInt256.ofNat 0x643 :: StackBlockModel.driverRest input i

def frameLoadEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  StackLoadTrace.loadEntry (StackBlockModel.scheduledState s input i)
    (UInt256.ofNat 0x731) (frameRest input i)

theorem frameLoadEntry_eq_loadSite986 (s : State) (input : ByteArray) (i : Nat) :
    frameLoadEntry s input i =
      StackLoadTrace.loadEntry (StackBlockModel.scheduledState s input i)
        loadSite986.startPC (frameRest input i) := by
  simp [frameLoadEntry]

theorem run_prefix (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock prefixPath (DriverTrace.compressEntry s input i) =
      some (DenseScheduleTemplate.scheduleEntry s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f)
        (StackBlockModel.scheduleRest input i)) := by
  have hpc979 : Artifact.submissionArtifact.instructionPC 979 = 0x726 := by rfl
  have hpc980 : Artifact.submissionArtifact.instructionPC 980 = 0x727 := by rfl
  have hpc981 : Artifact.submissionArtifact.instructionPC 981 = 0x72a := by rfl
  have hpc982 : Artifact.submissionArtifact.instructionPC 982 = 0x72b := by rfl
  have hpc983 : Artifact.submissionArtifact.instructionPC 983 = 0x72e := by rfl
  have hdest1164 : Decode.isValidJumpDest submissionBytecode 0x1164 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2313 (by rfl)
  simp [prefixPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DriverTrace.compressEntry, DenseScheduleTemplate.scheduleEntry,
    PackedScheduleSite.packedScheduleSite_startPC, StackBlockModel.scheduleRest,
    StackBlockModel.driverRest, hcode, hrun, hpc979, hpc980, hpc981, hpc982, hpc983,
    hdest1164]

theorem run_exit (s : State) (input : ByteArray) (i : Nat)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock exitPath
        (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)) =
      some (frameLoadEntry s input i) := by
  have hpc984 : Artifact.submissionArtifact.instructionPC 984 = 0x72f := by rfl
  have hpc985 : Artifact.submissionArtifact.instructionPC 985 = 0x730 := by rfl
  simp [exitPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    frameLoadEntry, Schedule.scheduleReturned, StackBlockModel.scheduledState,
    StackBlockModel.scheduleRest, StackBlockModel.driverRest, frameRest,
    StackLoadTrace.loadEntry,
    hrun, hpc984, hpc985]

def gasSteps_prefix (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i) 
      (DenseScheduleTemplate.scheduleEntry s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f)
        (StackBlockModel.scheduleRest input i)) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka prefixPath
  · exact hcode
  · exact hfork
  · exact run_prefix s input i hcode hrun
  · exact hrun
  · exact hnp

def gasSteps_schedule (s : State) (input : ByteArray) (i : Nat)
    (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
        (DenseScheduleTemplate.scheduleEntry s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f)
          (StackBlockModel.scheduleRest input i))
        (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)) := by
  let rest := StackBlockModel.scheduleRest input i
  have hstate :
      Schedule.scheduleReturned
          (DenseScheduleTemplate.denseExpectedState s
            PackedScheduleSite.packedScheduleSite.startPC
            (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f) rest)
          (UInt256.ofNat 0x72f) rest =
        Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x72f) rest := by
    simpa [StackBlockModel.scheduledState, StackBlockModel.withMemory,
      StackBlockModel.withActiveWords] using
      (DenseScheduleState.returned_eq_schedule_with_memory_active s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f) rest
        (DenseScheduleTemplate.denseExpectedMemory s
          (DriverTrace.messageOffsetWord i)) rfl)
  have hstack1023 : rest.length < 1023 := by
    change 4 < 1023
    norm_num
  have hstack1017 : rest.length < 1017 := by
    change 4 < 1017
    norm_num
  have hraw :
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f) rest) =
        some (DenseScheduleTemplate.denseExpectedState s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f) rest) := by
    exact DenseScheduleTrace.runInstrSeq_denseBeforeJump s
      PackedScheduleSite.packedScheduleSite.startPC
      (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f) rest
      hstack1017 hrun
  have hartifactCode : s.executionEnv.code = Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hvalid :
      Decode.isValidJumpDest s.executionEnv.code
        (UInt256.ofNat 0x72f).toNat = true := by
    rw [hcode]
    exact Artifact.submissionArtifact.isValidJumpDest_index 984 (by rfl)
  have hpacked := PackedScheduleSite.gasSteps_packedSchedule s
    (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f) rest
    hartifactCode hfork hrun hnp hstack1023 hvalid
    hraw
  exact hpacked.cast rfl hstate

def gasSteps_exit (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
        (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i))
        (frameLoadEntry s input i) := by
  have hqcode :
      (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
        (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)).executionEnv.code =
        submissionBytecode := by
    simp [StackBlockModel.scheduledState, Schedule.scheduleReturned, hcode]
  have hqfork :
      (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
        (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)).fork = .Osaka := by
    simpa [StackBlockModel.scheduledState, Schedule.scheduleReturned, State.fork] using hfork
  have hqrun :
      (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
        (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)).halt = .Running := by
    simp [StackBlockModel.scheduledState, Schedule.scheduleReturned, hrun]
  have hqnp :
      Precompile.isPrecompileWithConfig
          (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
            (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)).executionEnv.precompileConfig
          (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
            (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)).executionEnv.fork
          (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
            (UInt256.ofNat 0x72f) (StackBlockModel.scheduleRest input i)).executionEnv.codeAddr = false := by
    simpa [StackBlockModel.scheduledState, Schedule.scheduleReturned] using hnp
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka exitPath
  · exact hqcode
  · exact hqfork
  · exact run_exit s input i hrun
  · exact hqrun
  · exact hqnp

def gasSteps_frame (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i) (frameLoadEntry s input i) :=
  (gasSteps_prefix s input i hcode hfork hrun hnp).trans <|
    (gasSteps_schedule s input i hfit hi hcode hfork hrun hnp).trans <|
      gasSteps_exit s input i hcode hfork hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame
