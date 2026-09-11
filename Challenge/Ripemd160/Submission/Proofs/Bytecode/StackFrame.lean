import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# H30b compression frame

This module certifies the frame around the scheduled compression body.  The
compression body itself starts at the load-entry seam.

N: the single-use dense helper call prefix and its inner return are removed.
The dense-before-JUMP body now runs inline from the compression entry
(index 272, pc 0x1d0) and ends at pc 0x28e, where the mask and factor pushes
follow directly.  The raw suffix is the two-word driver stack; the preserved
outer return word 0x66 heads `frameRest`.  The historical model return ghost
0x29e and the ghost suffix `scheduleRest` survive only inside the pure
`Schedule.loopState` model, overwritten by the congrArg record bridge.
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

/-- N+L exit block: the mask push (index 323, pc 0x28e) and the factor push
(index 324, pc 0x293).  The removed call prefix and the removed inner-return
JUMPDEST are no longer live instructions. -/
def exitPath : List Located :=
  [⟨345, .push ⟨4, by decide⟩ mask, by rfl, by decide⟩,
   ⟨346, .push ⟨5, by decide⟩ QuadRoundTemplate.factor, by rfl, by decide⟩]

def loadSite987 : GenericRoundSite Artifact.submissionArtifact .Osaka
    StackLoadTrace.loadTemplate :=
  StackSiteBuilder.ofSlice (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    StackLoadTrace.loadTemplate 325 (by rfl) (by decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := StackLoadTrace.loadTemplate) (by decide))
    (by simp [StackLoadTrace.loadTemplate])

def loadSite1238 : GenericRoundSite Artifact.submissionArtifact .Osaka
    StackLoadTrace.loadTemplate :=
  StackSiteBuilder.ofSlice (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    StackLoadTrace.loadTemplate QuadLayout.rightLoadIndex (by rfl) (by decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := StackLoadTrace.loadTemplate) (by decide))
    (by simp [StackLoadTrace.loadTemplate])

@[simp] theorem loadSite987_startPC : loadSite987.startPC = UInt256.ofNat 0x299 := by
  rfl

@[simp] theorem loadSite1238_startPC :
    loadSite1238.startPC = UInt256.ofNat 0xb73 := by
  change UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC QuadLayout.rightLoadIndex) = _
  rw [QuadLayout.rightLoad_pc]

def frameRest (input : ByteArray) (i : Nat) : List UInt256 :=
  UInt256.ofNat 0x66 :: StackBlockModel.driverRest input i

/-- The frame the two exit pushes run from: the schedule body ends at pc 0x28e
with the outer return word preserved on the stack. -/
def frameSeam (s : State) (input : ByteArray) (i : Nat) : State :=
  { StackBlockModel.scheduledState s input i with
    pc := UInt256.ofNat 0x28e, stack := frameRest input i }

def frameLoadEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  StackLoadTrace.loadEntry (StackBlockModel.scheduledState s input i)
    (UInt256.ofNat 0x299) (QuadRoundTemplate.factor :: mask :: frameRest input i)

theorem frameLoadEntry_eq_loadSite987 (s : State) (input : ByteArray) (i : Nat) :
    frameLoadEntry s input i =
      StackLoadTrace.loadEntry (StackBlockModel.scheduledState s input i)
        loadSite987.startPC (QuadRoundTemplate.factor :: mask :: frameRest input i) := by
  simp [frameLoadEntry]

/-- N+L: the raw dense entry is definitionally the compression entry — the
relocated site start 0x1d0, the message pointer, the preserved outer return
0x66, and the two-word driver suffix.  No prefix instructions run. -/
theorem frameEntry_eq_scheduleEntry (s : State) (input : ByteArray) (i : Nat) :
    DriverTrace.compressEntry s input i =
      DenseScheduleTemplate.scheduleEntry s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66)
        (StackBlockModel.driverRest input i) := by
  unfold DriverTrace.compressEntry DenseScheduleTemplate.scheduleEntry
    StackBlockModel.driverRest PackedScheduleSite.packedScheduleSite
  rfl

/-- Model bridge: the ghost return 0x29e and
the ghost suffix 0x66::driverRest = scheduleRest are overwritten on both
sides by pc 0x28e and frameRest, without changing the pure loopState model. -/
theorem denseEnd_eq_frameSeam (s : State) (input : ByteArray) (i : Nat) :
    DenseScheduleTemplate.denseExpectedState s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66)
        (StackBlockModel.driverRest input i) =
      frameSeam s input i := by
  have hpc : PackedScheduleSite.packedScheduleSite.startPC = UInt256.ofNat 512 :=
    PackedScheduleSite.packedScheduleSite_startPC
  let mo := DriverTrace.messageOffsetWord i
  let dr := StackBlockModel.driverRest input i
  have h := DenseScheduleState.returned_eq_schedule_with_memory_active s
    (UInt256.ofNat 464) mo (UInt256.ofNat 670) (UInt256.ofNat 0x66 :: dr)
    (DenseScheduleTemplate.denseExpectedMemory s mo) rfl
  have hu := congrArg (fun t : State =>
    { t with pc := UInt256.ofNat 654, stack := UInt256.ofNat 0x66 :: dr }) h
  rw [hpc]
  show DenseScheduleTemplate.denseExpectedState s (UInt256.ofNat 464)
      mo (UInt256.ofNat 0x66) dr = frameSeam s input i
  calc DenseScheduleTemplate.denseExpectedState s (UInt256.ofNat 464)
        mo (UInt256.ofNat 0x66) dr =
      { Schedule.scheduleReturned
          (DenseScheduleTemplate.denseExpectedState s (UInt256.ofNat 464)
            mo (UInt256.ofNat 670) (UInt256.ofNat 0x66 :: dr))
          (UInt256.ofNat 670) (UInt256.ofNat 0x66 :: dr) with
        pc := UInt256.ofNat 654, stack := UInt256.ofNat 0x66 :: dr } := by
        unfold DenseScheduleTemplate.denseExpectedState Schedule.scheduleReturned
        rfl
    _ = { Schedule.scheduleReturned
            { { Schedule.loopState s mo (UInt256.ofNat 670)
                  (UInt256.ofNat 0x66 :: dr) 16 with
                memory := DenseScheduleTemplate.denseExpectedMemory s mo } with
              activeWords := DenseScheduleTemplate.denseExpectedActiveWords s mo }
            (UInt256.ofNat 670) (UInt256.ofNat 0x66 :: dr) with
          pc := UInt256.ofNat 654, stack := UInt256.ofNat 0x66 :: dr } := hu
    _ = frameSeam s input i := by
        unfold frameSeam frameRest StackBlockModel.scheduledState
          StackBlockModel.withMemory StackBlockModel.withActiveWords
          StackBlockModel.scheduleRest Schedule.scheduleReturned
        rw [show [UInt256.ofNat 0x66] ++ dr = UInt256.ofNat 0x66 :: dr from rfl]

theorem run_exit (s : State) (input : ByteArray) (i : Nat)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock exitPath (frameSeam s input i) =
      some (frameLoadEntry s input i) := by
  have hpc940 : Artifact.submissionArtifact.instructionPC 345 = 0x25b := by rfl
  have hpc941 : Artifact.submissionArtifact.instructionPC 346 = 0x25c := by rfl
  simp [exitPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    frameSeam, frameLoadEntry, StackBlockModel.scheduledState,
    StackBlockModel.withMemory, StackBlockModel.withActiveWords,
    StackBlockModel.scheduleRest, StackBlockModel.driverRest, frameRest,
    StackLoadTrace.loadEntry, QuadRoundTemplate.factor,
    hrun, hpc940, hpc941, mask]

/-- N schedule step: raw dense body at the relocated site with the preserved
outer return word and the bare two-word driver suffix.  No `hvalid` premise —
the removed final JUMP is never executed. -/
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
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66)
          (StackBlockModel.driverRest input i))
        (frameSeam s input i) := by
  let rest := StackBlockModel.driverRest input i
  have hstack1017 : rest.length < 1017 := by
    simp [rest, StackBlockModel.driverRest]
  have hraw :
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66) rest) =
        some (DenseScheduleTemplate.denseExpectedState s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66) rest) := by
    exact DenseScheduleTrace.runInstrSeq_denseBeforeJump s
      PackedScheduleSite.packedScheduleSite.startPC
      (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66) rest
      hstack1017 hrun
  have hartifactCode : s.executionEnv.code = Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hpacked := PackedScheduleSite.gasSteps_packedSchedule_of_raw s
    (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x66) rest
    hartifactCode hfork hrun hnp hraw
  exact hpacked.cast rfl (denseEnd_eq_frameSeam s input i)

def gasSteps_exit (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (frameSeam s input i) (frameLoadEntry s input i) := by
  have hqcode : (frameSeam s input i).executionEnv.code = submissionBytecode := by
    simp [frameSeam, StackBlockModel.scheduledState, StackBlockModel.withMemory,
      StackBlockModel.withActiveWords, hcode]
  have hqfork : (frameSeam s input i).fork = .Osaka := by
    simpa [frameSeam, StackBlockModel.scheduledState,
      StackBlockModel.withMemory, StackBlockModel.withActiveWords,
      State.fork] using hfork
  have hqrun : (frameSeam s input i).halt = .Running := by
    simp [frameSeam, StackBlockModel.scheduledState, StackBlockModel.withMemory,
      StackBlockModel.withActiveWords, hrun]
  have hqnp :
      Precompile.isPrecompileWithConfig
          (frameSeam s input i).executionEnv.precompileConfig
          (frameSeam s input i).executionEnv.fork
          (frameSeam s input i).executionEnv.codeAddr = false := by
    simpa [frameSeam, StackBlockModel.scheduledState, StackBlockModel.withMemory,
      StackBlockModel.withActiveWords] using hnp
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
  ((gasSteps_schedule s input i hfit hi hcode hfork hrun hnp).cast
    (frameEntry_eq_scheduleEntry s input i).symm rfl).trans <|
      gasSteps_exit s input i hcode hfork hrun hnp

def savedLeft (left : Compression.EvmWorking) : List UInt256 :=
  [left.b, left.c, left.d, left.e, left.a]

def routeEntry (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  StackRoundTrace.roundEntry s (UInt256.ofNat 0xb45)
    left.a left.b left.c left.d left.e (QuadRoundTemplate.factor :: rest)

def routeReturned (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  StackLoadTrace.loadEntry s (UInt256.ofNat 0xb46)
    (QuadRoundTemplate.factor :: (savedLeft left ++ rest))

def routePath : List Located :=
  [⟨QuadLayout.routeIndex, .op (.Swap ⟨4, by decide⟩), by rfl,
    wfOp (by decide) trivial rfl⟩]

theorem run_route (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1007)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock routePath (routeEntry s left rest) =
      some (routeReturned s left rest) := by
  have hpc : Artifact.submissionArtifact.instructionPC
      QuadLayout.routeIndex = 0xb45 := QuadLayout.route_pc
  have hcap : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hswap :
      (left.a :: left.b :: left.c :: left.d :: left.e ::
        QuadRoundTemplate.factor :: rest).exchange 0 5 =
      some (QuadRoundTemplate.factor :: left.b :: left.c :: left.d :: left.e ::
        left.a :: rest) := by
    simpa using YulEvmCompiler.exchange_swap left.a QuadRoundTemplate.factor
      [left.b, left.c, left.d, left.e] rest
  simp [routePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    routeEntry, routeReturned, StackRoundTrace.roundEntry,
    StackLoadTrace.loadEntry, savedLeft, hpc, hrun, hcap, hswap]

def gasSteps_route (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1007)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (routeEntry s left rest) (routeReturned s left rest) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka routePath
  · exact hcode
  · exact hfork
  · exact run_route s left rest hstack hrun
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame
