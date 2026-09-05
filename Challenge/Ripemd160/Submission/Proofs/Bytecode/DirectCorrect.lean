import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Output
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Conditional end-to-end direct-bytecode certificate

Everything outside compression is discharged here: initialization and
padding, the post-padding block driver, the complete five-word output loop,
and `RETURN(0, 32)`.  `CompressionSeam` is the single remaining interface. It
asks for one gas-parametric compression trace per padded block and records the
five final chaining words produced by those traces.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectCorrect

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

private def loadedH (s : State) (i : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 (OutputTrace.hOffset i) 32 }

private def writeLoopState (s : State) (offset : Nat) (word ret : UInt256)
    (tail : List UInt256) : Nat → State
  | 0 => { s with
      pc := UInt256.ofNat 0x3c8
      stack := [⟨0⟩, UInt256.ofNat offset, word, ret] ++ tail }
  | j + 1 => { OutputTrace.writeByte (writeLoopState s offset word ret tail j)
        offset word j with
      pc := UInt256.ofNat 0x3c8
      stack := [UInt256.ofNat (j + 1), UInt256.ofNat offset, word, ret] ++ tail }

@[simp] private theorem writeLoopState_executionEnv (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    (writeLoopState s offset word ret tail j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih => simp [writeLoopState, OutputTrace.writeByte, ih]

@[simp] private theorem writeLoopState_halt (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    (writeLoopState s offset word ret tail j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih => simp [writeLoopState, OutputTrace.writeByte, ih]

@[simp] private theorem writeLoopState_callStack (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    (writeLoopState s offset word ret tail j).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih => simp [writeLoopState, OutputTrace.writeByte, ih]

private theorem writeLoopState_normalized (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    { writeLoopState s offset word ret tail j with
      pc := UInt256.ofNat 0x3c8
      stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail } =
      writeLoopState s offset word ret tail j := by
  cases j <;> rfl

private def afterWrittenWord (s : State) (input : ByteArray) (i : Nat) : State :=
  let loaded := loadedH s i
  let written := writeLoopState loaded (12 + 4 * i) (OutputTrace.hWord s i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4
  { written with
    pc := UInt256.ofNat 0x654
    stack := [UInt256.ofNat (i + 1), Padding.paddedWord input] }

private def outputLoopState (s : State) (input : ByteArray) : Nat → State
  | 0 => { OutputTrace.zeroOutput s with
      pc := UInt256.ofNat 0x654
      stack := [⟨0⟩, Padding.paddedWord input] }
  | i + 1 => afterWrittenWord (outputLoopState s input i) input i

@[simp] private theorem outputLoopState_executionEnv (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [outputLoopState, afterWrittenWord, loadedH, ih]

@[simp] private theorem outputLoopState_halt (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [outputLoopState, afterWrittenWord, loadedH, ih]

@[simp] private theorem outputLoopState_pc (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).pc = UInt256.ofNat 0x654 := by
  cases i <;> rfl

@[simp] private theorem outputLoopState_stack (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).stack =
      [UInt256.ofNat i, Padding.paddedWord input] := by
  cases i with
  | zero => rfl
  | succ i => rfl

@[simp] private theorem outputLoopState_callStack (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [outputLoopState, afterWrittenWord, loadedH, ih]

private theorem outputLoopState_normalized (s : State) (input : ByteArray)
    (i : Nat) :
    { outputLoopState s input i with
      pc := UInt256.ofNat 0x654
      stack := [UInt256.ofNat i, Padding.paddedWord input] } =
      outputLoopState s input i := by
  cases i <;> rfl

@[simp] private theorem loadedH_executionEnv (s : State) (i : Nat) :
    (loadedH s i).executionEnv = s.executionEnv := rfl

@[simp] private theorem loadedH_halt (s : State) (i : Nat) :
    (loadedH s i).halt = s.halt := rfl

private def outputResult (s : State) (input : ByteArray) : State :=
  let q := outputLoopState s input 5
  { q with
    pc := UInt256.ofNat 0x1412
    stack := [Padding.paddedWord input]
    halt := .Returned
    hReturn := MachineState.readPadded q.memory 0 32
    activeWords := q.activeWordsAfterUInt256 0 32 }

private def gasSteps_writeIteration (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) (hj : j < 4)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (writeLoopState s offset word ret tail j)
      (writeLoopState s offset word ret tail (j + 1)) := by
  let q := writeLoopState s offset word ret tail j
  have qcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gtestRaw : GasSteps
      { q with
        pc := UInt256.ofNat 0x3c8
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail }
      { q with
        pc := UInt256.ofNat 0x3d2
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail } := by
    apply Output.gasSteps_block OutputTrace.writeTestPath
    · exact qcode
    · exact qfork
    · simpa using
        OutputTrace.run_writeTest_continue q j
          (UInt256.ofNat offset :: word :: ret :: tail) hj (by simp; omega) qrun
    · exact qrun
    · exact qnp
  have gtest : GasSteps q
      { q with
        pc := UInt256.ofNat 0x3d2
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail } :=
    GasSteps.cast gtestRaw
      (by simpa [q] using writeLoopState_normalized s offset word ret tail j) rfl
  have gbody := Output.gasSteps_writeBody q offset word j ret tail hj
    (by omega) htail qcode qfork qrun qnp
  exact GasSteps.cast (gtest.trans gbody) rfl (by rfl)

private def gasSteps_writeLoop (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (writeLoopState s offset word ret tail 0)
      (writeLoopState s offset word ret tail 4) :=
  GasSteps.iterateBounded (count := 4) (I := writeLoopState s offset word ret tail)
    (fun j hj => gasSteps_writeIteration s offset word ret tail j hj
      htail hoff hcode hfork hrun hnp)

private def gasSteps_writeWord (s : State) (offset : Nat) (word ret : UInt256)
    (tail : List UInt256)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps
      { s with
        pc := UInt256.ofNat 0x3c6
        stack := UInt256.ofNat offset :: word :: ret :: tail }
      { writeLoopState s offset word ret tail 4 with pc := ret, stack := tail } := by
  have ginit : GasSteps
      { s with
        pc := UInt256.ofNat 0x3c6
        stack := UInt256.ofNat offset :: word :: ret :: tail }
      (writeLoopState s offset word ret tail 0) := by
    apply Output.gasSteps_block OutputTrace.writeInitPath
    · exact hcode
    · exact hfork
    · simpa [writeLoopState] using OutputTrace.run_writeInit s
        (UInt256.ofNat offset) word ret tail (by omega) hrun
    · exact hrun
    · exact hnp
  let q := writeLoopState s offset word ret tail 4
  have qcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gtest : GasSteps q
      { q with
        pc := UInt256.ofNat 0x3e9
        stack := UInt256.ofNat 4 :: UInt256.ofNat offset :: word :: ret :: tail } := by
    apply Output.gasSteps_block OutputTrace.writeTestPath
    · exact qcode
    · exact qfork
    · simpa [q, writeLoopState] using OutputTrace.run_writeTest_exit q
        (UInt256.ofNat offset :: word :: ret :: tail) (by simp; omega) qcode qrun
    · exact qrun
    · exact qnp
  have gexit : GasSteps
      { q with
        pc := UInt256.ofNat 0x3e9
        stack := UInt256.ofNat 4 :: UInt256.ofNat offset :: word :: ret :: tail }
      { q with pc := ret, stack := tail } := by
    apply Output.gasSteps_block OutputTrace.writeExitPath
    · exact qcode
    · exact qfork
    · simpa using OutputTrace.run_writeExit q (UInt256.ofNat offset) word ret
        tail (by omega) qcode qrun hvalid
    · exact qrun
    · exact qnp
  exact ginit.trans ((gasSteps_writeLoop s offset word ret tail htail hoff hcode hfork
    hrun hnp).trans (gtest.trans gexit))

private def gasSteps_outputIteration (s : State) (input : ByteArray)
    (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputLoopState s input i) (outputLoopState s input (i + 1)) := by
  let q := outputLoopState s input i
  have qcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gconditionRaw : GasSteps
      { q with
        pc := UInt256.ofNat 0x654
        stack := [UInt256.ofNat i, Padding.paddedWord input] }
      { q with
        pc := UInt256.ofNat 0x65e
        stack := [UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.outerTestPath
    · exact qcode
    · exact qfork
    · simpa using OutputTrace.run_outerTest_continue q i
        [Padding.paddedWord input] hi (by simp) qrun
    · exact qrun
    · exact qnp
  have gcondition : GasSteps q
      { q with
        pc := UInt256.ofNat 0x65e
        stack := [UInt256.ofNat i, Padding.paddedWord input] } :=
    GasSteps.cast gconditionRaw
      (by simpa [q] using outputLoopState_normalized s input i) rfl
  have gcall : GasSteps
      { q with
        pc := UInt256.ofNat 0x65e
        stack := [UInt256.ofNat i, Padding.paddedWord input] }
      { q with
        pc := UInt256.ofNat 0x20
        stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x66a,
          UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.hAtCallPath
    · exact qcode
    · exact qfork
    · simpa using OutputTrace.run_hAtCall q i [Padding.paddedWord input]
        (by simp) qcode qrun
    · exact qrun
    · exact qnp
  have gh : GasSteps
      { q with
        pc := UInt256.ofNat 0x20
        stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x66a,
          UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] }
      { loadedH q i with
        pc := UInt256.ofNat 0x66a
        stack := [OutputTrace.hWord q i, UInt256.ofNat 0x676,
          UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.hAtPath
    · exact qcode
    · exact qfork
    · simpa [loadedH] using OutputTrace.run_hAt q i
        [UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input]
        hi (by simp) qcode qrun
    · exact qrun
    · exact qnp
  let loaded := loadedH q i
  have loadedCode : loaded.executionEnv.code = submissionBytecode := by
    change q.executionEnv.code = submissionBytecode
    exact qcode
  have loadedFork : loaded.fork = .Osaka := by
    change q.executionEnv.fork = .Osaka
    exact qfork
  have loadedRun : loaded.halt = .Running := by
    change q.halt = .Running
    exact qrun
  have loadedNp : Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig loaded.executionEnv.fork
      loaded.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false
    exact qnp
  have gwcall : GasSteps
      { loaded with
        pc := UInt256.ofNat 0x66a
        stack := [OutputTrace.hWord q i, UInt256.ofNat 0x676,
          UInt256.ofNat i, Padding.paddedWord input] }
      { loaded with
        pc := UInt256.ofNat 0x3c6
        stack := [UInt256.ofNat (12 + 4 * i), OutputTrace.hWord q i,
          UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.writeCallPath
    · exact loadedCode
    · exact loadedFork
    · simpa using OutputTrace.run_writeCall loaded i (OutputTrace.hWord q i)
        [Padding.paddedWord input] hi (by simp) loadedCode loadedRun
    · exact loadedRun
    · exact loadedNp
  have gwrite := gasSteps_writeWord loaded (12 + 4 * i)
    (OutputTrace.hWord q i) (UInt256.ofNat 0x676)
    [UInt256.ofNat i, Padding.paddedWord input] (by simp) (by omega)
    loadedCode loadedFork loadedRun
    loadedNp (by exact Artifact.submissionArtifact.isValidJumpDest_index 818 (by rfl))
  let written := writeLoopState loaded (12 + 4 * i) (OutputTrace.hWord q i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4
  have writtenCode : written.executionEnv.code = submissionBytecode := by
    simpa [written] using loadedCode
  have writtenFork : written.fork = .Osaka := by
    simpa [written, State.fork] using loadedFork
  have writtenRun : written.halt = .Running := by simpa [written] using loadedRun
  have writtenNp : Precompile.isPrecompileWithConfig written.executionEnv.precompileConfig written.executionEnv.fork
      written.executionEnv.codeAddr = false := by simpa [written] using loadedNp
  have gnext : GasSteps
      { written with
        pc := UInt256.ofNat 0x676
        stack := [UInt256.ofNat i, Padding.paddedWord input] }
      (afterWrittenWord q input i) := by
    apply Output.gasSteps_block OutputTrace.outerNextPath
    · exact writtenCode
    · exact writtenFork
    · simpa [afterWrittenWord, written, loaded] using
        OutputTrace.run_outerNext written i [Padding.paddedWord input] hi
          (by simp) writtenCode writtenRun
    · exact writtenRun
    · exact writtenNp
  exact GasSteps.cast
    (gcondition.trans (gcall.trans (gh.trans (gwcall.trans (gwrite.trans gnext)))))
    rfl (by rfl)

private def gasSteps_outputLoop (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputLoopState s input 0) (outputLoopState s input 5) :=
  GasSteps.iterateBounded (count := 5) (I := outputLoopState s input)
    (fun i hi => gasSteps_outputIteration s input i hi hcode hfork hrun hnp)

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem spc2473 : Artifact.submissionArtifact.instructionPC 2473 = 0x1374 := by rfl
@[simp] private theorem spc2474 : Artifact.submissionArtifact.instructionPC 2474 = 0x1375 := by rfl
@[simp] private theorem spc2475 : Artifact.submissionArtifact.instructionPC 2475 = 0x1376 := by rfl
@[simp] private theorem spc2476 : Artifact.submissionArtifact.instructionPC 2476 = 0x1377 := by rfl
@[simp] private theorem spc2477 : Artifact.submissionArtifact.instructionPC 2477 = 0x1378 := by rfl
@[simp] private theorem spc2478 : Artifact.submissionArtifact.instructionPC 2478 = 0x1379 := by rfl
@[simp] private theorem spc2479 : Artifact.submissionArtifact.instructionPC 2479 = 0x137b := by rfl
@[simp] private theorem spc2480 : Artifact.submissionArtifact.instructionPC 2480 = 0x137c := by rfl
@[simp] private theorem spc2481 : Artifact.submissionArtifact.instructionPC 2481 = 0x137d := by rfl
@[simp] private theorem spc2482 : Artifact.submissionArtifact.instructionPC 2482 = 0x137f := by rfl
@[simp] private theorem spc2483 : Artifact.submissionArtifact.instructionPC 2483 = 0x1380 := by rfl
@[simp] private theorem spc2484 : Artifact.submissionArtifact.instructionPC 2484 = 0x1382 := by rfl
@[simp] private theorem spc2485 : Artifact.submissionArtifact.instructionPC 2485 = 0x1383 := by rfl
@[simp] private theorem spc2486 : Artifact.submissionArtifact.instructionPC 2486 = 0x1384 := by rfl
@[simp] private theorem spc2487 : Artifact.submissionArtifact.instructionPC 2487 = 0x1386 := by rfl
@[simp] private theorem spc2488 : Artifact.submissionArtifact.instructionPC 2488 = 0x1387 := by rfl
@[simp] private theorem spc2489 : Artifact.submissionArtifact.instructionPC 2489 = 0x1389 := by rfl
@[simp] private theorem spc2490 : Artifact.submissionArtifact.instructionPC 2490 = 0x138a := by rfl
@[simp] private theorem spc2491 : Artifact.submissionArtifact.instructionPC 2491 = 0x138b := by rfl
@[simp] private theorem spc2492 : Artifact.submissionArtifact.instructionPC 2492 = 0x138d := by rfl
@[simp] private theorem spc2493 : Artifact.submissionArtifact.instructionPC 2493 = 0x138e := by rfl
@[simp] private theorem spc2494 : Artifact.submissionArtifact.instructionPC 2494 = 0x1390 := by rfl
@[simp] private theorem spc2495 : Artifact.submissionArtifact.instructionPC 2495 = 0x1391 := by rfl
@[simp] private theorem spc2496 : Artifact.submissionArtifact.instructionPC 2496 = 0x1393 := by rfl
@[simp] private theorem spc2497 : Artifact.submissionArtifact.instructionPC 2497 = 0x1394 := by rfl
@[simp] private theorem spc2498 : Artifact.submissionArtifact.instructionPC 2498 = 0x1396 := by rfl
@[simp] private theorem spc2499 : Artifact.submissionArtifact.instructionPC 2499 = 0x1397 := by rfl
@[simp] private theorem spc2500 : Artifact.submissionArtifact.instructionPC 2500 = 0x1399 := by rfl
@[simp] private theorem spc2501 : Artifact.submissionArtifact.instructionPC 2501 = 0x139a := by rfl
@[simp] private theorem spc2502 : Artifact.submissionArtifact.instructionPC 2502 = 0x139b := by rfl
@[simp] private theorem spc2503 : Artifact.submissionArtifact.instructionPC 2503 = 0x139d := by rfl
@[simp] private theorem spc2504 : Artifact.submissionArtifact.instructionPC 2504 = 0x139e := by rfl
@[simp] private theorem spc2505 : Artifact.submissionArtifact.instructionPC 2505 = 0x13a0 := by rfl
@[simp] private theorem spc2506 : Artifact.submissionArtifact.instructionPC 2506 = 0x13a1 := by rfl
@[simp] private theorem spc2507 : Artifact.submissionArtifact.instructionPC 2507 = 0x13a2 := by rfl
@[simp] private theorem spc2508 : Artifact.submissionArtifact.instructionPC 2508 = 0x13a4 := by rfl
@[simp] private theorem spc2509 : Artifact.submissionArtifact.instructionPC 2509 = 0x13a5 := by rfl
@[simp] private theorem spc2510 : Artifact.submissionArtifact.instructionPC 2510 = 0x13a7 := by rfl
@[simp] private theorem spc2511 : Artifact.submissionArtifact.instructionPC 2511 = 0x13a8 := by rfl
@[simp] private theorem spc2512 : Artifact.submissionArtifact.instructionPC 2512 = 0x13a9 := by rfl
@[simp] private theorem spc2513 : Artifact.submissionArtifact.instructionPC 2513 = 0x13ab := by rfl
@[simp] private theorem spc2514 : Artifact.submissionArtifact.instructionPC 2514 = 0x13ac := by rfl
@[simp] private theorem spc2515 : Artifact.submissionArtifact.instructionPC 2515 = 0x13ae := by rfl
@[simp] private theorem spc2516 : Artifact.submissionArtifact.instructionPC 2516 = 0x13af := by rfl
@[simp] private theorem spc2517 : Artifact.submissionArtifact.instructionPC 2517 = 0x13b1 := by rfl
@[simp] private theorem spc2518 : Artifact.submissionArtifact.instructionPC 2518 = 0x13b2 := by rfl
@[simp] private theorem spc2519 : Artifact.submissionArtifact.instructionPC 2519 = 0x13b4 := by rfl
@[simp] private theorem spc2520 : Artifact.submissionArtifact.instructionPC 2520 = 0x13b5 := by rfl
@[simp] private theorem spc2521 : Artifact.submissionArtifact.instructionPC 2521 = 0x13b7 := by rfl
@[simp] private theorem spc2522 : Artifact.submissionArtifact.instructionPC 2522 = 0x13b8 := by rfl
@[simp] private theorem spc2523 : Artifact.submissionArtifact.instructionPC 2523 = 0x13b9 := by rfl
@[simp] private theorem spc2524 : Artifact.submissionArtifact.instructionPC 2524 = 0x13bb := by rfl
@[simp] private theorem spc2525 : Artifact.submissionArtifact.instructionPC 2525 = 0x13bc := by rfl
@[simp] private theorem spc2526 : Artifact.submissionArtifact.instructionPC 2526 = 0x13be := by rfl
@[simp] private theorem spc2527 : Artifact.submissionArtifact.instructionPC 2527 = 0x13bf := by rfl
@[simp] private theorem spc2528 : Artifact.submissionArtifact.instructionPC 2528 = 0x13c0 := by rfl
@[simp] private theorem spc2529 : Artifact.submissionArtifact.instructionPC 2529 = 0x13c2 := by rfl
@[simp] private theorem spc2530 : Artifact.submissionArtifact.instructionPC 2530 = 0x13c3 := by rfl
@[simp] private theorem spc2531 : Artifact.submissionArtifact.instructionPC 2531 = 0x13c5 := by rfl
@[simp] private theorem spc2532 : Artifact.submissionArtifact.instructionPC 2532 = 0x13c6 := by rfl
@[simp] private theorem spc2533 : Artifact.submissionArtifact.instructionPC 2533 = 0x13c7 := by rfl
@[simp] private theorem spc2534 : Artifact.submissionArtifact.instructionPC 2534 = 0x13c9 := by rfl
@[simp] private theorem spc2535 : Artifact.submissionArtifact.instructionPC 2535 = 0x13ca := by rfl
@[simp] private theorem spc2536 : Artifact.submissionArtifact.instructionPC 2536 = 0x13cc := by rfl
@[simp] private theorem spc2537 : Artifact.submissionArtifact.instructionPC 2537 = 0x13cd := by rfl
@[simp] private theorem spc2538 : Artifact.submissionArtifact.instructionPC 2538 = 0x13cf := by rfl
@[simp] private theorem spc2539 : Artifact.submissionArtifact.instructionPC 2539 = 0x13d0 := by rfl
@[simp] private theorem spc2540 : Artifact.submissionArtifact.instructionPC 2540 = 0x13d2 := by rfl
@[simp] private theorem spc2541 : Artifact.submissionArtifact.instructionPC 2541 = 0x13d3 := by rfl
@[simp] private theorem spc2542 : Artifact.submissionArtifact.instructionPC 2542 = 0x13d5 := by rfl
@[simp] private theorem spc2543 : Artifact.submissionArtifact.instructionPC 2543 = 0x13d6 := by rfl
@[simp] private theorem spc2544 : Artifact.submissionArtifact.instructionPC 2544 = 0x13d7 := by rfl
@[simp] private theorem spc2545 : Artifact.submissionArtifact.instructionPC 2545 = 0x13d9 := by rfl
@[simp] private theorem spc2546 : Artifact.submissionArtifact.instructionPC 2546 = 0x13da := by rfl
@[simp] private theorem spc2547 : Artifact.submissionArtifact.instructionPC 2547 = 0x13dc := by rfl
@[simp] private theorem spc2548 : Artifact.submissionArtifact.instructionPC 2548 = 0x13dd := by rfl
@[simp] private theorem spc2549 : Artifact.submissionArtifact.instructionPC 2549 = 0x13de := by rfl
@[simp] private theorem spc2550 : Artifact.submissionArtifact.instructionPC 2550 = 0x13e0 := by rfl
@[simp] private theorem spc2551 : Artifact.submissionArtifact.instructionPC 2551 = 0x13e1 := by rfl
@[simp] private theorem spc2552 : Artifact.submissionArtifact.instructionPC 2552 = 0x13e3 := by rfl
@[simp] private theorem spc2553 : Artifact.submissionArtifact.instructionPC 2553 = 0x13e4 := by rfl
@[simp] private theorem spc2554 : Artifact.submissionArtifact.instructionPC 2554 = 0x13e5 := by rfl
@[simp] private theorem spc2555 : Artifact.submissionArtifact.instructionPC 2555 = 0x13e7 := by rfl
@[simp] private theorem spc2556 : Artifact.submissionArtifact.instructionPC 2556 = 0x13e8 := by rfl
@[simp] private theorem spc2557 : Artifact.submissionArtifact.instructionPC 2557 = 0x13ea := by rfl
@[simp] private theorem spc2558 : Artifact.submissionArtifact.instructionPC 2558 = 0x13eb := by rfl
@[simp] private theorem spc2559 : Artifact.submissionArtifact.instructionPC 2559 = 0x13ed := by rfl
@[simp] private theorem spc2560 : Artifact.submissionArtifact.instructionPC 2560 = 0x13ee := by rfl
@[simp] private theorem spc2561 : Artifact.submissionArtifact.instructionPC 2561 = 0x13f0 := by rfl
@[simp] private theorem spc2562 : Artifact.submissionArtifact.instructionPC 2562 = 0x13f1 := by rfl
@[simp] private theorem spc2563 : Artifact.submissionArtifact.instructionPC 2563 = 0x13f3 := by rfl
@[simp] private theorem spc2564 : Artifact.submissionArtifact.instructionPC 2564 = 0x13f4 := by rfl
@[simp] private theorem spc2565 : Artifact.submissionArtifact.instructionPC 2565 = 0x13f5 := by rfl
@[simp] private theorem spc2566 : Artifact.submissionArtifact.instructionPC 2566 = 0x13f7 := by rfl
@[simp] private theorem spc2567 : Artifact.submissionArtifact.instructionPC 2567 = 0x13f8 := by rfl
@[simp] private theorem spc2568 : Artifact.submissionArtifact.instructionPC 2568 = 0x13fa := by rfl
@[simp] private theorem spc2569 : Artifact.submissionArtifact.instructionPC 2569 = 0x13fb := by rfl
@[simp] private theorem spc2570 : Artifact.submissionArtifact.instructionPC 2570 = 0x13fc := by rfl
@[simp] private theorem spc2571 : Artifact.submissionArtifact.instructionPC 2571 = 0x13fe := by rfl
@[simp] private theorem spc2572 : Artifact.submissionArtifact.instructionPC 2572 = 0x13ff := by rfl
@[simp] private theorem spc2573 : Artifact.submissionArtifact.instructionPC 2573 = 0x1401 := by rfl
@[simp] private theorem spc2574 : Artifact.submissionArtifact.instructionPC 2574 = 0x1402 := by rfl
@[simp] private theorem spc2575 : Artifact.submissionArtifact.instructionPC 2575 = 0x1403 := by rfl
@[simp] private theorem spc2576 : Artifact.submissionArtifact.instructionPC 2576 = 0x1405 := by rfl
@[simp] private theorem spc2577 : Artifact.submissionArtifact.instructionPC 2577 = 0x1406 := by rfl
@[simp] private theorem spc2578 : Artifact.submissionArtifact.instructionPC 2578 = 0x1408 := by rfl
@[simp] private theorem spc2579 : Artifact.submissionArtifact.instructionPC 2579 = 0x1409 := by rfl
@[simp] private theorem spc2580 : Artifact.submissionArtifact.instructionPC 2580 = 0x140b := by rfl
@[simp] private theorem spc2581 : Artifact.submissionArtifact.instructionPC 2581 = 0x140c := by rfl
@[simp] private theorem spc2582 : Artifact.submissionArtifact.instructionPC 2582 = 0x140e := by rfl
@[simp] private theorem spc2583 : Artifact.submissionArtifact.instructionPC 2583 = 0x140f := by rfl
@[simp] private theorem spc2584 : Artifact.submissionArtifact.instructionPC 2584 = 0x1411 := by rfl
@[simp] private theorem spc2585 : Artifact.submissionArtifact.instructionPC 2585 = 0x1412 := by rfl
@[simp] private theorem spc2586 : Artifact.submissionArtifact.instructionPC 2586 = 0x1413 := by rfl

/-- `BYTE i w` and the output loop's `wordByte` extract the same byte:
index `31 - j` from the high end is byte `j` from the low end. -/
private theorem byteAt_wordByte (w : UInt256) (j : Nat) (hj : j < 4) :
    UInt8.ofNat (((UInt256.ofNat (31 - j)).byteAt w).toNat % 256)
      = OutputTrace.wordByte w j := by
  have h31 : (31 - j) % UInt256.size = 31 - j := by
    apply Nat.mod_eq_of_lt; unfold UInt256.size; omega
  have h8 : (8 * j) % UInt256.size = 8 * j := by
    apply Nat.mod_eq_of_lt; unfold UInt256.size; omega
  have hff : (255 : Nat) % UInt256.size = 255 := by
    apply Nat.mod_eq_of_lt; unfold UInt256.size; omega
  have hlt : ¬ (32 ≤ 31 - j) := by omega
  have hsh : ¬ (256 ≤ 8 * j) := by omega
  have hjj : 31 - (31 - j) = j := by omega
  simp [UInt8.ofNat, OutputTrace.wordByte, UInt256.byteAt, UInt256.shiftRight,
    UInt256.land, UInt256.ofNat, UInt256.toNat, Fin.land, Fin.ofNat,
    h31, h8, hff, hlt, hsh, hjj]

@[simp] private theorem byteAt31 (w : UInt256) :
    UInt8.ofNat (((UInt256.ofNat 31).byteAt w).toNat % 256) = OutputTrace.wordByte w 0 := by
  simpa using byteAt_wordByte w 0 (by omega)

@[simp] private theorem byteAt30 (w : UInt256) :
    UInt8.ofNat (((UInt256.ofNat 30).byteAt w).toNat % 256) = OutputTrace.wordByte w 1 := by
  simpa using byteAt_wordByte w 1 (by omega)

@[simp] private theorem byteAt29 (w : UInt256) :
    UInt8.ofNat (((UInt256.ofNat 29).byteAt w).toNat % 256) = OutputTrace.wordByte w 2 := by
  simpa using byteAt_wordByte w 2 (by omega)

@[simp] private theorem byteAt28 (w : UInt256) :
    UInt8.ofNat (((UInt256.ofNat 28).byteAt w).toNat % 256) = OutputTrace.wordByte w 3 := by
  simpa using byteAt_wordByte w 3 (by omega)

/-- The appended straight-line serializer. -/
private def straightPath : List
    (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   ⟨2473, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2474, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2475, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨2476, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨2477, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2478, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2479, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2480, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2481, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨2482, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2483, .push ⟨1, by decide⟩ (UInt256.ofNat 12), by rfl, by decide⟩,
   ⟨2484, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2485, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2486, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨2487, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2488, .push ⟨1, by decide⟩ (UInt256.ofNat 13), by rfl, by decide⟩,
   ⟨2489, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2490, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2491, .push ⟨1, by decide⟩ (UInt256.ofNat 29), by rfl, by decide⟩,
   ⟨2492, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2493, .push ⟨1, by decide⟩ (UInt256.ofNat 14), by rfl, by decide⟩,
   ⟨2494, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2495, .push ⟨1, by decide⟩ (UInt256.ofNat 28), by rfl, by decide⟩,
   ⟨2496, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2497, .push ⟨1, by decide⟩ (UInt256.ofNat 15), by rfl, by decide⟩,
   ⟨2498, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2499, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨2500, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2501, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2502, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨2503, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2504, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨2505, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2506, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2507, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨2508, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2509, .push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨2510, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2511, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2512, .push ⟨1, by decide⟩ (UInt256.ofNat 29), by rfl, by decide⟩,
   ⟨2513, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2514, .push ⟨1, by decide⟩ (UInt256.ofNat 18), by rfl, by decide⟩,
   ⟨2515, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2516, .push ⟨1, by decide⟩ (UInt256.ofNat 28), by rfl, by decide⟩,
   ⟨2517, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2518, .push ⟨1, by decide⟩ (UInt256.ofNat 19), by rfl, by decide⟩,
   ⟨2519, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2520, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨2521, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2522, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2523, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨2524, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2525, .push ⟨1, by decide⟩ (UInt256.ofNat 20), by rfl, by decide⟩,
   ⟨2526, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2527, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2528, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨2529, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2530, .push ⟨1, by decide⟩ (UInt256.ofNat 21), by rfl, by decide⟩,
   ⟨2531, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2532, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2533, .push ⟨1, by decide⟩ (UInt256.ofNat 29), by rfl, by decide⟩,
   ⟨2534, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2535, .push ⟨1, by decide⟩ (UInt256.ofNat 22), by rfl, by decide⟩,
   ⟨2536, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2537, .push ⟨1, by decide⟩ (UInt256.ofNat 28), by rfl, by decide⟩,
   ⟨2538, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2539, .push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨2540, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2541, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨2542, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2543, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2544, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨2545, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2546, .push ⟨1, by decide⟩ (UInt256.ofNat 24), by rfl, by decide⟩,
   ⟨2547, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2548, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2549, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨2550, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2551, .push ⟨1, by decide⟩ (UInt256.ofNat 25), by rfl, by decide⟩,
   ⟨2552, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2553, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2554, .push ⟨1, by decide⟩ (UInt256.ofNat 29), by rfl, by decide⟩,
   ⟨2555, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2556, .push ⟨1, by decide⟩ (UInt256.ofNat 26), by rfl, by decide⟩,
   ⟨2557, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2558, .push ⟨1, by decide⟩ (UInt256.ofNat 28), by rfl, by decide⟩,
   ⟨2559, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2560, .push ⟨1, by decide⟩ (UInt256.ofNat 27), by rfl, by decide⟩,
   ⟨2561, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2562, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨2563, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2564, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2565, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨2566, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2567, .push ⟨1, by decide⟩ (UInt256.ofNat 28), by rfl, by decide⟩,
   ⟨2568, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2569, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2570, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨2571, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2572, .push ⟨1, by decide⟩ (UInt256.ofNat 29), by rfl, by decide⟩,
   ⟨2573, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2574, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2575, .push ⟨1, by decide⟩ (UInt256.ofNat 29), by rfl, by decide⟩,
   ⟨2576, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2577, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨2578, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2579, .push ⟨1, by decide⟩ (UInt256.ofNat 28), by rfl, by decide⟩,
   ⟨2580, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2581, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨2582, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2583, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2584, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨2585, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩
  ]

set_option maxHeartbeats 10000000 in
private theorem run_straight (s : State) (input : ByteArray)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock straightPath (DriverTrace.afterExit s input) =
      some (outputResult s input) := by
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [straightPath, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, DriverTrace.afterExit, outputResult, outputLoopState,
    hzeroNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    afterWrittenWord, writeLoopState, loadedH, OutputTrace.writeByte,
    OutputTrace.zeroOutput, OutputTrace.hWord, OutputTrace.hOffset,
    State.activeWordsAfterUInt256, hrun, _hcode]

private def gasSteps_output (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.afterExit s input) (outputResult s input) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka straightPath
    hcode hfork (run_straight s input hcode hrun) hrun hnp

/-- The one remaining end-to-end hypothesis: a certified compression trace
for each padded block, plus the resulting five mathematical chaining words. -/
structure CompressionSeam (input : ByteArray) where
  states : Nat → State
  initial : DriverTrace.setupEntry (states 0) input = PaddingTrace.padReturned input
  code : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).executionEnv.code = submissionBytecode
  fork : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).fork = .Osaka
  running : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).halt = .Running
  noPrecompile : ∀ i, i ≤ DriverTrace.blockCount input →
    Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
      (states i).executionEnv.codeAddr = false
  callStack : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).callStack = []
  compress : ∀ i, i < DriverTrace.blockCount input →
    GasSteps (DriverTrace.compressEntry (states i) input i)
      (DriverTrace.compressReturned (states (i + 1)) input i)
  finalWords : ∀ i : Fin 5,
    OutputTrace.hWord (states (DriverTrace.blockCount input)) i =
      Challenge.EvmProof.Word.ofUInt32
      (SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
          (Padding.paddedMessage input) 0
          (DriverTrace.blockCount input))[i]!

private noncomputable def gasSteps_driver (input : ByteArray)
    (hfit : CalldataFits input) (seam : CompressionSeam input) :
    GasSteps (PaddingTrace.padReturned input)
      (DriverTrace.afterExit (seam.states (DriverTrace.blockCount input)) input) := by
  have gsetup := DriverTrace.gasSteps_setup (seam.states 0) input
    (seam.code 0 (by omega)) (seam.fork 0 (by omega))
    (seam.running 0 (by omega)) (seam.noPrecompile 0 (by omega))
  have gloop := DriverTrace.gasSteps_loop_of_compress seam.states input hfit
    seam.code seam.fork seam.running seam.noPrecompile seam.compress
  let final := seam.states (DriverTrace.blockCount input)
  have gexit := DriverTrace.gasSteps_condition_exit final input hfit
    (seam.code _ (by omega)) (seam.fork _ (by omega))
    (seam.running _ (by omega)) (seam.noPrecompile _ (by omega))
  exact GasSteps.cast (gsetup.trans (gloop.trans gexit)) seam.initial
    (by simp [final, DriverTrace.afterExit])

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input)
    (seam : CompressionSeam input) :
    GasSteps (initialState submissionBytecode input 0)
      (outputResult (seam.states (DriverTrace.blockCount input)) input) := by
  let final := seam.states (DriverTrace.blockCount input)
  have gout := gasSteps_output final input (seam.code _ (by omega))
    (seam.fork _ (by omega)) (seam.running _ (by omega))
    (seam.noPrecompile _ (by omega))
  exact (PaddingTrace.gasSteps_pad input hfit).trans
    ((gasSteps_driver input hfit seam).trans (by simpa [final] using gout))

/-- Conditional exact-gas connection to the closed schedule in `GasCost`.
All control-flow costs are already carried by `fullTrace`; the remaining cost
identity is precisely the compression-cost telescope. -/
theorem correctWithSchedule_of_compression
    (seam : ∀ (input : ByteArray), CalldataFits input → CompressionSeam input)
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit (seam input hfit)).cost = GasCost.referenceGas input)
    (hresult : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (outputResult
        ((seam input hfit).states (DriverTrace.blockCount input)) input).toResult =
          .returned (spec input)) :
    GasCost.CorrectWithSchedule submissionBytecode GasCost.referenceGasForSize := by
  apply GasCost.gasSchedule_correct_of_trace
    (finalState := fun input hfit => outputResult
      ((seam input hfit).states (DriverTrace.blockCount input)) input)
    (fullTrace := fun input hfit => fullTrace input hfit (seam input hfit))
  · exact hcost
  · intro input hfit
    simp [outputResult, State.isDone, State.isHalted, State.isRunning,
      (seam input hfit).callStack (DriverTrace.blockCount input) (by omega)]
  · exact hresult

/-- The same conditional certificate, projected to the challenge's minimal
eventual-sufficiency statement. -/
theorem correct_of_compression
    (seam : ∀ (input : ByteArray), CalldataFits input → CompressionSeam input)
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit (seam input hfit)).cost = GasCost.referenceGas input)
    (hresult : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (outputResult
        ((seam input hfit).states (DriverTrace.blockCount input)) input).toResult =
          .returned (spec input)) :
    Correct submissionBytecode :=
  GasCost.correct_of_schedule
    (correctWithSchedule_of_compression seam hcost hresult)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectCorrect
