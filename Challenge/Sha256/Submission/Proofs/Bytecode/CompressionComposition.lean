
import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionExec
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
/-!
# Composition of the reference SHA-256 compression executor

This layer chains the reusable certified basic blocks from `CompressionExec`
into complete schedule, round-loop, feed-forward, and return executions.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.Compression

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem shiftReturned_executionEnv (q : State) (src dest loadReturn
    storeReturn : Nat) (context : List UInt256) :
    (shiftReturned q src dest loadReturn storeReturn context).executionEnv =
      q.executionEnv := by
  rfl

@[simp] theorem shiftReturned_halt (q : State) (src dest loadReturn
    storeReturn : Nat) (context : List UInt256) :
    (shiftReturned q src dest loadReturn storeReturn context).halt = q.halt := by
  rfl

@[simp] theorem shiftReturned_callStack (q : State) (src dest loadReturn
    storeReturn : Nat) (context : List UInt256) :
    (shiftReturned q src dest loadReturn storeReturn context).callStack =
      q.callStack := by
  rfl

@[simp] theorem directStored_executionEnv (q : State) (offset : Nat)
    (value : UInt256) (nextPC : Nat) (context : List UInt256) :
    (directStored q offset value nextPC context).executionEnv =
      q.executionEnv := by
  rfl

@[simp] theorem directStored_halt (q : State) (offset : Nat)
    (value : UInt256) (nextPC : Nat) (context : List UInt256) :
    (directStored q offset value nextPC context).halt = q.halt := by
  rfl

@[simp] theorem directStored_callStack (q : State) (offset : Nat)
    (value : UInt256) (nextPC : Nat) (context : List UInt256) :
    (directStored q offset value nextPC context).callStack = q.callStack := by
  rfl

@[simp] theorem afterSchedule_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) :
    (afterSchedule s msgOff returnDest rest).executionEnv = s.executionEnv := by
  simp only [afterSchedule, Schedule.scheduleResult, Schedule.scheduleReturned,
    Schedule.secondLoopState_executionEnv,
    Schedule.firstLoopState_executionEnv]

@[simp] theorem afterSchedule_halt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) :
    (afterSchedule s msgOff returnDest rest).halt = s.halt := by
  simp only [afterSchedule, Schedule.scheduleResult, Schedule.scheduleReturned,
    Schedule.secondLoopState_halt, Schedule.firstLoopState_halt]

@[simp] theorem afterSchedule_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) :
    (afterSchedule s msgOff returnDest rest).callStack = s.callStack := by
  simp only [afterSchedule, Schedule.scheduleResult, Schedule.scheduleReturned,
    Schedule.secondLoopState_callStack, Schedule.firstLoopState_callStack]

@[simp] theorem copyHashState_executionEnv (s : State) :
    (copyHashState s).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem copyHashState_halt (s : State) :
    (copyHashState s).halt = s.halt := by
  rfl

@[simp] theorem copyHashState_callStack (s : State) :
    (copyHashState s).callStack = s.callStack := by
  rfl

def gasSteps_entry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (compressEntry s msgOff returnDest rest)
      (callSchedule s msgOff returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka entryPath
  · exact hcode
  · exact hfork
  · exact run_entry s msgOff returnDest rest (by omega) hcode hrun
  · exact hrun
  · exact hnp

def scheduleCallStackCap (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988) :
    (msgOff :: returnDest :: rest).length < 990 := by
  simp
  omega

def scheduleCallReturnValid :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 621).toNat = true := by
  decide

def gasSteps_toRoundLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (compressEntry s msgOff returnDest rest)
      (roundAt (copyHashState (afterSchedule s msgOff returnDest rest))
        msgOff returnDest rest 0) := by
  have gEntry := gasSteps_entry s msgOff returnDest rest hcap
    hcode hfork hrun hnp
  have gSchedule := Schedule.gasSteps_schedule s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest)
    (scheduleCallStackCap msgOff returnDest rest hcap) hcode hfork hrun hnp
    scheduleCallReturnValid
  let q := afterSchedule s msgOff returnDest rest
  have qenv : q.executionEnv = s.executionEnv := by
    simp only [q, afterSchedule, Schedule.scheduleResult,
      Schedule.scheduleReturned, Schedule.secondLoopState_executionEnv,
      Schedule.firstLoopState_executionEnv]
  have qhalt : q.halt = s.halt := by
    simp only [q, afterSchedule, Schedule.scheduleResult,
      Schedule.scheduleReturned, Schedule.secondLoopState_halt,
      Schedule.firstLoopState_halt]
  have qcode : q.executionEnv.code = submissionBytecode := by
    rw [qenv]
    exact hcode
  have qfork : q.fork = .Osaka := by
    simpa only [State.fork, qenv] using hfork
  have qrun : q.halt = .Running := by
    rw [qhalt]
    exact hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa only [qenv] using hnp
  have qpc : q.pc = UInt256.ofNat 621 := by
    simp only [q, afterSchedule, Schedule.scheduleResult,
      Schedule.scheduleReturned]
  have qstack : q.stack = [msgOff, returnDest] ++ rest := by
    simp only [q, afterSchedule, Schedule.scheduleResult,
      Schedule.scheduleReturned]
    rfl
  have qentry :
      ({ q with pc := UInt256.ofNat 621
                stack := [msgOff, returnDest] ++ rest } : State) = q := by
    rw [← qpc, ← qstack]
  have gCopyRaw : Challenge.EvmProof.GasSteps
      { q with pc := UInt256.ofNat 621
               stack := [msgOff, returnDest] ++ rest }
      (roundAt (copyHashState q) msgOff returnDest rest 0) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka copyAndLoopStartPath
    · rw [qentry]
      exact qcode
    · rw [qentry]
      exact qfork
    · exact run_copyAndLoopStart q msgOff returnDest rest (by omega) qrun
    · rw [qentry]
      exact qrun
    · rw [qentry]
      exact qnp
  have gCopy : Challenge.EvmProof.GasSteps q
      (roundAt (copyHashState q) msgOff returnDest rest 0) :=
    Challenge.EvmProof.GasSteps.cast gCopyRaw qentry rfl
  exact gEntry.trans (gSchedule.trans gCopy)

@[simp] theorem gasSteps_toRoundLoop_cost (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    let q := afterSchedule s msgOff returnDest rest
    (gasSteps_toRoundLoop s msgOff returnDest rest hcap hcode hfork hrun hnp).cost =
      (gasSteps_entry s msgOff returnDest rest hcap hcode hfork hrun hnp).cost +
      (Schedule.gasSteps_scheduleCost s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest)
        (scheduleCallStackCap msgOff returnDest rest hcap)
        hcode hfork hrun hnp scheduleCallReturnValid +
      Challenge.EvmProof.Stepper.runLocatedBlockCost copyAndLoopStartPath
        { q with pc := UInt256.ofNat 621
                 stack := [msgOff, returnDest] ++ rest }) := by
  simp only [Schedule.gasSteps_scheduleCost, gasSteps_toRoundLoop,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]

def gasSteps_condition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (roundAt s msgOff returnDest rest j)
      (afterCondition s msgOff returnDest rest j) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka conditionPath
  · exact hcode
  · exact hfork
  · exact run_condition s msgOff returnDest rest j hj hcap hrun
  · exact hrun
  · exact hnp

/- Superseded standalone Ch/Maj composition. -/
/-
/-- Execute the round condition and the complete `t1` half of one compression
round.  The result is the exact stack expected by the compiler's `t2` code. -/
def gasSteps_t1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (roundAt s msgOff returnDest rest j)
      (afterT1 s msgOff returnDest rest j) := by
  have gCond := gasSteps_condition s msgOff returnDest rest j hj (by omega)
    hcode hfork hrun hnp
  have gSetupW : Challenge.EvmProof.GasSteps
      (afterCondition s msgOff returnDest rest j)
      (gotW s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupWPath
    · exact hcode
    · exact hfork
    · exact run_setupW s msgOff returnDest rest j (by omega) hrun
    · exact hrun
    · exact hnp
  have qWcode : (gotW s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotW, loadedE, Accessors.loadReturned] using hcode
  have qWfork : (gotW s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotW, loadedE, Accessors.loadReturned, State.fork] using hfork
  have qWrun : (gotW s msgOff returnDest rest j).halt = .Running := by
    simpa [gotW, loadedE, Accessors.loadReturned] using hrun
  have qWnp : Precompile.isPrecompileWithConfig (gotW s msgOff returnDest rest j).executionEnv.precompileConfig (gotW s msgOff returnDest rest j).executionEnv.fork
      (gotW s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotW, loadedE, Accessors.loadReturned] using hnp
  have gSetupK : Challenge.EvmProof.GasSteps
      (gotW s msgOff returnDest rest j) (gotK s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupKPath
    · exact qWcode
    · exact qWfork
    · exact run_setupK s msgOff returnDest rest j hj (by omega) hrun
    · exact qWrun
    · exact qWnp
  have qKcode : (gotK s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned] using hcode
  have qKfork : (gotK s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned, State.fork] using hfork
  have qKrun : (gotK s msgOff returnDest rest j).halt = .Running := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned] using hrun
  have qKnp : Precompile.isPrecompileWithConfig (gotK s msgOff returnDest rest j).executionEnv.precompileConfig (gotK s msgOff returnDest rest j).executionEnv.fork
      (gotK s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned] using hnp
  have gSetupH6 : Challenge.EvmProof.GasSteps
      (gotK s msgOff returnDest rest j) (gotH6 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupH6Path
    · exact qKcode
    · exact qKfork
    · exact run_setupH6 s msgOff returnDest rest j (by omega) hrun
    · exact qKrun
    · exact qKnp
  have qH6code : (gotH6 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode
  have qH6fork : (gotH6 s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork
  have qH6run : (gotH6 s msgOff returnDest rest j).halt = .Running := by
    simpa [gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun
  have qH6np : Precompile.isPrecompileWithConfig (gotH6 s msgOff returnDest rest j).executionEnv.precompileConfig (gotH6 s msgOff returnDest rest j).executionEnv.fork
      (gotH6 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp
  have gSetupH5 : Challenge.EvmProof.GasSteps
      (gotH6 s msgOff returnDest rest j) (gotH5 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupH5Path
    · exact qH6code
    · exact qH6fork
    · exact run_setupH5 s msgOff returnDest rest j (by omega) hrun
    · exact qH6run
    · exact qH6np
  have qH5code : (gotH5 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotH5, gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode
  have qH5fork : (gotH5 s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotH5, gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork
  have qH5run : (gotH5 s msgOff returnDest rest j).halt = .Running := by
    simpa [gotH5, gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun
  have qH5np : Precompile.isPrecompileWithConfig (gotH5 s msgOff returnDest rest j).executionEnv.precompileConfig (gotH5 s msgOff returnDest rest j).executionEnv.fork
      (gotH5 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotH5, gotH6, gotK, gotW, loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp
  have gSetupCh : Challenge.EvmProof.GasSteps
      (gotH5 s msgOff returnDest rest j) (callCh s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupChPath
    · exact qH5code
    · exact qH5fork
    · exact run_setupCh s msgOff returnDest rest j (by omega) hcode hrun
    · exact qH5run
    · exact qH5np
  have gCh := Functions.gasSteps_ch (gotH5 s msgOff returnDest rest j)
    (hValue s 4) (hValue s 5) (hValue s 6) 0 (UInt256.ofNat 703)
    ([kValue s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) qH5code qH5fork qH5run qH5np (by decide)
  have qChcode : (gotCh s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotCh, gotH5, gotH6, gotK, gotW, loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode
  have qChfork : (gotCh s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotCh, gotH5, gotH6, gotK, gotW, loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork
  have qChrun : (gotCh s msgOff returnDest rest j).halt = .Running := by
    simpa [gotCh, gotH5, gotH6, gotK, gotW, loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun
  have qChnp : Precompile.isPrecompileWithConfig (gotCh s msgOff returnDest rest j).executionEnv.precompileConfig (gotCh s msgOff returnDest rest j).executionEnv.fork
      (gotCh s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotCh, gotH5, gotH6, gotK, gotW, loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp
  have gSetupB1 : Challenge.EvmProof.GasSteps
      (gotCh s msgOff returnDest rest j)
      (callBigSigma1 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupBigSigma1Path
    · exact qChcode
    · exact qChfork
    · exact run_setupBigSigma1 s msgOff returnDest rest j (by omega)
        hcode hrun
    · exact qChrun
    · exact qChnp
  have gB1 : Challenge.EvmProof.GasSteps
      (callBigSigma1 s msgOff returnDest rest j)
      (gotFusedT1 s msgOff returnDest rest j) := by
    exact Challenge.EvmProof.GasSteps.cast
      (BigSigma.gasSteps_bigSigma1 (gotCh s msgOff returnDest rest j)
        (hValue s 4) (chPlusK s j) (wValue s j)
        ([hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
        (by simp; omega) qChcode qChfork qChrun qChnp)
      (by rfl) (by rfl)
  have qB1code : (gotFusedT1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotFusedT1, BigSigma.t1Returned, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode
  have qB1fork : (gotFusedT1 s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotFusedT1, BigSigma.t1Returned, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork
  have qB1run : (gotFusedT1 s msgOff returnDest rest j).halt = .Running := by
    simpa [gotFusedT1, BigSigma.t1Returned, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun
  have qB1np : Precompile.isPrecompileWithConfig
      (gotFusedT1 s msgOff returnDest rest j).executionEnv.precompileConfig
      (gotFusedT1 s msgOff returnDest rest j).executionEnv.fork
      (gotFusedT1 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotFusedT1, BigSigma.t1Returned, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp
  have gFinish : Challenge.EvmProof.GasSteps
      (gotFusedT1 s msgOff returnDest rest j)
      (afterT1 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka finishT1Path
    · exact qB1code
    · exact qB1fork
    · exact run_finishT1 s msgOff returnDest rest j (by omega) hrun
    · exact qB1run
    · exact qB1np
  exact gCond.trans (gSetupW.trans
    (gSetupK.trans (gSetupH6.trans
      (gSetupH5.trans (gSetupCh.trans (gCh.trans
        (gSetupB1.trans (gB1.trans gFinish))))))))

/-- Execute the complete `t2` half, leaving the eight working-state updates
as the only remaining part of the round. -/
def gasSteps_t2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterT1 s msgOff returnDest rest j)
      (afterT2 s msgOff returnDest rest j) := by
  have qT1code : (afterT1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [afterT1, gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode
  have qT1fork : (afterT1 s msgOff returnDest rest j).fork = .Osaka := by
    simpa [afterT1, gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork
  have qT1run : (afterT1 s msgOff returnDest rest j).halt = .Running := by
    simpa [afterT1, gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun
  have qT1np : Precompile.isPrecompileWithConfig (afterT1 s msgOff returnDest rest j).executionEnv.precompileConfig (afterT1 s msgOff returnDest rest j).executionEnv.fork
      (afterT1 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [afterT1, gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp
  have gSetupH2 : Challenge.EvmProof.GasSteps
      (afterT1 s msgOff returnDest rest j)
      (gotT2H2 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupT2H2Path
    · exact qT1code
    · exact qT1fork
    · exact run_setupT2H2 s msgOff returnDest rest j (by omega) hrun
    · exact qT1run
    · exact qT1np
  have qH2code : (gotT2H2 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    change (afterT1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode
    exact qT1code
  have qH2fork : (gotT2H2 s msgOff returnDest rest j).fork = .Osaka := by
    change (afterT1 s msgOff returnDest rest j).fork = .Osaka
    exact qT1fork
  have qH2run : (gotT2H2 s msgOff returnDest rest j).halt = .Running := by
    change (afterT1 s msgOff returnDest rest j).halt = .Running
    exact qT1run
  have qH2np : Precompile.isPrecompileWithConfig (gotT2H2 s msgOff returnDest rest j).executionEnv.precompileConfig (gotT2H2 s msgOff returnDest rest j).executionEnv.fork
      (gotT2H2 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig (afterT1 s msgOff returnDest rest j).executionEnv.precompileConfig (afterT1 s msgOff returnDest rest j).executionEnv.fork
      (afterT1 s msgOff returnDest rest j).executionEnv.codeAddr = false
    exact qT1np
  have gSetupH1 : Challenge.EvmProof.GasSteps
      (gotT2H2 s msgOff returnDest rest j)
      (gotT2H1 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupT2H1Path
    · exact qH2code
    · exact qH2fork
    · exact run_setupT2H1 s msgOff returnDest rest j (by omega) hrun
    · exact qH2run
    · exact qH2np
  have qH1code : (gotT2H1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    change (afterT1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode
    exact qT1code
  have qH1fork : (gotT2H1 s msgOff returnDest rest j).fork = .Osaka := by
    change (afterT1 s msgOff returnDest rest j).fork = .Osaka
    exact qT1fork
  have qH1run : (gotT2H1 s msgOff returnDest rest j).halt = .Running := by
    change (afterT1 s msgOff returnDest rest j).halt = .Running
    exact qT1run
  have qH1np : Precompile.isPrecompileWithConfig (gotT2H1 s msgOff returnDest rest j).executionEnv.precompileConfig (gotT2H1 s msgOff returnDest rest j).executionEnv.fork
      (gotT2H1 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig (afterT1 s msgOff returnDest rest j).executionEnv.precompileConfig (afterT1 s msgOff returnDest rest j).executionEnv.fork
      (afterT1 s msgOff returnDest rest j).executionEnv.codeAddr = false
    exact qT1np
  have gSetupMaj : Challenge.EvmProof.GasSteps
      (gotT2H1 s msgOff returnDest rest j)
      (callMaj s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupMajPath
    · exact qH1code
    · exact qH1fork
    · exact run_setupMaj s msgOff returnDest rest j (by omega) hcode hrun
    · exact qH1run
    · exact qH1np
  have gMaj := Functions.gasSteps_maj (gotT2H1 s msgOff returnDest rest j)
    (hValue s 0) (hValue s 1) (hValue s 2) 0 (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) qH1code qH1fork qH1run qH1np (by decide)
  have qMajcode : (gotMaj s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    change (afterT1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode
    exact qT1code
  have qMajfork : (gotMaj s msgOff returnDest rest j).fork = .Osaka := by
    change (afterT1 s msgOff returnDest rest j).fork = .Osaka
    exact qT1fork
  have qMajrun : (gotMaj s msgOff returnDest rest j).halt = .Running := by
    change (afterT1 s msgOff returnDest rest j).halt = .Running
    exact qT1run
  have qMajnp : Precompile.isPrecompileWithConfig (gotMaj s msgOff returnDest rest j).executionEnv.precompileConfig (gotMaj s msgOff returnDest rest j).executionEnv.fork
      (gotMaj s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig (afterT1 s msgOff returnDest rest j).executionEnv.precompileConfig (afterT1 s msgOff returnDest rest j).executionEnv.fork
      (afterT1 s msgOff returnDest rest j).executionEnv.codeAddr = false
    exact qT1np
  have gSetupB0 : Challenge.EvmProof.GasSteps
      (gotMaj s msgOff returnDest rest j)
      (callBigSigma0 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupBigSigma0Path
    · exact qMajcode
    · exact qMajfork
    · exact run_setupBigSigma0 s msgOff returnDest rest j (by omega)
        hcode hrun
    · exact qMajrun
    · exact qMajnp
  have gB0 : Challenge.EvmProof.GasSteps
      (callBigSigma0 s msgOff returnDest rest j)
      (afterT2 s msgOff returnDest rest j) := by
    simpa [callBigSigma0, afterT2, t2, gotBigSigma0, BigSigma.t2Returned,
      Functions.unaryReturned] using
      (BigSigma.gasSteps_bigSigma0
        (gotMaj s msgOff returnDest rest j) (hValue s 0)
        (Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2))
        ([hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
          msgOff, returnDest] ++ rest)
        (by simp; omega) qMajcode qMajfork qMajrun qMajnp)
  exact gSetupH2.trans (gSetupH1.trans
    (gSetupMaj.trans (gMaj.trans (gSetupB0.trans gB0))))

-/

/-- Execute the round condition and the integrated Ch+BSIG1+T1 half. -/
def gasSteps_t1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (roundAt s msgOff returnDest rest j)
      (afterT1 s msgOff returnDest rest j) := by
  have gCond := gasSteps_condition s msgOff returnDest rest j hj (by omega)
    hcode hfork hrun hnp
  have gSetupW : Challenge.EvmProof.GasSteps
      (afterCondition s msgOff returnDest rest j)
      (gotW s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupWPath
    · exact hcode
    · exact hfork
    · exact run_setupW s msgOff returnDest rest j (by omega) hrun
    · exact hrun
    · exact hnp
  have qWcode : (gotW s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotW, loadedE, Accessors.loadReturned] using hcode
  have qWfork : (gotW s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotW, loadedE, Accessors.loadReturned, State.fork] using hfork
  have qWrun : (gotW s msgOff returnDest rest j).halt = .Running := by
    simpa [gotW, loadedE, Accessors.loadReturned] using hrun
  have qWnp : Precompile.isPrecompileWithConfig
      (gotW s msgOff returnDest rest j).executionEnv.precompileConfig
      (gotW s msgOff returnDest rest j).executionEnv.fork
      (gotW s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotW, loadedE, Accessors.loadReturned] using hnp
  have gSetupK : Challenge.EvmProof.GasSteps
      (gotW s msgOff returnDest rest j) (gotK s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupKPath
    · exact qWcode
    · exact qWfork
    · exact run_setupK s msgOff returnDest rest j hj (by omega) hrun
    · exact qWrun
    · exact qWnp
  have qKcode : (gotK s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned] using hcode
  have qKfork : (gotK s msgOff returnDest rest j).fork = .Osaka := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned, State.fork] using hfork
  have qKrun : (gotK s msgOff returnDest rest j).halt = .Running := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned] using hrun
  have qKnp : Precompile.isPrecompileWithConfig
      (gotK s msgOff returnDest rest j).executionEnv.precompileConfig
      (gotK s msgOff returnDest rest j).executionEnv.fork
      (gotK s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [gotK, gotW, loadedE, Accessors.kAtReturned,
      Accessors.loadReturned] using hnp
  have gSetupT1 : Challenge.EvmProof.GasSteps
      (gotK s msgOff returnDest rest j)
      (callIntegratedT1 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupT1Path
    · exact qKcode
    · exact qKfork
    · exact run_setupT1 s msgOff returnDest rest j (by omega) hcode hrun
    · exact qKrun
    · exact qKnp
  have qLcode : (loadedT1Inputs s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [loadedT1Inputs] using qKcode
  have qLfork : (loadedT1Inputs s msgOff returnDest rest j).fork = .Osaka := by
    simpa [loadedT1Inputs, State.fork] using qKfork
  have qLrun : (loadedT1Inputs s msgOff returnDest rest j).halt = .Running := by
    simpa [loadedT1Inputs] using qKrun
  have qLnp : Precompile.isPrecompileWithConfig
      (loadedT1Inputs s msgOff returnDest rest j).executionEnv.precompileConfig
      (loadedT1Inputs s msgOff returnDest rest j).executionEnv.fork
      (loadedT1Inputs s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [loadedT1Inputs] using qKnp
  have gB1 : Challenge.EvmProof.GasSteps
      (callIntegratedT1 s msgOff returnDest rest j)
      (afterT1 s msgOff returnDest rest j) := by
    simpa [callIntegratedT1, afterT1, gotIntegratedT1] using
      (BigSigma.gasSteps_bigSigma1
        (loadedT1Inputs s msgOff returnDest rest j)
        (hValue s 4) (hValue s 5) (hValue s 6) (kValue s j) (wValue s j)
        ([hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
        (by simp; omega) qLcode qLfork qLrun qLnp)
  exact gCond.trans (gSetupW.trans (gSetupK.trans (gSetupT1.trans gB1)))

/-- Execute the integrated Maj+BSIG0+T2 half. -/
def gasSteps_t2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterT1 s msgOff returnDest rest j)
      (afterT2 s msgOff returnDest rest j) := by
  have qT1code : (afterT1 s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [afterT1, gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs,
      gotK, gotW, loadedE, Accessors.loadReturned, Accessors.kAtReturned]
      using hcode
  have qT1fork : (afterT1 s msgOff returnDest rest j).fork = .Osaka := by
    simpa [afterT1, gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs,
      gotK, gotW, loadedE, Accessors.loadReturned, Accessors.kAtReturned,
      State.fork] using hfork
  have qT1run : (afterT1 s msgOff returnDest rest j).halt = .Running := by
    simpa [afterT1, gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs,
      gotK, gotW, loadedE, Accessors.loadReturned, Accessors.kAtReturned]
      using hrun
  have qT1np : Precompile.isPrecompileWithConfig
      (afterT1 s msgOff returnDest rest j).executionEnv.precompileConfig
      (afterT1 s msgOff returnDest rest j).executionEnv.fork
      (afterT1 s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [afterT1, gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs,
      gotK, gotW, loadedE, Accessors.loadReturned, Accessors.kAtReturned]
      using hnp
  have gSetupT2 : Challenge.EvmProof.GasSteps
      (afterT1 s msgOff returnDest rest j)
      (callIntegratedT2 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupT2Path
    · exact qT1code
    · exact qT1fork
    · exact run_setupT2 s msgOff returnDest rest j (by omega) hcode hrun
    · exact qT1run
    · exact qT1np
  have qLcode : (loadedT2Inputs s msgOff returnDest rest j).executionEnv.code =
      submissionBytecode := by
    simpa [loadedT2Inputs] using qT1code
  have qLfork : (loadedT2Inputs s msgOff returnDest rest j).fork = .Osaka := by
    simpa [loadedT2Inputs, State.fork] using qT1fork
  have qLrun : (loadedT2Inputs s msgOff returnDest rest j).halt = .Running := by
    simpa [loadedT2Inputs] using qT1run
  have qLnp : Precompile.isPrecompileWithConfig
      (loadedT2Inputs s msgOff returnDest rest j).executionEnv.precompileConfig
      (loadedT2Inputs s msgOff returnDest rest j).executionEnv.fork
      (loadedT2Inputs s msgOff returnDest rest j).executionEnv.codeAddr = false := by
    simpa [loadedT2Inputs] using qT1np
  have gB0 : Challenge.EvmProof.GasSteps
      (callIntegratedT2 s msgOff returnDest rest j)
      (afterT2 s msgOff returnDest rest j) := by
    simpa [callIntegratedT2, afterT2] using
      (BigSigma.gasSteps_bigSigma0
        (loadedT2Inputs s msgOff returnDest rest j)
        (hValue s 0) (hValue s 1) (hValue s 2)
        ([hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
          msgOff, returnDest] ++ rest)
        (by simp; omega) qLcode qLfork qLrun qLnp)
  exact gSetupT2.trans gB0

@[simp] theorem afterT2_executionEnv (s : State) (msgOff returnDest : UInt256)
  (rest : List UInt256) (j : Nat) :
    (afterT2 s msgOff returnDest rest j).executionEnv = s.executionEnv := by
  simp [afterT2, loadedT2Inputs, BigSigma.t2Returned, afterT1,
    gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs, gotK, gotW,
    loadedE, Accessors.loadReturned, Accessors.kAtReturned]

@[simp] theorem afterT2_halt (s : State) (msgOff returnDest : UInt256)
  (rest : List UInt256) (j : Nat) :
    (afterT2 s msgOff returnDest rest j).halt = s.halt := by
  simp [afterT2, loadedT2Inputs, BigSigma.t2Returned, afterT1,
    gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs, gotK, gotW,
    loadedE, Accessors.loadReturned, Accessors.kAtReturned]

@[simp] theorem afterT2_callStack (s : State) (msgOff returnDest : UInt256)
  (rest : List UInt256) (j : Nat) :
    (afterT2 s msgOff returnDest rest j).callStack = s.callStack := by
  simp [afterT2, loadedT2Inputs, BigSigma.t2Returned, afterT1,
    gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs, gotK, gotW,
    loadedE, Accessors.loadReturned, Accessors.kAtReturned]

def gasSteps_shift (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (q : State) (src dest loadReturn storeReturn startPC : Nat)
    (context : List UInt256)
    (hmatch :
      (path = shift76Path ∧ src = 6 ∧ dest = 7 ∧ loadReturn = 796 ∧
        storeReturn = 803 ∧ startPC = 783) ∨
      (path = shift65Path ∧ src = 5 ∧ dest = 6 ∧ loadReturn = 817 ∧
        storeReturn = 824 ∧ startPC = 803) ∨
      (path = shift32Path ∧ src = 2 ∧ dest = 3 ∧ loadReturn = 872 ∧
        storeReturn = 879 ∧ startPC = 858) ∨
      (path = shift21Path ∧ src = 1 ∧ dest = 2 ∧ loadReturn = 893 ∧
        storeReturn = 900 ∧ startPC = 879))
    (hpc : q.pc = UInt256.ofNat startPC) (hstack : q.stack = context)
    (hcap : context.length < 1016)
    (hcode : q.executionEnv.code = submissionBytecode)
    (hfork : q.fork = .Osaka) (hrun : q.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps q
      (shiftReturned q src dest loadReturn storeReturn context) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact run_shiftDirect path q src dest loadReturn storeReturn startPC
      context hmatch hpc hstack (by omega) hrun
  · exact hrun
  · exact hnp

/-- Perform all eight working-state assignments and jump back to the round
condition with `j + 1`. -/
def gasSteps_updates (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterT2 s msgOff returnDest rest j)
      (afterSecondIteration s msgOff returnDest rest j) := by
  let ctx := roundContext s msgOff returnDest rest j
  let q0 := afterT2 s msgOff returnDest rest j
  have hctx : ctx.length < 1016 := by simp [ctx, roundContext]; omega
  have q0env : q0.executionEnv = s.executionEnv := by
    simp only [q0, afterT2_executionEnv]
  have q0halt : q0.halt = s.halt := by
    simp only [q0, afterT2_halt]
  have q0code : q0.executionEnv.code = submissionBytecode := by
    rw [q0env]
    exact hcode
  have q0fork : q0.fork = .Osaka := by
    simpa only [State.fork, q0env] using hfork
  have q0run : q0.halt = .Running := by
    rw [q0halt]
    exact hrun
  have q0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by
    simpa only [q0env] using hnp
  have g7 := gasSteps_shift shift76Path q0 6 7 796 803 783 ctx
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by rfl) (by rfl) hctx q0code q0fork q0run q0np
  let q1 := afterShift7 s msgOff returnDest rest j
  have q1eq : q1 = shiftReturned q0 6 7 796 803 ctx := by rfl
  have q1code : q1.executionEnv.code = submissionBytecode := by
    change q0.executionEnv.code = submissionBytecode
    exact q0code
  have q1fork : q1.fork = .Osaka := by
    change q0.fork = .Osaka
    exact q0fork
  have q1run : q1.halt = .Running := by
    change q0.halt = .Running
    exact q0run
  have q1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false
    exact q0np
  have g6 := gasSteps_shift shift65Path q1 5 6 817 824 803 ctx
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))
    (by rfl) (by rfl) hctx q1code q1fork q1run q1np
  let q2 := afterShift6 s msgOff returnDest rest j
  have q2eq : q2 = shiftReturned q1 5 6 817 824 ctx := by rfl
  have q2code : q2.executionEnv.code = submissionBytecode := by
    change q1.executionEnv.code = submissionBytecode
    exact q1code
  have q2fork : q2.fork = .Osaka := by
    change q1.fork = .Osaka
    exact q1fork
  have q2run : q2.halt = .Running := by
    change q1.halt = .Running
    exact q1run
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false
    exact q1np
  have gE : Challenge.EvmProof.GasSteps q2
      (afterStoreE s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka storeEPath
    · exact q2code
    · exact q2fork
    · simpa [q2] using run_storeE s msgOff returnDest rest j
        (by omega) hrun
    · exact q2run
    · exact q2np
  let q3 := afterStoreE s msgOff returnDest rest j
  have q3code : q3.executionEnv.code = submissionBytecode := by
    change q2.executionEnv.code = submissionBytecode
    exact q2code
  have q3fork : q3.fork = .Osaka := by
    change q2.fork = .Osaka
    exact q2fork
  have q3run : q3.halt = .Running := by
    change q2.halt = .Running
    exact q2run
  have q3np : Precompile.isPrecompileWithConfig q3.executionEnv.precompileConfig q3.executionEnv.fork
      q3.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false
    exact q2np
  have gH4 : Challenge.EvmProof.GasSteps q3
      (afterStoreH4 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupH3ForH4Path
    · exact q3code
    · exact q3fork
    · simpa [q3] using run_updateH4 s msgOff returnDest rest j
        (by omega) hrun
    · exact q3run
    · exact q3np
  let q4 := afterStoreH4 s msgOff returnDest rest j
  have q4code : q4.executionEnv.code = submissionBytecode := by
    change q3.executionEnv.code = submissionBytecode
    exact q3code
  have q4fork : q4.fork = .Osaka := by
    change q3.fork = .Osaka
    exact q3fork
  have q4run : q4.halt = .Running := by
    change q3.halt = .Running
    exact q3run
  have q4np : Precompile.isPrecompileWithConfig q4.executionEnv.precompileConfig q4.executionEnv.fork
      q4.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig q3.executionEnv.precompileConfig
      q3.executionEnv.fork q3.executionEnv.codeAddr = false
    exact q3np
  have g3 := gasSteps_shift shift32Path q4 2 3 872 879 858 ctx
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))
    (by rfl) (by rfl) hctx q4code q4fork q4run q4np
  let q5 := shiftReturned q4 2 3 872 879 ctx
  have q5env : q5.executionEnv = q4.executionEnv := by
    simp only [q5, shiftReturned_executionEnv]
  have q5halt : q5.halt = q4.halt := by
    simp only [q5, shiftReturned_halt]
  have q5code : q5.executionEnv.code = submissionBytecode := by
    rw [q5env]
    exact q4code
  have q5fork : q5.fork = .Osaka := by
    simpa only [State.fork, q5env] using q4fork
  have q5run : q5.halt = .Running := by
    rw [q5halt]
    exact q4run
  have q5np : Precompile.isPrecompileWithConfig q5.executionEnv.precompileConfig q5.executionEnv.fork
      q5.executionEnv.codeAddr = false := by
    simpa only [q5env] using q4np
  have g2 := gasSteps_shift shift21Path q5 1 2 893 900 879 ctx
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))
    (by rfl) (by rfl) hctx q5code q5fork q5run q5np
  let q6 := shiftReturned q5 1 2 893 900 ctx
  have q6env : q6.executionEnv = q5.executionEnv := by
    simp only [q6, shiftReturned_executionEnv]
  have q6halt : q6.halt = q5.halt := by
    simp only [q6, shiftReturned_halt]
  have q6code : q6.executionEnv.code = submissionBytecode := by
    rw [q6env]
    exact q5code
  have q6fork : q6.fork = .Osaka := by
    simpa only [State.fork, q6env] using q5fork
  have q6run : q6.halt = .Running := by
    rw [q6halt]
    exact q5run
  have q6np : Precompile.isPrecompileWithConfig q6.executionEnv.precompileConfig q6.executionEnv.fork
      q6.executionEnv.codeAddr = false := by
    simpa only [q6env] using q5np
  have q6eq : q6 = afterShift2 s msgOff returnDest rest j := by rfl
  have gFinish : Challenge.EvmProof.GasSteps q6
      (afterSecondIteration s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka finishRoundPath
    · exact q6code
    · exact q6fork
    · rw [q6eq]
      exact run_finishRound s msgOff returnDest rest j hj
        (by omega) hcode hrun
    · exact q6run
    · exact q6np
  exact g7.trans (g6.trans (gE.trans
    (gH4.trans (g3.trans (g2.trans gFinish)))))

/-- One complete concrete compression round, including the loop branch,
arithmetic, all eight memory updates, and the back edge. -/
def gasSteps_roundIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (roundAt s msgOff returnDest rest j)
      (afterSecondIteration s msgOff returnDest rest j) :=
  (gasSteps_t1 s msgOff returnDest rest j hj hcap hcode hfork hrun hnp).trans
    ((gasSteps_t2 s msgOff returnDest rest j hcap hcode hfork hrun hnp).trans
      (gasSteps_updates s msgOff returnDest rest j hj hcap
        hcode hfork hrun hnp))

def roundLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => roundAt s msgOff returnDest rest 0
  | n + 1 => afterSecondIteration
      (roundLoopState s msgOff returnDest rest n)
      msgOff returnDest rest n

@[simp] theorem afterSecondIteration_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (afterSecondIteration s msgOff returnDest rest j).executionEnv =
      s.executionEnv := by
  simp only [afterSecondIteration, afterStoreH1,
    directStored_executionEnv, afterShift2, shiftReturned_executionEnv,
    afterShift3, afterStoreH4, Accessors.storeReturned, h4Loaded,
    Accessors.loadReturned, afterStoreE, afterShift6, afterShift7,
    afterT2_executionEnv]

@[simp] theorem afterSecondIteration_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (afterSecondIteration s msgOff returnDest rest j).halt = s.halt := by
  simp only [afterSecondIteration, afterStoreH1, directStored_halt,
    afterShift2, shiftReturned_halt, afterShift3, afterStoreH4,
    Accessors.storeReturned, h4Loaded, Accessors.loadReturned, afterStoreE,
    afterShift6, afterShift7, afterT2_halt]

@[simp] theorem afterSecondIteration_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (afterSecondIteration s msgOff returnDest rest j).callStack =
      s.callStack := by
  simp only [afterSecondIteration, afterStoreH1, directStored_callStack,
    afterShift2, shiftReturned_callStack, afterShift3, afterStoreH4,
    Accessors.storeReturned, h4Loaded, Accessors.loadReturned, afterStoreE,
    afterShift6, afterShift7, afterT2_callStack]

@[simp] theorem roundLoopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (roundLoopState s msgOff returnDest rest n).executionEnv =
      s.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simp [roundLoopState, ih]

@[simp] theorem roundLoopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (roundLoopState s msgOff returnDest rest n).halt = s.halt := by
  induction n with
  | zero => rfl
  | succ n ih => simp [roundLoopState, ih]

@[simp] theorem roundLoopState_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (roundLoopState s msgOff returnDest rest n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih => simp [roundLoopState, ih]

@[simp] theorem roundAt_roundLoopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    roundAt (roundLoopState s msgOff returnDest rest n)
      msgOff returnDest rest n = roundLoopState s msgOff returnDest rest n := by
  cases n <;> simp [roundLoopState, afterSecondIteration, roundAt]

def gasSteps_roundLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (roundLoopState s msgOff returnDest rest 0)
      (roundLoopState s msgOff returnDest rest 64) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 64)
  intro n hn
  let q := roundLoopState s msgOff returnDest rest n
  have qcode : q.executionEnv.code = submissionBytecode := by
    simpa [q] using hcode
  have qfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by
    simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have g := gasSteps_roundIteration q msgOff returnDest rest n hn hcap
    qcode qfork qrun qnp
  have hs : roundAt q msgOff returnDest rest n =
      roundLoopState s msgOff returnDest rest n := by
    simp [q]
  have ht : afterSecondIteration q msgOff returnDest rest n =
      roundLoopState s msgOff returnDest rest (n + 1) := by
    simp [q, roundLoopState]
  exact Challenge.EvmProof.GasSteps.cast g hs ht

def gasSteps_roundsExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (roundAt s msgOff returnDest rest 64)
      (foldAt s msgOff returnDest rest 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka roundsExitPath
  · exact hcode
  · exact hfork
  · exact run_roundsExit s msgOff returnDest rest hcap hcode hrun
  · exact hrun
  · exact hnp

def gasSteps_foldIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 8)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (foldAt s msgOff returnDest rest i)
      (afterFoldIteration s msgOff returnDest rest i) := by
  have gCond : Challenge.EvmProof.GasSteps
      (foldAt s msgOff returnDest rest i)
      (afterFoldCondition s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka foldConditionPath
    · exact hcode
    · exact hfork
    · exact run_foldCondition s msgOff returnDest rest i hi
        (by omega) hrun
    · exact hrun
    · exact hnp
  have gSetup : Challenge.EvmProof.GasSteps
      (afterFoldCondition s msgOff returnDest rest i)
      (foldGotSet s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka foldSetupPath
    · exact hcode
    · exact hfork
    · exact run_foldSetup s msgOff returnDest rest i (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have qSetCode : (foldGotSet s msgOff returnDest rest i).executionEnv.code =
      submissionBytecode := by
    simpa [foldGotSet, foldGotH, loadedSaved, Accessors.storeReturned,
      Accessors.loadReturned] using hcode
  have qSetFork : (foldGotSet s msgOff returnDest rest i).fork = .Osaka := by
    simpa [foldGotSet, foldGotH, loadedSaved, Accessors.storeReturned,
      Accessors.loadReturned, State.fork] using hfork
  have qSetRun : (foldGotSet s msgOff returnDest rest i).halt = .Running := by
    simpa [foldGotSet, foldGotH, loadedSaved, Accessors.storeReturned,
      Accessors.loadReturned] using hrun
  have qSetNp : Precompile.isPrecompileWithConfig (foldGotSet s msgOff returnDest rest i).executionEnv.precompileConfig (foldGotSet s msgOff returnDest rest i).executionEnv.fork
      (foldGotSet s msgOff returnDest rest i).executionEnv.codeAddr = false := by
    simpa [foldGotSet, foldGotH, loadedSaved, Accessors.storeReturned,
      Accessors.loadReturned] using hnp
  have gInc : Challenge.EvmProof.GasSteps
      (foldGotSet s msgOff returnDest rest i)
      (afterFoldIteration s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka foldIncrementPath
    · exact qSetCode
    · exact qSetFork
    · exact run_foldIncrement s msgOff returnDest rest i hi (by omega)
        hcode hrun
    · exact qSetRun
    · exact qSetNp
  exact gCond.trans (gSetup.trans gInc)

def foldLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => foldAt s msgOff returnDest rest 0
  | n + 1 => afterFoldIteration (foldLoopState s msgOff returnDest rest n)
      msgOff returnDest rest n

@[simp] theorem afterFoldIteration_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (afterFoldIteration s msgOff returnDest rest i).executionEnv =
      s.executionEnv := by
  rfl

@[simp] theorem afterFoldIteration_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (afterFoldIteration s msgOff returnDest rest i).halt = s.halt := by
  rfl

@[simp] theorem afterFoldIteration_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (afterFoldIteration s msgOff returnDest rest i).callStack =
      s.callStack := by
  rfl

@[simp] theorem foldLoopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (foldLoopState s msgOff returnDest rest n).executionEnv =
      s.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldLoopState, ih]

@[simp] theorem foldLoopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (foldLoopState s msgOff returnDest rest n).halt = s.halt := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldLoopState, ih]

@[simp] theorem foldLoopState_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (foldLoopState s msgOff returnDest rest n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldLoopState, ih]

@[simp] theorem foldAt_foldLoopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    foldAt (foldLoopState s msgOff returnDest rest n)
      msgOff returnDest rest n = foldLoopState s msgOff returnDest rest n := by
  cases n <;> simp [foldLoopState, afterFoldIteration, foldAt]

def gasSteps_foldLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (foldLoopState s msgOff returnDest rest 0)
      (foldLoopState s msgOff returnDest rest 8) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
  intro i hi
  let q := foldLoopState s msgOff returnDest rest i
  have qcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have g := gasSteps_foldIteration q msgOff returnDest rest i hi hcap
    qcode qfork qrun qnp
  have hs : foldAt q msgOff returnDest rest i =
      foldLoopState s msgOff returnDest rest i := by
    simp [q]
  have ht : afterFoldIteration q msgOff returnDest rest i =
      foldLoopState s msgOff returnDest rest (i + 1) := by
    simp [q, foldLoopState]
  exact Challenge.EvmProof.GasSteps.cast g hs ht

def gasSteps_foldExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (foldAt s msgOff returnDest rest 8)
      (compressReturned s returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka foldExitPath
  · exact hcode
  · exact hfork
  · exact run_foldExit s msgOff returnDest rest hcap hcode hrun hreturn
  · exact hrun
  · exact hnp

def compressResult (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  let prepared := copyHashState (afterSchedule s msgOff returnDest rest)
  let afterRounds := roundLoopState prepared msgOff returnDest rest 64
  let afterFold := foldLoopState afterRounds msgOff returnDest rest 8
  compressReturned afterFold returnDest rest

@[simp] theorem compressResult_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) :
    (compressResult s msgOff returnDest rest).callStack = s.callStack := by
  simp only [compressResult, compressReturned, foldLoopState_callStack,
    roundLoopState_callStack, copyHashState_callStack,
    afterSchedule_callStack]

/-- Complete direct execution theorem for the reference `compress` bytecode:
schedule construction, saved-state copy, 64 rounds, eight-word feed-forward,
and internal return. -/
def gasSteps_compress (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (compressEntry s msgOff returnDest rest)
      (compressResult s msgOff returnDest rest) := by
  let prepared := copyHashState (afterSchedule s msgOff returnDest rest)
  have gPrepare := gasSteps_toRoundLoop s msgOff returnDest rest hcap
    hcode hfork hrun hnp
  have preparedEnv : prepared.executionEnv = s.executionEnv := by
    simp only [prepared, copyHashState_executionEnv,
      afterSchedule_executionEnv]
  have preparedHalt : prepared.halt = s.halt := by
    simp only [prepared, copyHashState_halt, afterSchedule_halt]
  have preparedCode : prepared.executionEnv.code = submissionBytecode := by
    rw [preparedEnv]
    exact hcode
  have preparedFork : prepared.fork = .Osaka := by
    simpa only [State.fork, preparedEnv] using hfork
  have preparedRun : prepared.halt = .Running := by
    rw [preparedHalt]
    exact hrun
  have preparedNp : Precompile.isPrecompileWithConfig prepared.executionEnv.precompileConfig prepared.executionEnv.fork
      prepared.executionEnv.codeAddr = false := by
    simpa only [preparedEnv] using hnp
  have gRounds := gasSteps_roundLoop prepared msgOff returnDest rest hcap
    preparedCode preparedFork preparedRun preparedNp
  let afterRounds := roundLoopState prepared msgOff returnDest rest 64
  have roundsCode : afterRounds.executionEnv.code = submissionBytecode := by
    simpa [afterRounds] using preparedCode
  have roundsFork : afterRounds.fork = .Osaka := by
    simpa [afterRounds, State.fork] using preparedFork
  have roundsRun : afterRounds.halt = .Running := by
    simpa [afterRounds] using preparedRun
  have roundsNp : Precompile.isPrecompileWithConfig afterRounds.executionEnv.precompileConfig afterRounds.executionEnv.fork
      afterRounds.executionEnv.codeAddr = false := by
    simpa [afterRounds] using preparedNp
  have gRoundsExitRaw := gasSteps_roundsExit afterRounds msgOff returnDest rest
    (by omega) roundsCode roundsFork roundsRun roundsNp
  have roundsExitStart : roundAt afterRounds msgOff returnDest rest 64 =
      afterRounds := by simp [afterRounds]
  have gRoundsExit := Challenge.EvmProof.GasSteps.cast gRoundsExitRaw
    roundsExitStart rfl
  have gFold := gasSteps_foldLoop afterRounds msgOff returnDest rest hcap
    roundsCode roundsFork roundsRun roundsNp
  let afterFold := foldLoopState afterRounds msgOff returnDest rest 8
  have foldCode : afterFold.executionEnv.code = submissionBytecode := by
    simpa [afterFold] using roundsCode
  have foldFork : afterFold.fork = .Osaka := by
    simpa [afterFold, State.fork] using roundsFork
  have foldRun : afterFold.halt = .Running := by
    simpa [afterFold] using roundsRun
  have foldNp : Precompile.isPrecompileWithConfig afterFold.executionEnv.precompileConfig afterFold.executionEnv.fork
      afterFold.executionEnv.codeAddr = false := by
    simpa [afterFold] using roundsNp
  have gReturnRaw := gasSteps_foldExit afterFold msgOff returnDest rest (by omega)
    foldCode foldFork foldRun foldNp hreturn
  have foldExitStart : foldAt afterFold msgOff returnDest rest 8 =
      afterFold := by simp [afterFold]
  have gReturn := Challenge.EvmProof.GasSteps.cast gReturnRaw foldExitStart rfl
  have gAll := gPrepare
    |>.trans gRounds
    |>.trans gRoundsExit
    |>.trans gFold
    |>.trans gReturn
  have resultEq : compressReturned afterFold returnDest rest =
      compressResult s msgOff returnDest rest := by
    rfl
  exact Challenge.EvmProof.GasSteps.cast gAll rfl resultEq

@[simp] theorem gasSteps_compress_cost (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    let prepared := copyHashState (afterSchedule s msgOff returnDest rest)
    let preparedCode : prepared.executionEnv.code = submissionBytecode := by
      simpa [prepared] using hcode
    let preparedFork : prepared.fork = .Osaka := by
      simpa [prepared, State.fork] using hfork
    let preparedRun : prepared.halt = .Running := by
      simpa [prepared] using hrun
    let preparedNp : Precompile.isPrecompileWithConfig prepared.executionEnv.precompileConfig prepared.executionEnv.fork
        prepared.executionEnv.codeAddr = false := by
      simpa [prepared] using hnp
    let afterRounds := roundLoopState prepared msgOff returnDest rest 64
    let roundsCode : afterRounds.executionEnv.code = submissionBytecode := by
      simpa [afterRounds] using preparedCode
    let roundsFork : afterRounds.fork = .Osaka := by
      simpa [afterRounds, State.fork] using preparedFork
    let roundsRun : afterRounds.halt = .Running := by
      simpa [afterRounds] using preparedRun
    let roundsNp : Precompile.isPrecompileWithConfig afterRounds.executionEnv.precompileConfig afterRounds.executionEnv.fork
        afterRounds.executionEnv.codeAddr = false := by
      simpa [afterRounds] using preparedNp
    let afterFold := foldLoopState afterRounds msgOff returnDest rest 8
    let foldCode : afterFold.executionEnv.code = submissionBytecode := by
      simpa [afterFold] using roundsCode
    let foldFork : afterFold.fork = .Osaka := by
      simpa [afterFold, State.fork] using roundsFork
    let foldRun : afterFold.halt = .Running := by
      simpa [afterFold] using roundsRun
    let foldNp : Precompile.isPrecompileWithConfig afterFold.executionEnv.precompileConfig afterFold.executionEnv.fork
        afterFold.executionEnv.codeAddr = false := by
      simpa [afterFold] using roundsNp
    (gasSteps_compress s msgOff returnDest rest hcap hcode hfork hrun hnp
      hreturn).cost =
      ((((gasSteps_toRoundLoop s msgOff returnDest rest hcap hcode hfork hrun
        hnp).cost +
      (gasSteps_roundLoop prepared msgOff returnDest rest hcap preparedCode
        preparedFork preparedRun preparedNp).cost) +
      (gasSteps_roundsExit afterRounds msgOff returnDest rest (by omega)
        roundsCode roundsFork roundsRun roundsNp).cost) +
      (gasSteps_foldLoop afterRounds msgOff returnDest rest hcap roundsCode
        roundsFork roundsRun roundsNp).cost) +
      (gasSteps_foldExit afterFold msgOff returnDest rest (by omega) foldCode
        foldFork foldRun foldNp hreturn).cost := by
  simp only [gasSteps_compress, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost]

end Challenge.Sha256.Submission.Proofs.Bytecode.Compression
