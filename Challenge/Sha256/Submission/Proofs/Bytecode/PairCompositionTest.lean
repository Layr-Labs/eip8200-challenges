import Challenge.Sha256.Submission.Proofs.Bytecode.PairSegmentTest
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.PairCompositionTest

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

def gasStepsPair (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j + 2 ≤ 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Compression.pairAt s msgOff returnDest rest j)
      (Compression.afterPair s msgOff returnDest rest j) := by
  have hj64 : j < 64 := by omega
  have hj1 : j + 1 < 64 := by omega
  have gCond : Challenge.EvmProof.GasSteps
      (Compression.pairAt s msgOff returnDest rest j)
      (Compression.afterPairCondition s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairConditionPath
    · exact hcode
    · exact hfork
    · exact Compression.run_pairCondition s msgOff returnDest rest j hj64
        (by omega) hrun
    · exact hrun
    · exact hnp
  have gSetup10 : Challenge.EvmProof.GasSteps
      (Compression.afterPairCondition s msgOff returnDest rest j)
      (Compression.callPairT10 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairFirstSetupPath
    · exact hcode
    · exact hfork
    · exact PairSegmentTest.runFirstSetup s msgOff returnDest rest j hj64
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have valid717 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 717).toNat = true := by
    decide
  have gT10 : Challenge.EvmProof.GasSteps
      (Compression.callPairT10 s msgOff returnDest rest j)
      (Compression.afterPairT10 s msgOff returnDest rest j) := by
    simpa [Compression.callPairT10, Compression.afterPairT10] using
      (BigSigma.gasSteps_bigSigma1
        (Compression.firstPairInputsLoaded s msgOff returnDest rest j)
        (Compression.hValue s 4) (Compression.hValue s 5)
        (Compression.hValue s 6)
        (Compression.hValue s 7 + Compression.kValue s j)
        (Compression.wValue s j) (UInt256.ofNat 717)
        ([Compression.kValue s j, Compression.wValue s j,
          Compression.hValue s 0, Compression.hValue s 4,
          Compression.hValue s 5, Compression.hValue s 6,
          Compression.hValue s 7, Compression.hValue s 1,
          Compression.hValue s 2, Compression.hValue s 3,
          UInt256.ofNat j, msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid717)
  have gSetup20 : Challenge.EvmProof.GasSteps
      (Compression.afterPairT10 s msgOff returnDest rest j)
      (Compression.callPairT20 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairFirstT2SetupPath
    · exact hcode
    · exact hfork
    · exact PairSegmentTest.runFirstT2Setup s msgOff returnDest rest j
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have valid737 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 737).toNat = true := by
    decide
  have gT20 : Challenge.EvmProof.GasSteps
      (Compression.callPairT20 s msgOff returnDest rest j)
      (Compression.afterPairT20 s msgOff returnDest rest j) := by
    simpa [Compression.callPairT20, Compression.afterPairT20] using
      (BigSigma.gasSteps_bigSigma0
        (Compression.afterPairT10 s msgOff returnDest rest j)
        (Compression.hValue s 0) (Compression.hValue s 1)
        (Compression.hValue s 2) (UInt256.ofNat 737)
        ([Compression.t10 s j, Compression.hValue s 0,
          Compression.hValue s 4, Compression.hValue s 5,
          Compression.hValue s 6, Compression.hValue s 7,
          Compression.hValue s 1, Compression.hValue s 2,
          Compression.hValue s 3, UInt256.ofNat j, msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid737)
  have gSetup11 : Challenge.EvmProof.GasSteps
      (Compression.afterPairT20 s msgOff returnDest rest j)
      (Compression.callPairT11 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairSecondT1SetupPath
    · exact hcode
    · exact hfork
    · exact PairSegmentTest.runSecondT1Setup s msgOff returnDest rest j hj1
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have valid805 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 805).toNat = true := by
    decide
  have gT11 : Challenge.EvmProof.GasSteps
      (Compression.callPairT11 s msgOff returnDest rest j)
      (Compression.afterPairT11 s msgOff returnDest rest j) := by
    simpa [Compression.callPairT11, Compression.afterPairT11] using
      (BigSigma.gasSteps_bigSigma1
        (Compression.secondPairInputsLoaded s msgOff returnDest rest j)
        (Compression.pairE1 s j) (Compression.hValue s 4)
        (Compression.hValue s 5)
        (Compression.hValue s 6 + Compression.kValue s (j + 1))
        (Compression.wValue s (j + 1)) (UInt256.ofNat 805)
        ([Compression.kValue s (j + 1), Compression.wValue s (j + 1),
          Compression.pairA1 s j, Compression.pairE1 s j,
          Compression.hValue s 0, Compression.hValue s 4,
          Compression.hValue s 5, Compression.hValue s 6,
          Compression.hValue s 7, Compression.hValue s 1,
          Compression.hValue s 2, Compression.hValue s 3,
          UInt256.ofNat (j + 1), msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid805)
  have gSetup21 : Challenge.EvmProof.GasSteps
      (Compression.afterPairT11 s msgOff returnDest rest j)
      (Compression.callPairT21 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairSecondT2SetupPath
    · exact hcode
    · exact hfork
    · exact PairSegmentTest.runSecondT2Setup s msgOff returnDest rest j
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have valid825 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 825).toNat = true := by
    decide
  have gT21 : Challenge.EvmProof.GasSteps
      (Compression.callPairT21 s msgOff returnDest rest j)
      (Compression.afterPairT21 s msgOff returnDest rest j) := by
    simpa [Compression.callPairT21, Compression.afterPairT21] using
      (BigSigma.gasSteps_bigSigma0
        (Compression.afterPairT11 s msgOff returnDest rest j)
        (Compression.pairA1 s j) (Compression.hValue s 0)
        (Compression.hValue s 1) (UInt256.ofNat 825)
        ([Compression.t11 s j, Compression.pairA1 s j,
          Compression.pairE1 s j, Compression.hValue s 0,
          Compression.hValue s 4, Compression.hValue s 5,
          Compression.hValue s 6, Compression.hValue s 7,
          Compression.hValue s 1, Compression.hValue s 2,
          Compression.hValue s 3, UInt256.ofNat (j + 1), msgOff,
          returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid825)
  have gCommit : Challenge.EvmProof.GasSteps
      (Compression.afterPairT21 s msgOff returnDest rest j)
      (Compression.afterPair s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairCommitPath
    · exact hcode
    · exact hfork
    · exact PairSegmentTest.runCommit s msgOff returnDest rest j (by omega)
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  exact gCond.trans (gSetup10.trans (gT10.trans (gSetup20.trans
    (gT20.trans (gSetup11.trans (gT11.trans (gSetup21.trans
      (gT21.trans gCommit))))))))

@[simp] private theorem loadedWord_executionEnv (s : State) (offset : Nat) :
    (Compression.loadedWord s offset).executionEnv = s.executionEnv := by rfl

@[simp] private theorem loadedWord_halt (s : State) (offset : Nat) :
    (Compression.loadedWord s offset).halt = s.halt := by rfl

@[simp] private theorem loadedWord_callStack (s : State) (offset : Nat) :
    (Compression.loadedWord s offset).callStack = s.callStack := by rfl

@[simp] private theorem storedWord_executionEnv (s : State) (offset : Nat)
    (value : UInt256) :
    (Compression.storedWord s offset value).executionEnv = s.executionEnv := by rfl

@[simp] private theorem storedWord_halt (s : State) (offset : Nat)
    (value : UInt256) :
    (Compression.storedWord s offset value).halt = s.halt := by rfl

@[simp] private theorem storedWord_callStack (s : State) (offset : Nat)
    (value : UInt256) :
    (Compression.storedWord s offset value).callStack = s.callStack := by rfl

@[simp] private theorem t1Returned_executionEnv (s : State)
    (x y z addend1 addend2 returnDest : UInt256) (rest : List UInt256) :
    (BigSigma.t1Returned s x y z addend1 addend2 returnDest rest).executionEnv =
      s.executionEnv := by rfl

@[simp] private theorem t1Returned_halt (s : State)
    (x y z addend1 addend2 returnDest : UInt256) (rest : List UInt256) :
    (BigSigma.t1Returned s x y z addend1 addend2 returnDest rest).halt = s.halt := by
  rfl

@[simp] private theorem t1Returned_callStack (s : State)
    (x y z addend1 addend2 returnDest : UInt256) (rest : List UInt256) :
    (BigSigma.t1Returned s x y z addend1 addend2 returnDest rest).callStack =
      s.callStack := by rfl

@[simp] private theorem t2Returned_executionEnv (s : State)
    (x y z returnDest : UInt256) (rest : List UInt256) :
    (BigSigma.t2Returned s x y z returnDest rest).executionEnv = s.executionEnv := by
  rfl

@[simp] private theorem t2Returned_halt (s : State)
    (x y z returnDest : UInt256) (rest : List UInt256) :
    (BigSigma.t2Returned s x y z returnDest rest).halt = s.halt := by rfl

@[simp] private theorem t2Returned_callStack (s : State)
    (x y z returnDest : UInt256) (rest : List UInt256) :
    (BigSigma.t2Returned s x y z returnDest rest).callStack = s.callStack := by rfl

@[simp] theorem afterPair_executionEnv (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterPair s msgOff returnDest rest j).executionEnv =
      s.executionEnv := by
  simp [Compression.afterPair, Compression.afterPairT21,
    Compression.afterPairT11, Compression.secondPairInputsLoaded,
    Compression.afterPairT20, Compression.afterPairT10,
    Compression.firstPairInputsLoaded, Compression.afterPairCondition]

@[simp] theorem afterPair_halt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterPair s msgOff returnDest rest j).halt = s.halt := by
  simp [Compression.afterPair, Compression.afterPairT21,
    Compression.afterPairT11, Compression.secondPairInputsLoaded,
    Compression.afterPairT20, Compression.afterPairT10,
    Compression.firstPairInputsLoaded, Compression.afterPairCondition]

@[simp] theorem afterPair_callStack (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterPair s msgOff returnDest rest j).callStack = s.callStack := by
  simp [Compression.afterPair, Compression.afterPairT21,
    Compression.afterPairT11, Compression.secondPairInputsLoaded,
    Compression.afterPairT20, Compression.afterPairT10,
    Compression.firstPairInputsLoaded, Compression.afterPairCondition]

def pairLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => Compression.pairAt s msgOff returnDest rest 0
  | n + 1 => Compression.afterPair
      (pairLoopState s msgOff returnDest rest n)
      msgOff returnDest rest (2 * n)

@[simp] theorem pairLoopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (pairLoopState s msgOff returnDest rest n).executionEnv = s.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairLoopState, ih]

@[simp] theorem pairLoopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (pairLoopState s msgOff returnDest rest n).halt = s.halt := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairLoopState, ih]

@[simp] theorem pairLoopState_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (pairLoopState s msgOff returnDest rest n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairLoopState, ih]

def gasStepsPairLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (pairLoopState s msgOff returnDest rest 0)
      (pairLoopState s msgOff returnDest rest 32) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 32)
  intro n hn
  let q := pairLoopState s msgOff returnDest rest n
  have qcode : q.executionEnv.code = submissionBytecode := by
    simpa [q] using hcode
  have qfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by
    simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have g := gasStepsPair q msgOff returnDest rest (2 * n) (by omega)
    hcap qcode qfork qrun qnp
  have hs : Compression.pairAt q msgOff returnDest rest (2 * n) =
      pairLoopState s msgOff returnDest rest n := by
    cases n with
    | zero => rfl
    | succ n => simp [q, pairLoopState, Compression.afterPair,
        Compression.pairAt, Nat.mul_add, Nat.add_comm]
  have ht : Compression.afterPair q msgOff returnDest rest (2 * n) =
      pairLoopState s msgOff returnDest rest (n + 1) := by
    rfl
  exact Challenge.EvmProof.GasSteps.cast g hs ht

end Challenge.Sha256.Submission.Proofs.Bytecode.PairCompositionTest
