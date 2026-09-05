import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-!
# Q4M quad-round lane

Each lane repeats twenty quad wrappers.  The lane invariants are those of the
paired design; only the step size changes.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLane

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

def stateAt (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  roundEntry s pc w.a w.b w.c w.d w.e rest

def WordsAt (s : State) (word : Nat → UInt32) : Prop :=
  ∀ k, k < 16 → Challenge.EvmProof.Word.toUInt32
    (MachineState.readWord s.memory (644 + 4 * k)) = word k

theorem stateAt_words (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rest : List UInt256) (word : Nat → UInt32) (hwords : WordsAt s word) :
    WordsAt (stateAt s pc w rest) word := by
  intro k hk
  simpa [stateAt, roundEntry] using hwords k hk

theorem stateAt_activeWords (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rest : List UInt256) :
    (stateAt s pc w rest).activeWords = s.activeWords := by
  rfl

private theorem leftRounds_quad (word : Nat → UInt32) (i : Nat)
    (working : Compression.EvmWorking) :
    StackCompression.leftRounds word (4 * (i + 1)) working =
      StackCompression.leftStep word (4 * i + 3)
        (StackCompression.leftStep word (4 * i + 2)
          (StackCompression.leftStep word (4 * i + 1)
            (StackCompression.leftStep word (4 * i)
              (StackCompression.leftRounds word (4 * i) working)))) := by
  have h1 : 4 * (i + 1) = (((4 * i + 1) + 1) + 1) + 1 := by omega
  rw [h1]
  simp only [StackCompression.leftRounds]

private theorem rightRounds_quad (word : Nat → UInt32) (i : Nat)
    (working : Compression.EvmWorking) :
    StackCompression.rightRounds word (4 * (i + 1)) working =
      StackCompression.rightStep word (4 * i + 3)
        (StackCompression.rightStep word (4 * i + 2)
          (StackCompression.rightStep word (4 * i + 1)
            (StackCompression.rightStep word (4 * i)
              (StackCompression.rightRounds word (4 * i) working)))) := by
  have h1 : 4 * (i + 1) = (((4 * i + 1) + 1) + 1) + 1 := by omega
  rw [h1]
  simp only [StackCompression.rightRounds]

def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC 0) w rest)
      (stateAt s (QuadSites.leftPC 20)
        (StackCompression.leftRounds word 80 w) rest) := by
  let states := fun n => stateAt s (QuadSites.leftPC n)
    (StackCompression.leftRounds word (4 * n) w) rest
  have step (i : Nat) (hi : i < 20) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := QuadRoundCertificates.gasSteps_leftQuad s word
      (StackCompression.leftRounds word (4 * i) w) rest k
      (fun n hn => hwords n hn) hactive hstack hcode hfork hrun hnp
    have hnext :
        StackCompression.leftRounds word (4 * (i + 1)) w =
          QuadRoundCertificates.pureQuadWorking s
            (StackCompression.leftRounds word (4 * i) w) (k.val / 4)
            (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
            (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
            (QuadSites.leftM0 k) (QuadSites.leftM1 k)
            (QuadSites.leftM2 k) (QuadSites.leftM3 k)
            (QuadSites.leftConstant k) := by
      rw [QuadRoundCertificates.pureQuadWorking_left s word
        (StackCompression.leftRounds word (4 * i) w) k
        (fun n hn => hwords n hn)]
      exact leftRounds_quad word i w
    apply g.cast
    · rfl
    · simp only [states, stateAt, roundEntry, roundWords, k]
      rw [hnext]
  have g := GasSteps.iterateBounded 20 step
  simpa only [states, Nat.mul_zero, StackCompression.leftRounds] using g

def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.rightPC 0) w rest)
      (stateAt s (QuadSites.rightPC 20)
        (StackCompression.rightRounds word 80 w) rest) := by
  let states := fun n => stateAt s (QuadSites.rightPC n)
    (StackCompression.rightRounds word (4 * n) w) rest
  have step (i : Nat) (hi : i < 20) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := QuadRoundCertificates.gasSteps_rightQuad s word
      (StackCompression.rightRounds word (4 * i) w) rest k
      (fun n hn => hwords n hn) hactive hstack hcode hfork hrun hnp
    have hnext :
        StackCompression.rightRounds word (4 * (i + 1)) w =
          QuadRoundCertificates.pureQuadWorking s
            (StackCompression.rightRounds word (4 * i) w) (4 - k.val / 4)
            (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
            (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
            (QuadSites.rightM0 k) (QuadSites.rightM1 k)
            (QuadSites.rightM2 k) (QuadSites.rightM3 k)
            (QuadSites.rightConstant k) := by
      rw [QuadRoundCertificates.pureQuadWorking_right s word
        (StackCompression.rightRounds word (4 * i) w) k
        (fun n hn => hwords n hn)]
      exact rightRounds_quad word i w
    apply g.cast
    · rfl
    · simp only [states, stateAt, roundEntry, roundWords, k]
      rw [hnext]
  have g := GasSteps.iterateBounded 20 step
  simpa only [states, Nat.mul_zero, StackCompression.rightRounds] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLane
