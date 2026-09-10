import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsEntry
import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsGuard
import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTail
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsGuard
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsEntry
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTail
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding

/-- A checked raw run implies the ordinary symbolic instruction fold. -/
theorem runInstructions_of_raw (instructions : List Instr) (s t : State)
    (h : runRaw instructions s = some t) :
    runInstructions instructions s = some t := by
  induction instructions generalizing s t with
  | nil => simpa [runRaw, runInstructions] using h
  | cons i rest ih =>
      cases hstep : Stepper.runInstr i s with
      | none => simp [runRaw, hstep] at h
      | some next =>
          cases rest with
          | nil => simpa [runRaw, runInstructions, hstep] using h
          | cons j tail =>
              cases hhalt : next.halt <;> simp [runRaw, hstep, hhalt] at h
              simpa [runInstructions, hstep] using ih next t h

/-- The instruction and location obligations required from the final artifact. -/
structure Blocks (artifact : ProgramArtifact) where
  entry : Block artifact .Osaka 2225 entryProgram
  first : Block artifact .Osaka 2241 limbProgram
  second : Block artifact .Osaka 2366 limbProgram
  guard : Block artifact .Osaka 2491 guardProgram
  tail : Block artifact .Osaka 2500 tailProgram

def gasSteps_limb {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (first : Bool) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact .Osaka s) (hcap : rest.length ≤ 1008)
    (hact : 296 ≤ s.activeWords.toNat) (hj : j < n) (hn32 : n ≤ 32) :
    GasSteps (walkState (limbPC first) s memory n j pdst ret rest)
      (walkState (limbPC first + 125) s memory n (j + 1) pdst ret rest) := by
  have hrun := runInstructions_of_raw _ _ _
    (run_limb first s memory n j pdst ret rest hcap env.running hact hj hn32)
  cases first
  · exact blocks.second.steps (env.transfer rfl rfl) rfl hrun
  · exact blocks.first.steps (env.transfer rfl rfl) rfl hrun

def gasSteps_guard {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact .Osaka s) (hcap : rest.length ≤ 1008)
    (hj : j ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2241 = true) :
    GasSteps (walkState 2491 s memory n j pdst ret rest)
      (walkState (if j < n then 2241 else 2500) s memory n j pdst ret rest) :=
  blocks.guard.steps (env.transfer rfl rfl) rfl (runInstructions_of_raw _ _ _
    (run_guard s memory n j pdst ret rest hcap env.running hj hn32 hjump))

def gasSteps_pair {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact .Osaka s) (hcap : rest.length ≤ 1008)
    (hact : 296 ≤ s.activeWords.toNat) (hj : j + 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2241 = true) :
    GasSteps (walkState 2241 s memory n j pdst ret rest)
      (walkState (if j + 2 < n then 2241 else 2500) s memory n (j + 2) pdst ret rest) :=
  ((gasSteps_limb blocks true s memory n j pdst ret rest env hcap hact (by omega) hn32).trans
    (gasSteps_limb blocks false s memory n (j + 1) pdst ret rest env hcap hact (by omega) hn32)).trans
    (gasSteps_guard blocks s memory n (j + 2) pdst ret rest env hcap hj hn32 hjump)

/-- Any nonempty sequence of pairs completes the unchanged subtraction model. -/
def gasSteps_pairs {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact .Osaka s) (hcap : rest.length ≤ 1008)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2241 = true)
    (k j : Nat) (hk : 0 < k) (hcount : j + 2 * k = n) :
    GasSteps (walkState 2241 s memory n j pdst ret rest)
      (walkState 2500 s memory n n pdst ret rest) := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
      have hp := gasSteps_pair blocks s memory n j pdst ret rest env hcap hact
        (by omega) hn32 hjump
      by_cases hk0 : k = 0
      · have hlast : j + 2 = n := by omega
        exact hp.cast rfl (by simp [hlast])
      · have hmore : j + 2 < n := by omega
        exact (hp.cast rfl (by rw [if_pos hmore])).trans
          (ih (j + 2) (by omega) (by omega))

/-- Complete CSUB trace, parameterized only by exact block bindings. -/
def gasSteps_csub {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact .Osaka s) (hcap : rest.length ≤ 1008)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hfirst : Decode.isValidJumpDest s.executionEnv.code 2241 = true)
    (hsecond : Decode.isValidJumpDest s.executionEnv.code 2366 = true)
    (hret : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n))
    (hs32 : MachineState.readWord (csStep memory n n).memory 9344 = UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (hsrcFit : (csSrc memory n n).toNat + 32 * n ≤ 9472) :
    GasSteps (entryState s memory pdst ret rest)
      (csReturnedState s memory n n pdst ret rest) := by
  have hentry := blocks.entry.steps (env.transfer (t := entryState s memory pdst ret rest) rfl rfl) rfl
    (runInstructions_of_raw _ _ _ (run_entry s memory n pdst ret rest hcap
      env.running hact hn hn32 htl hsecond))
  have hquot : 0 < n / 2 := by omega
  have hcomplete : GasSteps (enteredState s memory n pdst ret rest)
      (walkState 2500 s memory n n pdst ret rest) := by
    by_cases heven : n % 2 = 0
    · have hstart : enteredState s memory n pdst ret rest =
          walkState 2241 s memory n 0 pdst ret rest := by
        simp [enteredState, walkState, heven, csStep, affinePt]
      exact (gasSteps_pairs blocks s memory n pdst ret rest env hcap hact hn32 hfirst
        (n / 2) 0 hquot (by omega)).cast hstart.symm rfl
    · have hstart : enteredState s memory n pdst ret rest =
          walkState 2366 s memory n 0 pdst ret rest := by
        simp [enteredState, walkState, heven, csStep, affinePt]
      have h1 := gasSteps_limb blocks false s memory n 0 pdst ret rest env hcap hact
        (by omega) hn32
      have h2 := gasSteps_guard blocks s memory n 1 pdst ret rest env hcap (by omega) hn32 hfirst
      have hpeel := (h1.trans h2).cast hstart.symm (by rw [if_pos (show 1 < n by omega)])
      exact hpeel.trans (gasSteps_pairs blocks s memory n pdst ret rest env hcap hact hn32 hfirst
        (n / 2) 1 hquot (by omega))
  have hnn : n - 1 + 1 = n := by omega
  have htailRaw := run_tail s memory n (n - 1) pdst ret rest hcap env.running hact
    hn hn32 hret (by simpa [hnn] using hs32) hdstFit (by simpa [hnn] using hsrcFit)
  have htail := blocks.tail.steps (env.transfer (t := walkState 2500 s memory n (n - 1 + 1) pdst ret rest) rfl rfl) rfl
    (runInstructions_of_raw _ _ _ htailRaw)
  exact (hentry.trans hcomplete).trans (htail.cast (by rw [hnn]) (by rw [hnn]))

end Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTrace
