import Challenge.Modexp.Submission.Proofs.Fast.Ccb
import Challenge.Modexp.Submission.Proofs.Fast.CcbSeedPaths
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Generic execution of the width-selected CCB seed. The appendix performs
eight or sixteen doublings, then rejoins the unchanged CCB squaring loop with
five or four iterations. Arithmetic memory effects remain abstract contracts. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

def flag (n : Nat) : Nat := if 128 < 32 * n then 1 else 0
def doubles (n : Nat) : Nat := if 128 < 32 * n then 16 else 8
def squares (n : Nat) : Nat := if 128 < 32 * n then 4 else 5

theorem flag_le_one (n : Nat) : flag n ≤ 1 := by
  unfold flag
  split <;> omega

theorem doubles_pos (n : Nat) : 1 ≤ doubles n := by
  unfold doubles
  split <;> omega

theorem doubles_le_sixteen (n : Nat) : doubles n ≤ 16 := by
  unfold doubles
  split <;> omega

theorem squares_pos (n : Nat) : 1 ≤ squares n := by
  unfold squares
  split <;> omega

theorem squares_le_eight (n : Nat) : squares n ≤ 8 := by
  unfold squares
  split <;> omega

def loopStack (px n k : Nat) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat (flag n), UInt256.ofNat px, ret] ++ rest

def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3768
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

def loopState (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3781
           stack := loopStack px n k ret rest
           memory := mem }

def amCallState (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2203
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 3792] ++ loopStack px n k ret rest
           memory := mem }

def retState (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3792
           stack := loopStack px n k ret rest
           memory := mem }

def exitState (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3801
           stack := loopStack px n 0 ret rest
           memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hn32 : n ≤ 32)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hact : 296 ≤ s.activeWords.toNat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPath (entryState s mem px ret rest) =
      some (loopState s mem px n (doubles n) ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hwidth : 32 * n < 2 ^ 256 := by omega
  have hcmp : UInt256.lt (UInt256.ofNat 128) (UInt256.ofNat (32 * n)) =
      UInt256.ofNat (flag n) := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 128 < 2 ^ 256), Nat.mod_eq_of_lt hwidth]
    by_cases h : 128 < 32 * n <;> simp [flag, h]
  have hseed : UInt256.shiftLeft (UInt256.ofNat 8) (UInt256.ofNat (flag n)) =
      UInt256.ofNat (doubles n) := by
    by_cases h : 128 < 32 * n
    · simp only [flag, doubles, if_pos h]
      decide
    · simp only [flag, doubles, if_neg h]
      decide
  have hactN : MachineState.activeWordsAfter s.activeWords.toNat 9344 32 =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    simp only [show (32 : Nat) ≠ 0 by decide, if_false]
    exact Nat.max_eq_left (by omega)
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := by
    rw [hactN]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  simp (config := { maxSteps := 400000 })
    [entryPath, opAt, pushAt, wfOp, seedPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     entryState, loopState, loopStack, hc2, hc3, hc4, hc5, hrun,
     hsize, hcmp, hseed, hactW, State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_call (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock callPath (loopState s mem px n k ret rest) =
      some (amCallState s mem px n k ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h2467Nat : (UInt256.ofNat 2203).toNat = 2203 := by decide
  simp (config := { maxSteps := 400000 })
    [callPath, opAt, pushAt, wfOp, seedPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     loopState, amCallState, loopStack, hc4, hc5, hc6, hc7, hc8, hc9,
     hcode, hrun, h2467Nat, jumpDest2467,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_ret (s : State) (mem : ByteArray) (px n k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk16 : k ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock retPath (retState s mem px n k ret rest) =
      some (loopState s mem px n k' ret rest) := by
  subst hk
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hk15 : k' ≤ 15 := by omega
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h4029Nat : (UInt256.ofNat 3781).toNat = 3781 := by decide
  have hdec : UInt256.lnot ({ val := 0 } : UInt256) + UInt256.ofNat (k' + 1) =
      UInt256.ofNat k' := by
    interval_cases k' <;> decide
  have htrue : UInt256.isTrue (UInt256.ofNat k') := by
    show (UInt256.ofNat k').toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 400000 })
    [retPath, opAt, pushAt, wfOp, seedPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     retState, loopState, loopStack, hc4, hc5, hc6, hcode, hrun,
     hzero, h4029Nat, hdec, htrue, jumpDest4029, List.exchange,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_retLast (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock retPath (retState s mem px n 1 ret rest) =
      some (exitState s mem px n ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have hdec : UInt256.lnot ({ val := 0 } : UInt256) + UInt256.ofNat 1 =
      UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 })
    [retPath, opAt, pushAt, wfOp, seedPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     retState, exitState, loopStack, hc4, hc5, hc6, hrun,
     hzero, hdec, hfalse, List.exchange,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_finish (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishPath (exitState s mem px n ret rest) =
      some (Ccb.loopState s mem px (squares n) ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have h2877Nat : (UInt256.ofNat 2520).toNat = 2520 := by decide
  have hcount : UInt256.ofNat 5 - UInt256.ofNat (flag n) =
      UInt256.ofNat (squares n) := by
    by_cases h : 128 < 32 * n
    · simp only [flag, squares, if_pos h]
      decide
    · simp only [flag, squares, if_neg h]
      decide
  simp (config := { maxSteps := 400000 })
    [finishPath, opAt, pushAt, wfOp, seedPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     exitState, Ccb.loopState, loopStack, Ccb.loopStack, hc3, hc4,
     hcode, hrun, h2877Nat, hcount, jumpDest2855,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_entry (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hn32 : n ≤ 32)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (loopState s mem px n (doubles n) ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    entryPath hcode hfork (run_entry s mem px n ret rest hcap hn32 hsize hact hrun) hrun hnp

def gasSteps_call (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s mem px n k ret rest)
      (amCallState s mem px n k ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    callPath hcode hfork (run_call s mem px n k ret rest hcap hcode hrun) hrun hnp

def gasSteps_ret (s : State) (mem : ByteArray) (px n k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk16 : k ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px n k ret rest)
      (loopState s mem px n k' ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    retPath hcode hfork (run_ret s mem px n k k' ret rest hcap hk hk' hk16 hcode hrun) hrun hnp

def gasSteps_retLast (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px n 1 ret rest)
      (exitState s mem px n ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    retPath hcode hfork (run_retLast s mem px n ret rest hcap hrun) hrun hnp

def gasSteps_finish (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (exitState s mem px n ret rest)
      (Ccb.loopState s mem px (squares n) ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    finishPath hcode hfork (run_finish s mem px n ret rest hcap hcode hrun) hrun hnp

def gasSteps_seedLoop (s : State) (px n : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray)
    (addmod : ∀ i, i < doubles n →
      Challenge.EvmProof.GasSteps (amCallState s (mems i) px n (doubles n - i) ret rest)
        (retState s (mems (i + 1)) px n (doubles n - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s (mems 0) px n (doubles n) ret rest)
      (loopState s (mems (doubles n - 1)) px n 1 ret rest) := by
  have hd := doubles_pos n
  have hmax := doubles_le_sixteen n
  have hrem : doubles n - (doubles n - 1) = 1 := by omega
  have h := Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => loopState s (mems i) px n (doubles n - i) ret rest) (doubles n - 1)
    (fun i hi =>
      ((gasSteps_call s (mems i) px n (doubles n - i) ret rest
          hcap hcode hfork hrun hnp).trans (addmod i (by omega))).trans
        (gasSteps_ret s (mems (i + 1)) px n (doubles n - i) (doubles n - (i + 1))
          ret rest hcap (by omega) (by omega) (by omega) hcode hfork hrun hnp))
  simpa only [Nat.sub_zero, hrem] using h

/-- The existing CCB square loop accepts any positive count at most eight. -/
def gasSteps_squareRun (s : State) (px q : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (hq : 1 ≤ q) (hq8 : q ≤ 8)
    (monpro : ∀ i, i < q →
      Challenge.EvmProof.GasSteps (Ccb.mpCallState s (mems i) px (q - i) ret rest)
        (Ccb.retState s (mems (i + 1)) px (q - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (Ccb.loopState s (mems 0) px q ret rest)
      (Ccb.doneState s (mems q) ret rest) := by
  have hrem : q - (q - 1) = 1 := by omega
  have hnext : q - 1 + 1 = q := by omega
  have hloop := Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => Ccb.loopState s (mems i) px (q - i) ret rest) (q - 1)
    (fun i hi =>
      ((Ccb.gasSteps_call s (mems i) px (q - i) ret rest hcap hcode hfork hrun hnp).trans
        (monpro i (by omega))).trans
        (Ccb.gasSteps_ret s (mems (i + 1)) px (q - i) (q - (i + 1)) ret rest
          hcap (by omega) (by omega) (by omega) hcode hfork hrun hnp))
  have hloop' : Challenge.EvmProof.GasSteps (Ccb.loopState s (mems 0) px q ret rest)
      (Ccb.loopState s (mems (q - 1)) px 1 ret rest) := by
    simpa only [Nat.sub_zero, hrem] using hloop
  have hlast : Challenge.EvmProof.GasSteps (Ccb.mpCallState s (mems (q - 1)) px 1 ret rest)
      (Ccb.retState s (mems q) px 1 ret rest) := by
    simpa only [hrem, hnext] using monpro (q - 1) (by omega)
  exact ((hloop'.trans
    ((Ccb.gasSteps_call s (mems (q - 1)) px 1 ret rest hcap hcode hfork hrun hnp).trans
      hlast)).trans
        (Ccb.gasSteps_retLast s (mems q) px ret rest hcap hcode hfork hrun hnp)).trans
          (Ccb.gasSteps_exit s (mems q) px ret rest hcap hcode hjump hfork hrun hnp)

/-- Abstract execution certificate: width-selected doublings followed by the
unchanged generic CCB squaring loop. No arithmetic value assumption is added. -/
def gasSteps_ccb (s : State) (px n : Nat) (ret : UInt256) (rest : List UInt256)
    (seedMems squareMems : Nat → ByteArray)
    (hjoin : seedMems (doubles n) = squareMems 0)
    (addmod : ∀ i, i < doubles n →
      Challenge.EvmProof.GasSteps (amCallState s (seedMems i) px n (doubles n - i) ret rest)
        (retState s (seedMems (i + 1)) px n (doubles n - i) ret rest))
    (monpro : ∀ i, i < squares n →
      Challenge.EvmProof.GasSteps (Ccb.mpCallState s (squareMems i) px (squares n - i) ret rest)
        (Ccb.retState s (squareMems (i + 1)) px (squares n - i) ret rest))
    (hcap : rest.length ≤ 1008) (hn32 : n ≤ 32)
    (hsize : MachineState.readWord (seedMems 0) 9344 = UInt256.ofNat (32 * n))
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s (seedMems 0) px ret rest)
      (Ccb.doneState s (squareMems (squares n)) ret rest) := by
  have hd := doubles_pos n
  have hrem : doubles n - (doubles n - 1) = 1 := by omega
  have hnext : doubles n - 1 + 1 = doubles n := by omega
  have hlast : Challenge.EvmProof.GasSteps
      (amCallState s (seedMems (doubles n - 1)) px n 1 ret rest)
      (retState s (seedMems (doubles n)) px n 1 ret rest) := by
    simpa only [hrem, hnext] using addmod (doubles n - 1) (by omega)
  have hstart :=
    (gasSteps_entry s (seedMems 0) px n ret rest hcap hn32 hsize hact
      hcode hfork hrun hnp).trans
        (gasSteps_seedLoop s px n ret rest seedMems addmod hcap hcode hfork hrun hnp)
  have hlastStep :=
    ((gasSteps_call s (seedMems (doubles n - 1)) px n 1 ret rest
      hcap hcode hfork hrun hnp).trans hlast).trans
        (gasSteps_retLast s (seedMems (doubles n)) px n ret rest hcap hcode hfork hrun hnp)
  have hseed := (hstart.trans hlastStep).trans
    (gasSteps_finish s (seedMems (doubles n)) px n ret rest hcap hcode hfork hrun hnp)
  have hseed' : Challenge.EvmProof.GasSteps (entryState s (seedMems 0) px ret rest)
      (Ccb.loopState s (squareMems 0) px (squares n) ret rest) := by
    simpa only [hjoin] using hseed
  exact hseed'.trans
    (gasSteps_squareRun s px (squares n) ret rest squareMems (squares_pos n)
      (squares_le_eight n) monpro hcap hcode hjump hfork hrun hnp)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
