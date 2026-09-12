import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P14
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Reachable CCB squaring loop

The width-selected CcbSeed entry establishes the squaring count and enters this
loop. The legacy single-doubling entry is absent from the selected bytecode.
This module proves the shared loop and return contracts used by the current
seed path against the actual instruction locations.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Ccb

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

-- Lean 4.31 ships `List.getElem?_cons_zero` without the `simp` attribute, so the
-- program-counter tables of `Fast.Defs` (which end in `[…][i - lo]!`) do not
-- reduce inside the block-reduction `simp` calls without it.
attribute [local simp] List.getElem?_cons_zero

/-- The multiply entry `JUMPDEST` at pc 3920 (0x0f50, instruction 2961), the target of every `MONPRO` call. -/
theorem jumpDestMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3779 = true :=
  Artifact.isValidJumpDest_index 2849 (by rfl)

/-! ## States at the block boundaries -/

/-- The live part of the stack inside the loop: the counter, the block pointer
and the caller's return address. -/
def loopStack (px k : Nat) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat px, ret] ++ rest

/-- The loop head `CCL`, pc 2299, with the counter at `k`. -/
def loopState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1925
           stack := loopStack px k ret rest
           memory := mem }

/-- The `MONPRO` call, pc 4137, with the frame `[px, px, px, 2310]` pushed. -/
def mpCallState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3779
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 1936] ++ loopStack px k ret rest
           memory := mem }

/-- The return point, pc 2310, with the counter still at `k`. -/
def retState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1936
           stack := loopStack px k ret rest
           memory := mem }

/-- The loop exit, pc 2319, with the counter at zero. -/
def exitState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1945
           stack := loopStack px 0 ret rest
           memory := mem }

/-- Back at the caller, pc `ret`, with the frame popped. -/
def doneState (s : State) (mem : ByteArray) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := mem }

/-! ## Block reductions -/

set_option linter.unusedSimpArgs false in
/-- `blk1751` (pc 2299..2309): push the `MONPRO` frame and jump to pc 4137. -/
theorem run_call (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1751
      (loopState s mem px k ret rest) =
      some (mpCallState s mem px k ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h2888 : (1936 : UInt256) = UInt256.ofNat 1936 := by decide
  have h1939 : (3779 : UInt256) = UInt256.ofNat 3779 := by decide
  have h1939Nat : (UInt256.ofNat 3779).toNat = 3779 := by decide
  simp (config := { maxSteps := 400000 }) [blk1751, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, mpCallState, loopStack, fastPC20, hc3, hc4, hc5, hc6, hc7, hc8,
    hcode, hrun, h2888, h1939, h1939Nat, jumpDestMulEntry,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1758` (pc 2310..2318), counter above one: decrement and loop. -/
theorem run_ret (s : State) (mem : ByteArray) (px k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk8 : k ≤ 8)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1758
      (retState s mem px k ret rest) =
      some (loopState s mem px k' ret rest) := by
  subst hk
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h2877 : (1925 : UInt256) = UInt256.ofNat 1925 := by decide
  have h2877Nat : (UInt256.ofNat 1925).toNat = 1925 := by decide
  have hk7 : k' ≤ 7 := by omega
  have hdec : UInt256.lnot ({ val := 0 } : UInt256) + UInt256.ofNat (k' + 1) =
      UInt256.ofNat k' := by
    interval_cases k' <;> decide
  have htrue : UInt256.isTrue (UInt256.ofNat k') := by
    show (UInt256.ofNat k').toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 400000 }) [blk1758, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, loopState, loopStack, fastPC20, hc3, hc4, hc5, hcode, hrun,
    hzero, h2877, h2877Nat, hdec, htrue, jumpDest2299, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1758` (pc 2310..2318), counter one: fall through to the exit. -/
theorem run_retLast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1758
      (retState s mem px 1 ret rest) =
      some (exitState s mem px ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h2877 : (1925 : UInt256) = UInt256.ofNat 1925 := by decide
  have hdec : UInt256.lnot ({ val := 0 } : UInt256) + UInt256.ofNat 1 =
      UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1758, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, exitState, loopStack, fastPC20, hc3, hc4, hc5, hrun,
    hzero, h2877, hdec, hfalse, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1765` (pc 2319..2321): pop the frame and return to the caller. -/
theorem run_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1765
      (exitState s mem px ret rest) =
      some (doneState s mem ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp (config := { maxSteps := 200000 }) [blk1765, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    exitState, doneState, loopStack, fastPC20, hc1, hc2, hc3, hcode, hjump, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## Gas traces for the individual blocks -/

def gasSteps_call (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s mem px k ret rest)
      (mpCallState s mem px k ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1751 hcode hfork
      (run_call s mem px k ret rest hcap hcode hrun) hrun hnp

def gasSteps_ret (s : State) (mem : ByteArray) (px k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk8 : k ≤ 8)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px k ret rest)
      (loopState s mem px k' ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1758 hcode hfork
      (run_ret s mem px k k' ret rest hcap hk hk' hk8 hcode hrun) hrun hnp

def gasSteps_retLast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px 1 ret rest)
      (exitState s mem px ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1758 hcode hfork
      (run_retLast s mem px ret rest hcap hrun) hrun hnp

def gasSteps_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (exitState s mem px ret rest)
      (doneState s mem ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1765 hcode hfork
      (run_exit s mem px ret rest hcap hcode hjump hrun) hrun hnp

/-! ## The squaring loop -/

/-- The indexed loop-head family: after `i` `MONPRO` calls the counter stands
at `8 - i`. -/
def loopFamily (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (i : Nat) : State :=
  loopState s (mems i) px (8 - i) ret rest

/-- One loop iteration: call `MONPRO` and decrement the counter. -/
def gasSteps_iteration (s : State) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray)
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) px (8 - i) ret rest)
        (retState s (mems (i + 1)) px (8 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (i : Nat) (hi : i < 7) :
    Challenge.EvmProof.GasSteps (loopFamily s px ret rest mems i)
      (loopFamily s px ret rest mems (i + 1)) :=
  ((gasSteps_call s (mems i) px (8 - i) ret rest hcap hcode hfork hrun hnp).trans
      (monpro i (by omega))).trans
    (gasSteps_ret s (mems (i + 1)) px (8 - i) (8 - (i + 1)) ret rest hcap
      (by omega) (by omega) (by omega) hcode hfork hrun hnp)

/-- The seven iterations that end at the loop head with the counter at one. -/
def gasSteps_loop (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray)
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) px (8 - i) ret rest)
        (retState s (mems (i + 1)) px (8 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s (mems 0) px 8 ret rest)
      (loopState s (mems 7) px 1 ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := loopFamily s px ret rest mems) 7
    (fun i hi => gasSteps_iteration s px ret rest mems monpro hcap hcode hfork hrun
      hnp i hi)


end Challenge.Modexp.Submission.Proofs.Fast.Ccb
