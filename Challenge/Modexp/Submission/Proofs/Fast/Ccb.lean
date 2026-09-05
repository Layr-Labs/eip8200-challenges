import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P14
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P17
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Ccb

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

def stagePC : Nat → Nat
  | 0 => 2995
  | 1 => 3006
  | 2 => 3017
  | 3 => 3028
  | 4 => 3039
  | 5 => 3050
  | 6 => 3061
  | 7 => 3072
  | 8 => 3083
  | _ => 0

def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2863
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

def amCallState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2467
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 2995] ++ ([UInt256.ofNat px, ret] ++ rest)
           memory := mem }

def stageState (s : State) (mem : ByteArray) (i px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat (stagePC i)
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

abbrev postState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  stageState s mem 0 px ret rest

def mpCallState (s : State) (mem : ByteArray) (i px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat (stagePC (i + 1))] ++
                    ([UInt256.ofNat px, ret] ++ rest)
           memory := mem }

def doneState (s : State) (mem : ByteArray) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret, stack := rest, memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1742
      (entryState s mem px ret rest) = some (amCallState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h2995 : (2995 : UInt256) = UInt256.ofNat 2995 := by decide
  have h2467 : (2467 : UInt256) = UInt256.ofNat 2467 := by decide
  have h2467Nat : (UInt256.ofNat 2467).toNat = 2467 := by decide
  simp (config := { maxSteps := 400000 }) [blk1742, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, amCallState, fastPC20, hc2, hc3, hc4, hc5, hc6, hc7, hcode, hrun,
    h2995, h2467, h2467Nat, jumpDest2467,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_call (s : State) (mem : ByteArray) (i px : Nat) (ret : UInt256)
    (rest : List UInt256) (hi : i < 8) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (ccbCallBlock i)
      (stageState s mem i px ret rest) = some (mpCallState s mem i px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h1939 : (1939 : UInt256) = UInt256.ofNat 1939 := by decide
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  interval_cases i <;>
    simp (config := { maxSteps := 500000 }) [ccbCallBlock, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      stageState, stagePC, mpCallState, fastPC23, hc2, hc3, hc4, hc5, hc6, hc7,
      hcode, hrun, h1939, h1939Nat, jumpDest1939,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkCcbExit
      (stageState s mem 8 px ret rest) = some (doneState s mem ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp (config := { maxSteps := 200000 }) [blkCcbExit, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    stageState, stagePC, doneState, fastPC23, hc1, hc2, hc3, hcode, hjump, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_entry (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (amCallState s mem px ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1742 hcode hfork
      (run_entry s mem px ret rest hcap hcode hrun) hrun hnp

def gasSteps_call (s : State) (mem : ByteArray) (i px : Nat) (ret : UInt256)
    (rest : List UInt256) (hi : i < 8) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (stageState s mem i px ret rest)
      (mpCallState s mem i px ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (ccbCallBlock i) hcode hfork
      (run_call s mem i px ret rest hi hcap hcode hrun) hrun hnp

def gasSteps_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (stageState s mem 8 px ret rest)
      (doneState s mem ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkCcbExit hcode hfork
      (run_exit s mem px ret rest hcap hcode hjump hrun) hrun hnp

def chainFamily (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (i : Nat) : State :=
  stageState s (mems i) i px ret rest

def gasSteps_iteration (s : State) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray)
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) i px ret rest)
        (stageState s (mems (i + 1)) (i + 1) px ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.GasSteps (chainFamily s px ret rest mems i)
      (chainFamily s px ret rest mems (i + 1)) :=
  (gasSteps_call s (mems i) i px ret rest hi hcap hcode hfork hrun hnp).trans
    (monpro i hi)

def gasSteps_chain (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray)
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) i px ret rest)
        (stageState s (mems (i + 1)) (i + 1) px ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (stageState s (mems 0) 0 px ret rest)
      (stageState s (mems 8) 8 px ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := chainFamily s px ret rest mems) 8
    (fun i hi => gasSteps_iteration s px ret rest mems monpro hcap hcode hfork hrun
      hnp i hi)

def gasSteps_ccb (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mem0 : ByteArray) (mems : Nat → ByteArray)
    (addmod : Challenge.EvmProof.GasSteps (amCallState s mem0 px ret rest)
      (postState s (mems 0) px ret rest))
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) i px ret rest)
        (stageState s (mems (i + 1)) (i + 1) px ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s mem0 px ret rest)
      (doneState s (mems 8) ret rest) :=
  ((((gasSteps_entry s mem0 px ret rest hcap hcode hfork hrun hnp).trans addmod).trans
      (gasSteps_chain s px ret rest mems monpro hcap hcode hfork hrun hnp)).trans
    (gasSteps_exit s (mems 8) px ret rest hcap hcode hjump hfork hrun hnp))

end Challenge.Modexp.Submission.Proofs.Fast.Ccb
