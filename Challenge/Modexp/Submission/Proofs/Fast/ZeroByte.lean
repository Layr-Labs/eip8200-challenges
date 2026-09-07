import Challenge.Modexp.Submission.Proofs.Fast.Ccb
import Challenge.Modexp.Submission.Proofs.Fast.Lz

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.ZeroByte

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! The appended zero-byte dispatcher and its two short continuation blocks. -/

@[simp] theorem fastPC26 (i : Nat) (hi : 2617 ≤ i) (hii : i ≤ 2634) :
    Artifact.submissionArtifact.instructionPC i =
      [3965,3966,3967,3968,3971,3972,3975,3976,3977,3978,3979,3982,3985,
       3987,3990,3991,3992,3995][i - 2617]! := by
  interval_cases i <;> decide

theorem jumpDest3965 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2617 (by rfl)

theorem jumpDest3976 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3976 = true :=
  Artifact.isValidJumpDest_index 2624 (by rfl)

theorem jumpDest3991 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3991 = true :=
  Artifact.isValidJumpDest_index 2632 (by rfl)

def zeroEntryState (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3976
           stack := [UInt256.ofNat 128, UInt256.ofNat w, UInt256.ofNat i] ++ rest
           memory := mem }

def zeroLoopState (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) : State :=
  Ccb.loopState s mem 1024 8 (UInt256.ofNat 3991)
    ([UInt256.ofNat 0, UInt256.ofNat w, UInt256.ofNat i] ++ rest)

def zeroExitState (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3991
           stack := [UInt256.ofNat 0, UInt256.ofNat w, UInt256.ofNat i] ++ rest
           memory := mem }

def blk2617 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2617 .JUMPDEST,
   opAt 2618 (.Dup ⟨1, by decide⟩),
   opAt 2619 .ISZERO,
   pushAt 2620 2 3976,
   opAt 2621 .JUMPI,
   pushAt 2622 2 1789,
   opAt 2623 .JUMP]

def blk2624 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2624 .JUMPDEST,
   opAt 2625 .POP,
   pushAt 2626 0 0,
   pushAt 2627 2 3991,
   pushAt 2628 2 1024,
   pushAt 2629 1 8,
   pushAt 2630 2 2877,
   opAt 2631 .JUMP]

def blk2632 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2632 .JUMPDEST,
   pushAt 2633 2 1832,
   opAt 2634 .JUMP]

set_option linter.unusedSimpArgs false in
theorem run_dispatch_zero (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hw : w = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2617
      (Lz.lzDispatch s mem i w rest) =
      some (zeroEntryState s mem i w rest) := by
  subst hw
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have h3976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3976 = true :=
    jumpDest3976
  simp (config := { maxSteps := 400000 }) [blk2617, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Lz.lzDispatch, zeroEntryState, hrun, hcode, hc1, hc2, hc3, h3976,
    isZero_ofNat_zero, isTrue_one,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_dispatch_nonzero (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hw : w ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2617
      (Lz.lzDispatch s mem i w rest) =
      some (Lz.lzJoin s mem i w 128 rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hz : UInt256.isZero (UInt256.ofNat w) = UInt256.ofNat 0 :=
    isZero_ofNat_of_ne (by omega) hw
  have hf : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have h1789 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1789 = true :=
    jumpDest1789
  simp (config := { maxSteps := 400000 }) [blk2617, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Lz.lzDispatch, Lz.lzJoin, hrun, hcode, hc1, hc2, hc3, hz, hf, h1789,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroEntry (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2624
      (zeroEntryState s mem i w rest) =
      some (zeroLoopState s mem i w rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h2877 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2877 = true :=
    jumpDest2877
  simp (config := { maxSteps := 400000 }) [blk2624, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    zeroEntryState, zeroLoopState, Ccb.loopState, Ccb.loopStack,
    hcode, hrun, hc1, hc2, hc3, hc4, hc5, hc6, hc7, h2877,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroExit (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2632
      (zeroExitState s mem i w rest) =
      some (Lz.lzNext s mem i w rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have h1832 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1832 = true :=
    jumpDest1832
  simp (config := { maxSteps := 200000 }) [blk2632, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    zeroExitState, Lz.lzNext, hcode, hrun, hc1, hc2, hc3, h1832,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_dispatch_zero (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hw : w = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (Lz.lzDispatch s mem i w rest)
      (zeroEntryState s mem i w rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2617 hcode hfork
      (run_dispatch_zero s mem i w rest hcap hw hcode hrun) hrun hnp

def gasSteps_dispatch_nonzero (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hw : w ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (Lz.lzDispatch s mem i w rest)
      (Lz.lzJoin s mem i w 128 rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2617 hcode hfork
      (run_dispatch_nonzero s mem i w rest hcap hw hcode hrun) hrun hnp

def gasSteps_zeroEntry (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (zeroEntryState s mem i w rest)
      (zeroLoopState s mem i w rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2624 hcode hfork
      (run_zeroEntry s mem i w rest hcap hcode hrun) hrun hnp

def gasSteps_zeroExit (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (zeroExitState s mem i w rest)
      (Lz.lzNext s mem i w rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2632 hcode hfork
      (run_zeroExit s mem i w rest hcap hcode hrun) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.ZeroByte
