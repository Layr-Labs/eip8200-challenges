import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentFallbackTrace
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCore

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located traces for the fixed-exponent addition chains

The two memory-writing blocks are connected to artifact-independent semantic
reductions.  The remaining control-only blocks reduce directly.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentChainTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCore
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths

set_option linter.unusedSimpArgs false in
theorem run_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.start
      (FixedExponentStates.special s memory n bsize esize msize count) =
      some (FixedExponentStates.square s (initialSquareMem memory n)
        n bsize esize msize count) := by
  rw [show Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.start
      (FixedExponentStates.special s memory n bsize esize msize count) =
      runInstructions startProgram
        (FixedExponentStates.special s memory n bsize esize msize count) by
    simp (config := { maxSteps := 300000 })
      [FixedExponentPaths.start, startProgram, runInstructions,
        opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        FixedExponentStates.special, Exp.outer, hrun,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]]
  exact run_startProgram s memory n bsize esize msize count hn hn32 hactive hrun

set_option linter.unusedSimpArgs false in
theorem run_squareCall (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.squareCall
      (FixedExponentStates.square s memory n bsize esize msize count) =
      some (Exp.mpCall s memory 1024 1024 1024 (UInt256.ofNat 3781)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) := by
  simp (config := { maxSteps := 400000 })
    [FixedExponentPaths.squareCall, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.square, Exp.mpCall, Exp.outer, hcode, hrun, jumpDest1930,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_squareReturn_loop (s : State) (memory : ByteArray)
    (n bsize esize msize k : Nat) (hk : k ≠ 0) (hk16 : k + 1 ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.squareReturn
      (FixedExponentStates.squareReturn s memory n bsize esize msize (k + 1)) =
      some (FixedExponentStates.square s memory n bsize esize msize k) := by
  have hsub : UInt256.ofNat (k + 1) - UInt256.ofNat 1 = UInt256.ofNat k := by
    simpa using Challenge.EvmProof.Word.ofNat_sub_ofNat
      (a := k + 1) (b := 1) (by omega)
      (Nat.lt_of_le_of_lt hk16 (by norm_num))
  have htrue : UInt256.isTrue (UInt256.ofNat k) := by
    show (UInt256.ofNat k).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hk
  simp (config := { maxSteps := 400000 })
    [FixedExponentPaths.squareReturn, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.squareReturn, FixedExponentStates.square,
      Exp.outer, hcode, hrun, hsub, htrue,
      jumpDest3764, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_squareReturn_exit (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.squareReturn
      (FixedExponentStates.squareReturn s memory n bsize esize msize 1) =
      some (FixedExponentStates.product s memory n bsize esize msize) := by
  have hsub : UInt256.ofNat 1 - UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 300000 })
    [FixedExponentPaths.squareReturn, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.squareReturn, FixedExponentStates.product,
      Exp.outer, hrun, hsub, hfalse, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_product (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.product
      (FixedExponentStates.product s memory n bsize esize msize) =
      some (Exp.mpCall s memory 1024 2048 1024 (UInt256.ofNat 3808)
        (Exp.outer n bsize esize msize)) := by
  simp (config := { maxSteps := 400000 })
    [FixedExponentPaths.product, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.product, Exp.mpCall, Exp.outer,
      hcode, hrun, jumpDest1930,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_decode (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.decode
      (FixedExponentStates.decode s memory n bsize esize msize) =
      some (Exp.mpCall s
        (Exp.storeWord memory (3040 + 32 * n) (UInt256.ofNat 1))
        1024 3072 1024 (UInt256.ofNat 3833)
        (Exp.outer n bsize esize msize)) := by
  rw [show Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.decode
      (FixedExponentStates.decode s memory n bsize esize msize) =
      runInstructions decodeProgram
        (FixedExponentStates.decode s memory n bsize esize msize) by
    simp (config := { maxSteps := 300000 })
      [FixedExponentPaths.decode, decodeProgram, runInstructions,
        opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        FixedExponentStates.decode, Exp.outer, hcode, hrun, jumpDest1930,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]]
  exact run_decodeProgram s memory n bsize esize msize hn32 hactive
    (by simpa [hcode] using jumpDest1930) hrun

set_option linter.unusedSimpArgs false in
theorem run_finish (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.finish
      (FixedExponentStates.finish s memory n bsize esize msize) =
      some (Exp.finHead s memory n bsize esize msize) := by
  simp (config := { maxSteps := 300000 })
    [FixedExponentPaths.finish, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.finish, Exp.finHead, Exp.outer,
      hcode, hrun, jumpDest1867,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.special s memory n bsize esize msize count)
      (FixedExponentStates.square s (initialSquareMem memory n)
        n bsize esize msize count) :=
  sound FixedExponentPaths.start
    (run_start s memory n bsize esize msize count hn hn32 hactive hrun)
    hcode hfork hrun hnp

def gasSteps_squareCall (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.square s memory n bsize esize msize count)
      (Exp.mpCall s memory 1024 1024 1024 (UInt256.ofNat 3781)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  sound FixedExponentPaths.squareCall
    (run_squareCall s memory n bsize esize msize count hcode hrun)
    hcode hfork hrun hnp

def gasSteps_squareReturnLoop (s : State) (memory : ByteArray)
    (n bsize esize msize k : Nat) (hk : k ≠ 0) (hk16 : k + 1 ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.squareReturn s memory n bsize esize msize (k + 1))
      (FixedExponentStates.square s memory n bsize esize msize k) :=
  sound FixedExponentPaths.squareReturn
    (run_squareReturn_loop s memory n bsize esize msize k hk hk16 hcode hrun)
    hcode hfork hrun hnp

def gasSteps_squareReturnExit (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.squareReturn s memory n bsize esize msize 1)
      (FixedExponentStates.product s memory n bsize esize msize) :=
  sound FixedExponentPaths.squareReturn
    (run_squareReturn_exit s memory n bsize esize msize hrun)
    hcode hfork hrun hnp

def gasSteps_product (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.product s memory n bsize esize msize)
      (Exp.mpCall s memory 1024 2048 1024 (UInt256.ofNat 3808)
        (Exp.outer n bsize esize msize)) :=
  sound FixedExponentPaths.product
    (run_product s memory n bsize esize msize hcode hrun)
    hcode hfork hrun hnp

def gasSteps_decode (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.decode s memory n bsize esize msize)
      (Exp.mpCall s
        (Exp.storeWord memory (3040 + 32 * n) (UInt256.ofNat 1))
        1024 3072 1024 (UInt256.ofNat 3833)
        (Exp.outer n bsize esize msize)) :=
  sound FixedExponentPaths.decode
    (run_decode s memory n bsize esize msize hn32 hactive hcode hrun)
    hcode hfork hrun hnp

def gasSteps_finish (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.finish s memory n bsize esize msize)
      (Exp.finHead s memory n bsize esize msize) :=
  sound FixedExponentPaths.finish
    (run_finish s memory n bsize esize msize hcode hrun)
    hcode hfork hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentChainTrace
