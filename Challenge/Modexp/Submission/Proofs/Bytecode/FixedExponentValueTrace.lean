import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentDispatchTrace
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRouteLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located exponent-value checks

The two blocks below connect the single-byte and three-byte calldata reads to
the semantic exponent value used by the route interface.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentValueTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths

private theorem exponentValue_one (input : ByteArray) (bsize : Nat) :
    exponentValue input bsize 1 =
      (YulSemantics.EVM.byteFrom input.toList (96 + bsize)).toNat := by
  unfold exponentValue
  simpa using Challenge.EvmProof.Bytes.bytesToNatPadded_succ
    input (96 + bsize) 0

set_option linter.unusedSimpArgs false in
theorem run_checkThree_hit (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 1 = 3)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      (FixedExponentPaths.checkThree ++ FixedExponentPaths.threeHit)
      (FixedExponentStates.checkThree s memory n bsize 1 msize) =
      some (FixedExponentStates.special s memory n bsize 1 msize 1) := by
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat 2912 32) = s.activeWords :=
    Exp.activeWords_fix s 2912 32 (by omega) (by omega) hactive
  have haddr : (96 + bsize) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      96 + bsize := by
    apply Nat.mod_eq_of_lt
    omega
  have hread : UInt256.byteAt { val := 0 }
      (MachineState.readWord input (96 + bsize)) = UInt256.ofNat 3 := by
    rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord]
    rw [← exponentValue_one, hvalue]
  have heq : UInt256.eq (UInt256.ofNat 3) (UInt256.ofNat 3) =
      UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 700000 })
    [FixedExponentPaths.checkThree, FixedExponentPaths.threeHit,
      opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.checkThree, FixedExponentStates.special, Exp.outer,
      hdata, hcode, hrun, heoff, hfix, haddr, hread, heq,
      Exp.isZero_ofNat_one, Exp.not_isTrue_zero, jumpDest3719,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_checkThree_miss (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 1 ≠ 3)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.checkThree
      (FixedExponentStates.checkThree s memory n bsize 1 msize) =
      some (FixedExponentStates.fallback s memory n bsize 1 msize) := by
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat 2912 32) = s.activeWords :=
    Exp.activeWords_fix s 2912 32 (by omega) (by omega) hactive
  have haddr : (96 + bsize) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      96 + bsize := by
    apply Nat.mod_eq_of_lt
    omega
  have hread : UInt256.byteAt { val := 0 }
      (MachineState.readWord input (96 + bsize)) =
      UInt256.ofNat (exponentValue input bsize 1) := by
    rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord, exponentValue_one]
  have hvlt : exponentValue input bsize 1 < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
      input (96 + bsize) 1).trans_le (by norm_num)
  have heq : UInt256.eq (UInt256.ofNat 3)
      (UInt256.ofNat (exponentValue input bsize 1)) = UInt256.ofNat 0 := by
    rw [UInt256.eq, Exp.toNat_ofNat_self (by norm_num),
      Exp.toNat_ofNat_self hvlt, if_neg hvalue.symm]
  simp (config := { maxSteps := 700000 })
    [FixedExponentPaths.checkThree, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.checkThree, FixedExponentStates.fallback, Exp.outer,
      hdata, hcode, hrun, heoff, hfix, haddr, hread, heq,
      Exp.isZero_ofNat_zero, Exp.isTrue_one, jumpDest3802,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_check65537_hit (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 3 = 65537)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      (FixedExponentPaths.check65537 ++ FixedExponentPaths.fermatHit)
      (FixedExponentStates.check65537 s memory n bsize 3 msize) =
      some (FixedExponentStates.special s memory n bsize 3 msize 16) := by
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat 2912 32) = s.activeWords :=
    Exp.activeWords_fix s 2912 32 (by omega) (by omega) hactive
  have haddr : (96 + bsize) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      96 + bsize := by
    apply Nat.mod_eq_of_lt
    omega
  have hshr := Challenge.EvmProof.Bytes.shiftRight_readWord
    input (96 + bsize) 3 (by omega) (by omega)
  rw [show (32 - 3) * 8 = 232 by norm_num] at hshr
  unfold exponentValue at hvalue
  rw [hvalue] at hshr
  have heq : UInt256.eq (UInt256.ofNat 65537) (UInt256.ofNat 65537) =
      UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 700000 })
    [FixedExponentPaths.check65537, FixedExponentPaths.fermatHit,
      opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.check65537, FixedExponentStates.special, Exp.outer,
      hdata, hrun, heoff, hfix, haddr, hshr, heq,
      Exp.isZero_ofNat_one, Exp.not_isTrue_zero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_check65537_miss (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 3 ≠ 65537)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedExponentPaths.check65537
      (FixedExponentStates.check65537 s memory n bsize 3 msize) =
      some (FixedExponentStates.fallback s memory n bsize 3 msize) := by
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat 2912 32) = s.activeWords :=
    Exp.activeWords_fix s 2912 32 (by omega) (by omega) hactive
  have haddr : (96 + bsize) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      96 + bsize := by
    apply Nat.mod_eq_of_lt
    omega
  have hshr := Challenge.EvmProof.Bytes.shiftRight_readWord
    input (96 + bsize) 3 (by omega) (by omega)
  rw [show (32 - 3) * 8 = 232 by norm_num] at hshr
  change UInt256.shiftRight (MachineState.readWord input (96 + bsize))
      (UInt256.ofNat 232) = UInt256.ofNat (exponentValue input bsize 3) at hshr
  have hvlt : exponentValue input bsize 3 < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
      input (96 + bsize) 3).trans_le (by norm_num)
  have heq : UInt256.eq (UInt256.ofNat 65537)
      (UInt256.ofNat (exponentValue input bsize 3)) = UInt256.ofNat 0 := by
    rw [UInt256.eq, Exp.toNat_ofNat_self (by norm_num),
      Exp.toNat_ofNat_self hvlt, if_neg hvalue.symm]
  simp (config := { maxSteps := 700000 })
    [FixedExponentPaths.check65537, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedExponentStates.check65537, FixedExponentStates.fallback, Exp.outer,
      hdata, hcode, hrun, heoff, hfix, haddr, hshr, heq,
      Exp.isZero_ofNat_zero, Exp.isTrue_one, jumpDest3802,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

private def sound {start finish : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path start = some finish)
    (hcode : start.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : start.fork = .Osaka) (hrun : start.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig start.executionEnv.precompileConfig
      start.executionEnv.fork start.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps start finish :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_checkThree_hit (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 1 = 3)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.checkThree s memory n bsize 1 msize)
      (FixedExponentStates.special s memory n bsize 1 msize 1) :=
  sound (FixedExponentPaths.checkThree ++ FixedExponentPaths.threeHit)
    (run_checkThree_hit s memory input n bsize msize hb hvalue hdata hactive
      heoff hcode hrun)
    (by simpa [FixedExponentStates.checkThree, Artifact.submissionArtifact] using hcode)
    (by simpa [FixedExponentStates.checkThree] using hfork)
    (by simpa [FixedExponentStates.checkThree] using hrun)
    (by simpa [FixedExponentStates.checkThree] using hnp)

def gasSteps_checkThree_miss (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 1 ≠ 3)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.checkThree s memory n bsize 1 msize)
      (FixedExponentStates.fallback s memory n bsize 1 msize) :=
  sound FixedExponentPaths.checkThree
    (run_checkThree_miss s memory input n bsize msize hb hvalue hdata hactive
      heoff hcode hrun)
    (by simpa [FixedExponentStates.checkThree, Artifact.submissionArtifact] using hcode)
    (by simpa [FixedExponentStates.checkThree] using hfork)
    (by simpa [FixedExponentStates.checkThree] using hrun)
    (by simpa [FixedExponentStates.checkThree] using hnp)

def gasSteps_check65537_hit (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 3 = 65537)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.check65537 s memory n bsize 3 msize)
      (FixedExponentStates.special s memory n bsize 3 msize 16) :=
  sound (FixedExponentPaths.check65537 ++ FixedExponentPaths.fermatHit)
    (run_check65537_hit s memory input n bsize msize hb hvalue hdata hactive
      heoff hrun)
    (by simpa [FixedExponentStates.check65537, Artifact.submissionArtifact] using hcode)
    (by simpa [FixedExponentStates.check65537] using hfork)
    (by simpa [FixedExponentStates.check65537] using hrun)
    (by simpa [FixedExponentStates.check65537] using hnp)

def gasSteps_check65537_miss (s : State) (memory input : ByteArray)
    (n bsize msize : Nat) (hb : bsize ≤ 256)
    (hvalue : exponentValue input bsize 3 ≠ 65537)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 93 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2912 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedExponentStates.check65537 s memory n bsize 3 msize)
      (FixedExponentStates.fallback s memory n bsize 3 msize) :=
  sound FixedExponentPaths.check65537
    (run_check65537_miss s memory input n bsize msize hb hvalue hdata hactive
      heoff hcode hrun)
    (by simpa [FixedExponentStates.check65537, Artifact.submissionArtifact] using hcode)
    (by simpa [FixedExponentStates.check65537] using hfork)
    (by simpa [FixedExponentStates.check65537] using hrun)
    (by simpa [FixedExponentStates.check65537] using hnp)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentValueTrace
