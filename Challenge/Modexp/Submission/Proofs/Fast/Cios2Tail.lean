import Challenge.Modexp.Submission.Proofs.Fast.Cios2Constants
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Out
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # CIOS2 row tail and direct CSUB exit -/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Tail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Entry
open Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail

theorem jumpDest4115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4809 = true := by
  exact Artifact.isValidJumpDest_index 2936 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_tailNext (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2TailLoop
      (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest) =
      some (outState s (tailMem mem c) pa pb n (i + 1) pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have h4115 : (4809 : UInt256).toNat = 4809 := by decide
  have h4115' : (4809 : UInt256) = UInt256.ofNat 4809 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (4809 : UInt256).toNat = true := by
    rw [h4115]
    exact jumpDest4115
  have hnextB : ptrAt (pb + 32 * n - 32) (i + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 2 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpbmN : (pb - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pb - 32 < pb + 32 * (n - 2 - i) := by omega
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) = s.activeWords :=
    activeWords_fix s 8256 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) = s.activeWords :=
    activeWords_fix s 8192 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cios2TailLoop, cios2Tail, Cios2Paths.Tail.tailPC,
      Cios2Paths.Tail.startIndex, Cios2Paths.Tail.opAt,
      Cios2Paths.Tail.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Cios2Constants.notThirtyOne, Cios2Constants.notZero,
      tailState, outState, tailMem, tailMem1, fastPC14, fastPC15,
      hc5, hc6, hc7, hc8, hc9, hc10, hrun, hcode, hK, h8192, h8224, h8256,
      h4115, h4115', hjump, jumpDest4115, hnextB, hpbmN, hgt,
      hactN, hactS, hactP, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_tailLast (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2Tail
      (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest) =
      some (mpCsubState s (tailMem mem c) pdst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have h2642 : (2610 : UInt256).toNat = 2610 := by decide
  have h2642' : (2610 : UInt256) = UInt256.ofNat 2610 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (2610 : UInt256).toNat = true := by
    rw [h2642]
    exact jumpDest2642
  have hnextB : ptrAt (pb + 32 * n - 32) (i + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpbmN : (pb - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) = s.activeWords :=
    activeWords_fix s 8256 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) = s.activeWords :=
    activeWords_fix s 8192 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cios2Tail, Cios2Paths.Tail.tailPC, Cios2Paths.Tail.startIndex,
      Cios2Paths.Tail.opAt, Cios2Paths.Tail.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Cios2Constants.notThirtyOne, Cios2Constants.notZero,
      tailState, mpCsubState, tailMem, tailMem1, fastPC14, fastPC15,
      hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hrun, hcode,
      hK, h8192, h8224, h8256, h2642, h2642', hjump, jumpDest2642,
      hnextB, hpbmN, hactN, hactS, hactP, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

opaque gasSteps_tailNext (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest)
      (outState s (tailMem mem c) pa pb n (i + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2TailLoop hcode hfork
    (run_tailNext s mem pmj ptj c mu bi pa pb n i pdst ret rest hcap hrun hcode
      hact hn32 hi hpb hpbFit) hrun hnp

opaque gasSteps_tailLast (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest)
      (mpCsubState s (tailMem mem c) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2Tail hcode hfork
    (run_tailLast s mem pmj ptj c mu bi pa pb n i pdst ret rest hcap hrun hcode
      hact hn32 hi hpb hpbFit) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Tail
