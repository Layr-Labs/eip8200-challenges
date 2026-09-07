import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# One-MAC certificates for the two-limb CIOS L1 block

The first copied MAC ends at pc 4275.  The second copied MAC starts there and
owns the shared pair-loop test.  Keeping the two traces separate bounds concrete
instruction reduction and lets the pair trace be composed with `GasSteps.trans`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

/-- L1 state at an arbitrary copied-body boundary. -/
def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     (l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

abbrev l1State := l1At 4136

/-- Row middle reached after the final L1 MAC. -/
def midState (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4420
           stack := [paj, ptj, c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

theorem jumpDest4136 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4136 = true := by
  exact Artifact.isValidJumpDest_index 2726 (by rfl)

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_l1FirstMac (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstMac
      (l1At 4136 s mem bi pa pb n i j pdst ret rest) =
      some (l1At 4275 s mem bi pa pb n i (j + 1) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hpaj : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hnextA : ptrAt (pa + 32 * n - 32) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 2 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pa - 32 < pa + 32 * (n - 2 - j) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [firstMac, Cios2Paths.L1.firstPC, Cios2Paths.L1.firstStartIndex,
      Cios2Paths.L1.firstOpAt, Cios2Paths.L1.firstPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      hc9, hc10, hc11, hc12, hc13, hrun, hcode, hK,
      hpaj, hptj, hnextA, hpamN, hgt, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_l1SecondMacBody (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondMac
      (l1At 4275 s mem bi pa pb n i k pdst ret rest) =
      some (l1At 4136 s mem bi pa pb n i (k + 1) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h4136 : (4136 : UInt256).toNat = 4136 := by decide
  have h4136' : (4136 : UInt256) = UInt256.ofNat 4136 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (4136 : UInt256).toNat = true := by
    rw [h4136]
    exact jumpDest4136
  have hpaj : ptrAt (pa + 32 * n - 32) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8224 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hnextA : ptrAt (pa + 32 * n - 32) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pa - 32 < pa + 32 * (n - 2 - k) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [secondMac, Cios2Paths.L1.secondPC, Cios2Paths.L1.secondStartIndex,
      Cios2Paths.L1.secondOpAt, Cios2Paths.L1.secondPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      hc9, hc10, hc11, hc12, hc13, hrun, hcode, hK, h4136, h4136', hjump,
      jumpDest4136, hpaj, hptj, hnextA, hpamN, hgt, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_l1SecondMacExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondMac
      (l1At 4275 s mem bi pa pb n i k pdst ret rest) =
      some (midState s (l1Step mem bi pa n (k + 1)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (k + 1)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (k + 1)))
        (l1Step mem bi pa n (k + 1)).carry bi pa pb n i pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hpaj : ptrAt (pa + 32 * n - 32) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8224 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hnextA : ptrAt (pa + 32 * n - 32) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [secondMac, Cios2Paths.L1.secondPC, Cios2Paths.L1.secondStartIndex,
      Cios2Paths.L1.secondOpAt, Cios2Paths.L1.secondPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, midState, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      hc9, hc10, hc11, hc12, hc13, hrun, hK,
      hpaj, hptj, hnextA, hpamN, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

def gasSteps_l1FirstMac (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4136 s mem bi pa pb n i j pdst ret rest)
      (l1At 4275 s mem bi pa pb n i (j + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka firstMac hcode hfork
    (run_l1FirstMac s mem bi pa pb n i j pdst ret rest hcap hrun hcode hact hn32 hj
      hpa hpaFit) hrun hnp

def gasSteps_l1SecondMacBody (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4275 s mem bi pa pb n i k pdst ret rest)
      (l1At 4136 s mem bi pa pb n i (k + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka secondMac hcode hfork
    (run_l1SecondMacBody s mem bi pa pb n i k pdst ret rest hcap hrun hcode hact
      hn32 hk hpa hpaFit) hrun hnp

def gasSteps_l1SecondMacExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4275 s mem bi pa pb n i k pdst ret rest)
      (midState s (l1Step mem bi pa n (k + 1)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (k + 1)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (k + 1)))
        (l1Step mem bi pa n (k + 1)).carry bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka secondMac hcode hfork
    (run_l1SecondMacExit s mem bi pa pb n i k pdst ret rest hcap hrun hact hn32
      hk hpa hpaFit) hrun hnp

/-- One pair iteration is exactly two independently priced MAC traces. -/
def gasSteps_l1Pair (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 2 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4136 s mem bi pa pb n i j pdst ret rest)
      (l1At 4136 s mem bi pa pb n i (j + 2) pdst ret rest) :=
  (gasSteps_l1FirstMac s mem bi pa pb n i j pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans
    (gasSteps_l1SecondMacBody s mem bi pa pb n i (j + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega) hpa hpaFit)

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
