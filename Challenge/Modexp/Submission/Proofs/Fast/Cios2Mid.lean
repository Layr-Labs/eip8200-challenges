import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Mid

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # CIOS2 row middle -/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Mid

/-- L2 state at either the peeled head or the paired-loop head. -/
def l2At (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (32 * n - 64) k),
                     UInt256.ofNat (ptrAt (8192 + 32 * n) k),
                     (l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

set_option linter.unusedSimpArgs false in
theorem run_mid (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2Mid
      (midState s mem paj ptj c bi pa pb n i pdst ret rest) =
      some (l2At 4921 s (midMem mem c) bi (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 pdst ret rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hTLN : (8224 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hMLN : (32 * n - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n - 32 := Nat.mod_eq_of_lt (by omega)
  have hsc1 : 8256 ≤ 8224 + 32 * n := by omega
  have hsc2 : 32 * n - 32 + 32 ≤ 8192 := by omega
  have hsc3 : 32 * n ≤ 8192 := by omega
  have hsubTL : UInt256.ofNat (8224 + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (8192 + 32 * n) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hsubML : UInt256.ofNat (32 * n - 32) - UInt256.ofNat 32 =
      UInt256.ofNat (32 * n - 64) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) = s.activeWords :=
    activeWords_fix s 8192 32 (by decide) (by omega) hact
  have hactTL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) = s.activeWords :=
    activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactT0 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat (8224 + 32 * n) 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactMI : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9376 32) = s.activeWords :=
    activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hactML : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) = s.activeWords :=
    activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hactM0 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat (32 * n - 32) 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cios2Mid, Cios2Paths.Mid.midPC, Cios2Paths.Mid.startIndex,
      Cios2Paths.Mid.opAt, Cios2Paths.Mid.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState, l2At, l2Step, midMem, midMem1, rowMu, rowC0, mulHi,
      zero_lt_eq_double_isZero,
      maxWord_literal, fastPC12, fastPC13, readWord_midMem_peel,
      hc6, hc7, hc8, hc9, hc10, hc11, hrun, h32, h8192, h8224, h9376, h9408, h9440,
      hml, htl, hTLN, hMLN, hsubTL, hsubML, hsc1, hsc2, hsc3,
      hactN, hactP, hactTL, hactT0, hactMI, hactML, hactM0,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

opaque gasSteps_mid (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps
      (midState s mem paj ptj c bi pa pb n i pdst ret rest)
      (l2At 4921 s (midMem mem c) bi (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2Mid hcode hfork
    (run_mid s mem paj ptj c bi pa pb n i pdst ret rest hcap hrun hact hn hn32
      hml htl) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid
