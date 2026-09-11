import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart19

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem run_csEntry (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (hn8 : n ≠ 8) (hn4 : n ≠ 4)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord memory 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock csGenericPath
      (csEntryState s memory pdst ret rest) =
      some (csLoopState s memory n 0 pdst ret rest) := by
  have hbig : (20000 : Nat) < 2 ^ 256 := by norm_num
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hadd : (7168 : UInt256) + UInt256.ofNat (32 * n - 32) =
      UInt256.ofNat (7136 + 32 * n) := by
    rw [show (7168 : UInt256) = UInt256.ofNat 7168 from by decide,
      Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  have hactA : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) =
      s.activeWords := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hactS := activeWords_fix s 9344 32 (by decide) (by decide) hact
  have hne8 : 256 ≠ 32 * n := by omega
  have hne4 : 128 ≠ 32 * n := by omega
  have hsz : 32 * n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32 * n := Nat.mod_eq_of_lt (by omega)
  have hword9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hword128 : (128 : UInt256).toNat = 128 := by decide
  have hword256 : (256 : UInt256).toNat = 256 := by decide
  have hword4972 : (4978 : UInt256).toNat = 4978 := by decide
  have hword5022 : (5026 : UInt256).toNat = 5026 := by decide
  have hword5131 : (5112 : UInt256).toNat = 5112 := by decide
  have hword2225 : (2144 : UInt256).toNat = 2144 := by decide
  have hwordEq4972 : (4978 : UInt256) = UInt256.ofNat 4978 := by decide
  have hwordEq5022 : (5026 : UInt256) = UInt256.ofNat 5026 := by decide
  have hwordEq5131 : (5112 : UInt256) = UInt256.ofNat 5112 := by decide
  have hwordEq2225 : (2144 : UInt256) = UInt256.ofNat 2144 := by decide
  have hwordZero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 400000 })
    [csGenericPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csEntryState, csLoopState, csStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc2, hc3, hc4, hc5, hc6, hc7, hrun, h9408, h9440, hzero,
      hml, htl, hadd, hactA, hactB, hactS, hcode, hs32, hne8, hne4, hsz,
      UInt256.eq, UInt256.isTrue, jumpDest2225,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hword9344, hword128, hword256, hword4972, hword5022, hword5131, hword2225, hwordEq4972, hwordEq5022, hwordEq5131, hwordEq2225, hwordZero, List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
