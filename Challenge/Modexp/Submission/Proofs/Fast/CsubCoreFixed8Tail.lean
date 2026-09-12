import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreFixed8Step7
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
attribute [local irreducible] csStep
set_option linter.unusedSimpArgs false in
theorem run_csFixedTail8 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat) (_hn : 2 ≤ 8) (_hn32 : 8 ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2784 =
      UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2912)
    (hsrcFit : (csSrc memory 8 8).toNat + 32 * 8 ≤ 2912) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTail8
      (csFixedState s memory 8 8 5073 pdst ret rest) =
      some (subReturnedState s memory 8 8 pdst ret rest) := by
  have h5243 : (5098 : UInt256).toNat = 5098 := by decide
  have heq5243 : (5098 : UInt256) = UInt256.ofNat 5098 := by decide
  have hbig : (20000 : Nat) < 2 ^ 256 := by norm_num
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h9344 : (2784 : UInt256).toNat = 2784 := by decide
  have hsz : 32 * 8 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 8 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := activeWords_fix s 2784 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 8) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 8) (by omega) (by omega) hact
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (csSrc memory 8 8).toNat (32 * 8)) = s.activeWords :=
    activeWords_fix s _ (32 * 8) (by omega) (by omega) hact
  have hsrcEq : (2112 : UInt256) +
      (115792089237316195423570985008687907853269984665640564039457584007913129639616 :
        UInt256) *
        UInt256.lor (MachineState.readWord (csStep memory 8 8).memory 2080)
          (UInt256.isZero (csStep memory 8 8).flag) = csSrc memory 8 8 := rfl
  simp (config := { maxSteps := 400000 })
    [h5243, heq5243, jumpDestCopyResume, csFixedTail8, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, subReturnedState, hsrcEq, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc1, hc2, hc3, hc4, hc5, hc6, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]


end Challenge.Modexp.Submission.Proofs.Fast.Csub
