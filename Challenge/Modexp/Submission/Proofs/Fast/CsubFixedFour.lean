import Challenge.Modexp.Submission.Proofs.Fast.CsubFixedEight

set_option warningAsError true
set_option linter.unusedSimpArgs false
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

attribute [local irreducible] csStep

theorem run_csFixedEntry4 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * 4)) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedEntry4
      (csEntryState s memory pdst ret rest) =
      some (csFixedState s memory 4 0 5313 pdst ret rest) := by
  have hactS := activeWords_fix s 9344 32 (by decide) (by decide) hact
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hword9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hword128 : (128 : UInt256).toNat = 128 := by decide
  have hword256 : (256 : UInt256).toNat = 256 := by decide
  have hword4972 : (4978 : UInt256).toNat = 4978 := by decide
  have hword5022 : (5026 : UInt256).toNat = 5026 := by decide
  have hword5131 : (5312 : UInt256).toNat = 5312 := by decide
  have hword2225 : (2144 : UInt256).toNat = 2144 := by decide
  have hwordEq4972 : (4978 : UInt256) = UInt256.ofNat 4978 := by decide
  have hwordEq5022 : (5026 : UInt256) = UInt256.ofNat 5026 := by decide
  have hwordEq5131 : (5312 : UInt256) = UInt256.ofNat 5312 := by decide
  have hwordEq2225 : (2144 : UInt256) = UInt256.ofNat 2144 := by decide
  have hwordZero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedEntry4, csEntryState, csFixedState, csStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hrun, hcode, hs32, hactS, hc2, hc3, hc4, hc5,
      UInt256.eq, UInt256.isTrue, opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword9344, hword128, hword256, hword4972, hword5022, hword5131, hword2225, hwordEq4972, hwordEq5022, hwordEq5131, hwordEq2225, hwordZero, List.exchange]


theorem run_csFixedStep4_0 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_0
      (csFixedState s memory 4 0 5313 pdst ret rest) =
      some (csFixedState s memory 4 1 5136 pdst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 96 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 8352 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 7264 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 1 =
      (let prev := csStep memory 4 0
       let t := MachineState.readWord prev.memory (8256 + 32 * (4 - 1 - 0))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 0))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (7168 + 32 * (4 - 1 - 0))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 0
  have hword96 : (96 : UInt256).toNat = 96 := by decide
  have hword8352 : (8352 : UInt256).toNat = 8352 := by decide
  have hword7264 : (7264 : UInt256).toNat = 7264 := by decide
  have hword5117 : (5136 : UInt256).toNat = 5136 := by decide
  have hwordEq5117 : (5136 : UInt256) = UInt256.ofNat 5136 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_0, csFixedState, fixedOrComm, hstep, csStep, fixedSubtractZero, hrun, hcode,
      hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword96, hword8352, hword7264, hword5117, hwordEq5117, List.exchange]
  try (split <;> decide)


theorem run_csFixedStep4_1 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_1
      (csFixedState s memory 4 1 5136 pdst ret rest) =
      some (csFixedState s memory 4 2 5160 pdst ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 64 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 8320 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 7232 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 2 =
      (let prev := csStep memory 4 1
       let t := MachineState.readWord prev.memory (8256 + 32 * (4 - 1 - 1))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 1))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (7168 + 32 * (4 - 1 - 1))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 1
  have hword64 : (64 : UInt256).toNat = 64 := by decide
  have hword8320 : (8320 : UInt256).toNat = 8320 := by decide
  have hword7232 : (7232 : UInt256).toNat = 7232 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_1, csFixedState, fixedOrComm, hstep, hrun,
      hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword64, hword8320, hword7232, List.exchange]


theorem run_csFixedStep4_2 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_2
      (csFixedState s memory 4 2 5160 pdst ret rest) =
      some (csFixedState s memory 4 3 5183 pdst ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 32 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 8288 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 7200 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 3 =
      (let prev := csStep memory 4 2
       let t := MachineState.readWord prev.memory (8256 + 32 * (4 - 1 - 2))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 2))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (7168 + 32 * (4 - 1 - 2))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 2
  have hword32 : (32 : UInt256).toNat = 32 := by decide
  have hword8288 : (8288 : UInt256).toNat = 8288 := by decide
  have hword7200 : (7200 : UInt256).toNat = 7200 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_2, csFixedState, fixedOrComm, hstep, hrun,
      hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword32, hword8288, hword7200, List.exchange]


theorem run_csFixedStep4_3 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_3
      (csFixedState s memory 4 3 5183 pdst ret rest) =
      some (csFixedState s memory 4 4 5205 pdst ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 0 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 8256 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 7168 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 4 =
      (let prev := csStep memory 4 3
       let t := MachineState.readWord prev.memory (8256 + 32 * (4 - 1 - 3))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 3))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (7168 + 32 * (4 - 1 - 3))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 3
  have hword0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hword8256 : (8256 : UInt256).toNat = 8256 := by decide
  have hword7168 : (7168 : UInt256).toNat = 7168 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_3, csFixedState, fixedOrComm, hstep, hrun,
      hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword0, hzeroNat, hword8256, hword7168, List.exchange]


theorem run_csFixedTail4 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) (_hn : 2 ≤ 4) (_hn32 : 4 ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 9344 =
      UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 9472)
    (hsrcFit : (csSrc memory 4 4).toNat + 32 * 4 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTail4
      (csFixedState s memory 4 4 5205 pdst ret rest) =
      some (csReturnedState s memory 4 4 pdst ret rest) := by
  have hbig : (20000 : Nat) < 2 ^ 256 := by norm_num
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsz : 32 * 4 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 4 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 4) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 4) (by omega) (by omega) hact
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (csSrc memory 4 4).toNat (32 * 4)) = s.activeWords :=
    activeWords_fix s _ (32 * 4) (by omega) (by omega) hact
  have hsrcEq : (8256 : UInt256) +
      (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
        UInt256) *
        UInt256.lor (MachineState.readWord (csStep memory 4 4).memory 8224)
          (UInt256.isZero (csStep memory 4 4).flag) = csSrc memory 4 4 := rfl
  simp (config := { maxSteps := 400000 })
    [csFixedTail4, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, csReturnedState, hsrcEq, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc1, hc2, hc3, hc4, hc5, hc6, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

def gasSteps_csFixed4 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs : MachineState.readWord memory 9344 = UInt256.ofNat (32 * 4))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 9344 = UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 9472)
    (hsrcFit : (csSrc memory 4 4).toNat + 32 * 4 ≤ 9472) :
    Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
      (csReturnedState s memory 4 4 pdst ret rest) := by

  have hEntry4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedEntry4
    (by simpa [csEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [csEntryState, State.fork] using hfork)
    (run_csFixedEntry4 s memory pdst ret rest hcap hrun hcode hact hs)
    (by simpa [csEntryState] using hrun)
    (by simpa [csEntryState, State.fork] using hnp)

  have hStep4_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_0
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_0 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_1
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_1 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_2
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_2 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_3
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_3 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hTail4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedTail4
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedTail4 s memory pdst ret rest hcap hrun hcode hact (by decide) (by decide) hjump hs32 hdstFit hsrcFit)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  exact ((((hEntry4.trans hStep4_0).trans hStep4_1).trans hStep4_2).trans hStep4_3).trans hTail4

end Challenge.Modexp.Submission.Proofs.Fast.Csub
