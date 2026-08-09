import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionExec

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ResidentSegment

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

set_option linter.unusedSimpArgs false in
theorem runFirstSetup (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat)
    (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hrun : base.halt = .Running)
    (hW : MachineState.readWord base.memory (Compression.pairWPtr j).toNat =
      Compression.wValue ghost j)
    (hK : UInt256.ofNat 0xffffffff &&&
        MachineState.readWord base.memory (Compression.pairKPtr j).toNat =
      Compression.kValue ghost j) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairFirstSetupPath
      (Compression.residentAfterCondition base ghost msgOff returnDest rest j) =
        some (Compression.residentCallT10 base ghost msgOff returnDest rest j) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 163 = true := by decide
  have h163 : (163 : UInt256).toNat = 163 := by decide
  have h163Eq : (163 : UInt256) = UInt256.ofNat 163 := by decide
  have h708Eq : (708 : UInt256) = UInt256.ofNat 708 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have hKland : UInt256.land (UInt256.ofNat 0xffffffff)
        (MachineState.readWord base.memory (Compression.pairKPtr j).toNat) =
      Compression.kValue ghost j := by
    change UInt256.ofNat 0xffffffff &&&
      MachineState.readWord base.memory (Compression.pairKPtr j).toNat = _
    exact hK
  have hkPlus : UInt256.land (UInt256.ofNat 0xffffffff)
        (MachineState.readWord base.memory (Compression.pairKPtr j).toNat) +
        Compression.hValue ghost 7 =
      Compression.hValue ghost 7 + Compression.kValue ghost j := by
    rw [hKland]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  simp [Compression.pairFirstSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.residentAfterCondition, Compression.residentAt,
    Compression.residentCallT10, Compression.residentFirstInputsLoaded,
    Compression.loadedWord, BigSigma.t1Entry, List.exchange,
    Nat.add_assoc, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
    hc21, hc22, hc23, hc24, hcode, hrun, hdest, hW, hK, hKland, hkPlus,
    h163, h163Eq, h708Eq, hmaskEq,
    State.activeWordsAfterUInt256]
  exact Challenge.EvmProof.Word.word_add_comm _ _

set_option linter.unusedSimpArgs false in
theorem runFirstT2Setup (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairFirstT2SetupPath
      (Compression.residentAfterT10 base ghost msgOff returnDest rest j) =
        some (Compression.residentCallT20 base ghost msgOff returnDest rest j) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 114 = true := by decide
  have h114 : (114 : UInt256).toNat = 114 := by decide
  have h114Eq : (114 : UInt256) = UInt256.ofNat 114 := by decide
  have h728Eq : (728 : UInt256) = UInt256.ofNat 728 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have qrun :
      (Compression.residentFirstInputsLoaded base ghost msgOff returnDest rest j).halt =
        .Running := by
    change base.halt = .Running
    exact hrun
  have qcode :
      (Compression.residentFirstInputsLoaded base ghost msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change base.executionEnv.code = submissionBytecode
    exact hcode
  simp [Compression.pairFirstT2SetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.residentAfterT10, Compression.residentCallT20,
    Compression.t10,
    BigSigma.t1Returned, BigSigma.t2Entry, List.exchange, Nat.add_assoc,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19,
    hcode, hrun, qrun, qcode, hdest, h114, h114Eq, h728Eq, hmaskEq]

set_option linter.unusedSimpArgs false in
theorem runSecondT1Setup (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hrun : base.halt = .Running)
    (hW : MachineState.readWord base.memory
        (UInt256.ofNat 32 + Compression.pairWPtr j).toNat =
      Compression.wValue ghost (j + 1))
    (hK : UInt256.land (UInt256.ofNat 0xffffffff)
        (MachineState.readWord base.memory
          (UInt256.ofNat 4 + Compression.pairKPtr j).toNat) =
      Compression.kValue ghost (j + 1)) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairSecondT1SetupPath
      (Compression.residentAfterT20 base ghost msgOff returnDest rest j) =
        some (Compression.residentCallT11 base ghost msgOff returnDest rest j) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 163 = true := by decide
  have h163 : (163 : UInt256).toNat = 163 := by decide
  have h163Eq : (163 : UInt256) = UInt256.ofNat 163 := by decide
  have h783Eq : (783 : UInt256) = UInt256.ofNat 783 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have h32Eq : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h4Eq : (4 : UInt256) = UInt256.ofNat 4 := by decide
  have hwComm : UInt256.ofNat 32 + Compression.pairWPtr j =
      Compression.pairWPtr j + UInt256.ofNat 32 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hkComm : UInt256.ofNat 4 + Compression.pairKPtr j =
      Compression.pairKPtr j + UInt256.ofNat 4 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hWrev : MachineState.readWord base.memory
        (Compression.pairWPtr j + UInt256.ofNat 32).toNat =
      Compression.wValue ghost (j + 1) := by
    rw [← hwComm]
    exact hW
  have hKrev : UInt256.land (UInt256.ofNat 0xffffffff)
        (MachineState.readWord base.memory
          (Compression.pairKPtr j + UInt256.ofNat 4).toNat) =
      Compression.kValue ghost (j + 1) := by
    rw [← hkComm]
    exact hK
  have hand (a b : UInt256) : a &&& b = b &&& a := by
    apply Challenge.EvmProof.Word.word_ext
    change (a.val &&& b.val).val = (b.val &&& a.val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  have hpairE : UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t10 ghost j + Compression.hValue ghost 3) =
      Compression.pairE1 ghost j := by
    unfold Compression.pairE1 Challenge.EvmProof.Word.mask32
    rw [show UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t10 ghost j + Compression.hValue ghost 3) =
      UInt256.ofNat 0xffffffff &&&
        (Compression.t10 ghost j + Compression.hValue ghost 3) by rfl,
      hand, Challenge.EvmProof.Word.word_add_comm]
  have hpairA : UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t10 ghost j + Compression.t20 ghost) =
      Compression.pairA1 ghost j := by
    unfold Compression.pairA1 Challenge.EvmProof.Word.mask32
    rw [show UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t10 ghost j + Compression.t20 ghost) =
      UInt256.ofNat 0xffffffff &&&
        (Compression.t10 ghost j + Compression.t20 ghost) by rfl,
      hand, Challenge.EvmProof.Word.word_add_comm]
  have qrun :
      (Compression.residentAfterT20 base ghost msgOff returnDest rest j).halt =
        .Running := by
    change base.halt = .Running
    exact hrun
  have qcode :
      (Compression.residentAfterT20 base ghost msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change base.executionEnv.code = submissionBytecode
    exact hcode
  have qrun0 :
      (Compression.residentAfterT10 base ghost msgOff returnDest rest j).halt =
        .Running := by
    change base.halt = .Running
    exact hrun
  have qcode0 :
      (Compression.residentAfterT10 base ghost msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change base.executionEnv.code = submissionBytecode
    exact hcode
  have qmem :
      (Compression.residentAfterT10 base ghost msgOff returnDest rest j).memory =
        base.memory := by rfl
  simp [Compression.pairSecondT1SetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.residentAfterT20, Compression.residentCallT11,
    Compression.residentSecondInputsLoaded, Compression.loadedWord,
    BigSigma.t2Returned, BigSigma.t1Entry, List.exchange, Nat.add_assoc,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21,
    hc22, hc23, hc24, hcode, hrun, qrun, qcode, qrun0, qcode0,
    hdest, h163, h163Eq, h783Eq, hmaskEq, h32Eq, h4Eq,
    hwComm, hkComm, hW, hK, hWrev, hKrev, hpairE, hpairA, qmem,
    State.activeWordsAfterUInt256]
  constructor
  · exact Challenge.EvmProof.Word.word_add_comm _ _
  · simpa [Compression.t20] using hpairA

set_option linter.unusedSimpArgs false in
theorem runSecondT2Setup (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairSecondT2SetupPath
      (Compression.residentAfterT11 base ghost msgOff returnDest rest j) =
        some (Compression.residentCallT21 base ghost msgOff returnDest rest j) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 114 = true := by decide
  have h114 : (114 : UInt256).toNat = 114 := by decide
  have h114Eq : (114 : UInt256) = UInt256.ofNat 114 := by decide
  have h803Eq : (803 : UInt256) = UInt256.ofNat 803 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have qrun :
      (Compression.residentSecondInputsLoaded base ghost msgOff returnDest rest j).halt =
        .Running := by
    change base.halt = .Running
    exact hrun
  have qcode :
      (Compression.residentSecondInputsLoaded base ghost msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change base.executionEnv.code = submissionBytecode
    exact hcode
  simp [Compression.pairSecondT2SetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.residentAfterT11, Compression.residentCallT21,
    Compression.t11,
    BigSigma.t1Returned, BigSigma.t2Entry, List.exchange, Nat.add_assoc,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21,
    hcode, hrun, qrun, qcode, hdest, h114, h114Eq, h803Eq, hmaskEq]

set_option linter.unusedSimpArgs false in
theorem runCommit (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j + 2 < 65)
    (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairCommitPath
      (Compression.residentAfterT21 base ghost msgOff returnDest rest j) =
        some (Compression.residentAfterPair base ghost msgOff returnDest rest j) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 669 = true := by decide
  have h669 : (669 : UInt256).toNat = 669 := by decide
  have h669Eq : (669 : UInt256) = UInt256.ofNat 669 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have h64Eq : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h8Eq : (8 : UInt256) = UInt256.ofNat 8 := by decide
  have hand (a b : UInt256) : a &&& b = b &&& a := by
    apply Challenge.EvmProof.Word.word_ext
    change (a.val &&& b.val).val = (b.val &&& a.val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  have hpairA : UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t11 ghost j + Compression.t21 ghost j) =
      Compression.pairA2 ghost j := by
    unfold Compression.pairA2 Challenge.EvmProof.Word.mask32
    rw [show UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t11 ghost j + Compression.t21 ghost j) =
      UInt256.ofNat 0xffffffff &&&
        (Compression.t11 ghost j + Compression.t21 ghost j) by rfl,
      hand, Challenge.EvmProof.Word.word_add_comm]
  have hpairE : UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t11 ghost j + Compression.hValue ghost 2) =
      Compression.pairE2 ghost j := by
    unfold Compression.pairE2 Challenge.EvmProof.Word.mask32
    rw [show UInt256.land (UInt256.ofNat 0xffffffff)
        (Compression.t11 ghost j + Compression.hValue ghost 2) =
      UInt256.ofNat 0xffffffff &&&
        (Compression.t11 ghost j + Compression.hValue ghost 2) by rfl,
      hand, Challenge.EvmProof.Word.word_add_comm]
  have hwInc : UInt256.ofNat 64 + Compression.pairWPtr j =
      Compression.pairWPtr (j + 2) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    unfold Compression.pairWPtr
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega
  have hkInc : UInt256.ofNat 8 + Compression.pairKPtr j =
      Compression.pairKPtr (j + 2) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    unfold Compression.pairKPtr
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega
  have qrun :
      (Compression.residentSecondInputsLoaded base ghost msgOff returnDest rest j).halt =
        .Running := by
    change base.halt = .Running
    exact hrun
  have qcode :
      (Compression.residentSecondInputsLoaded base ghost msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change base.executionEnv.code = submissionBytecode
    exact hcode
  have qrun1 :
      (Compression.residentAfterT11 base ghost msgOff returnDest rest j).halt =
        .Running := by
    change base.halt = .Running
    exact hrun
  have qcode1 :
      (Compression.residentAfterT11 base ghost msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change base.executionEnv.code = submissionBytecode
    exact hcode
  simp [Compression.pairCommitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.residentAfterT21, Compression.residentAfterPair,
    Compression.t21, Compression.t11, BigSigma.t2Returned,
    BigSigma.t1Returned, List.exchange, Nat.add_assoc,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21,
    hcode, hrun, qrun, qcode, qrun1, qcode1, hdest,
    h669, h669Eq, hmaskEq, h64Eq, h8Eq, hpairA, hpairE, hwInc, hkInc]
  constructor
  · simpa [Compression.t11, Compression.t21] using hpairA
  · simpa [Compression.t11] using hpairE

end Challenge.Sha256.Submission.Proofs.Bytecode.ResidentSegment
