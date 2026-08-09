import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionExec
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.PairSegmentTest

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

private theorem activeWordsAfter_lt (curr offset limit : Nat)
    (hcurr : curr < limit) (hoff : offset + 32 < limit) :
    MachineState.activeWordsAfter curr offset 32 < limit := by
  unfold MachineState.activeWordsAfter
  simp only [OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte]
  rw [max_lt_iff]
  constructor
  · exact hcurr
  · have hdiv := Nat.div_le_self (offset + 32 - 1) 32
    calc
      (offset + 32 - 1) / 32 + 1 ≤ (offset + 32 - 1) + 1 :=
        Nat.add_le_add_right hdiv 1
      _ = offset + 32 := by omega
      _ < limit := hoff

set_option linter.unusedSimpArgs false in
theorem runFirstSetup (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairFirstSetupPath
      (Compression.afterPairCondition s msgOff returnDest rest j) =
        some (Compression.callPairT10 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
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
  have h288 : (288 : UInt256).toNat = 288 := by decide
  have h320 : (320 : UInt256).toNat = 320 := by decide
  have h352 : (352 : UInt256).toNat = 352 := by decide
  have h384 : (384 : UInt256).toNat = 384 := by decide
  have h416 : (416 : UInt256).toNat = 416 := by decide
  have h448 : (448 : UInt256).toNat = 448 := by decide
  have h480 : (480 : UInt256).toNat = 480 := by decide
  have h512 : (512 : UInt256).toNat = 512 := by decide
  have h800 : (800 : UInt256).toNat = 800 := by decide
  have h2 : (2 : UInt256).toNat = 2 := by decide
  have h4 : (4 : UInt256).toNat = 4 := by decide
  have h5 : (5 : UInt256).toNat = 5 := by decide
  have hshift :
      (UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) =
        UInt256.ofNat (j * 4) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
      (value := j) (shift := 2) (by omega) (by decide) (by omega)
  have hdirect :
      ((UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) +
        UInt256.ofNat 4).toNat = j * 4 + 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkoff :
      ((UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) +
        UInt256.ofNat 32).toNat = 32 + j * 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmask :
      Challenge.EvmProof.Word.mask32
          (MachineState.readWord s.memory (j * 4 + 4)) =
        Compression.kValue s j := by
    unfold Compression.kValue
    rw [hkoff, PaddedBlockBridge.shiftRight_readWord_224,
      PaddedBlockBridge.mask32_readWord_last4]
    congr 2
    omega
  have hand (a b : UInt256) : a &&& b = b &&& a := by
    apply Challenge.EvmProof.Word.word_ext
    change (a.val &&& b.val).val = (b.val &&& a.val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  have hmask' :
      UInt256.ofNat 0xffffffff &&&
          MachineState.readWord s.memory (j * 4 + 4) =
        Compression.kValue s j := by
    rw [hand]
    simpa [Challenge.EvmProof.Word.mask32] using hmask
  have hadd4 :
      UInt256.ofNat 4 + (UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) =
        (UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) + UInt256.ofNat 4 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have haddr800 :
      UInt256.ofNat 800 + (UInt256.ofNat j).shiftLeft (UInt256.ofNat 5) =
        (UInt256.ofNat j).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 800 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hmaskRev :
      UInt256.ofNat 0xffffffff &&&
          MachineState.readWord s.memory
            (UInt256.ofNat 4 +
              (UInt256.ofNat j).shiftLeft (UInt256.ofNat 2)).toNat =
        Compression.kValue s j := by
    rw [hadd4, hdirect]
    exact hmask'
  have hoff0 :
      (UInt256.shiftLeft 0 (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 288 := by
    decide
  have hoff1 :
      ((UInt256.ofNat 1).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 320 := by
    decide
  have hoff2 :
      ((UInt256.ofNat 2).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 352 := by
    decide
  have hoff3 :
      ((UInt256.ofNat 3).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 384 := by
    decide
  have hoff4 :
      ((UInt256.ofNat 4).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 416 := by
    decide
  have hoff5 :
      ((UInt256.ofNat 5).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 448 := by
    decide
  have hoff6 :
      ((UInt256.ofNat 6).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 480 := by
    decide
  have hoff7 :
      ((UInt256.ofNat 7).shiftLeft (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 512 := by
    decide
  have h163Eq : (163 : UInt256) = UInt256.ofNat 163 := by decide
  have h717Eq : (717 : UInt256) = UInt256.ofNat 717 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have h2Eq : (2 : UInt256) = UInt256.ofNat 2 := by decide
  have h4Eq : (4 : UInt256) = UInt256.ofNat 4 := by decide
  have h5Eq : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h800Eq : (800 : UInt256) = UInt256.ofNat 800 := by decide
  have haddr800' :
      (800 : UInt256) + (UInt256.ofNat j).shiftLeft (5 : UInt256) =
        (UInt256.ofNat j).shiftLeft (5 : UInt256) + (800 : UInt256) :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hdirectRev :
      ((4 : UInt256) + (UInt256.ofNat j).shiftLeft (2 : UInt256)).toNat =
        j * 4 + 4 := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hdirect
  have hmaskGoal :
      UInt256.ofNat 0xffffffff &&&
          MachineState.readWord s.memory
            ((4 : UInt256) +
              (UInt256.ofNat j).shiftLeft (2 : UInt256)).toNat =
        Compression.kValue s j := by
    rw [hdirectRev]
    exact hmask'
  have hmaskLandGoal :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory
            ((4 : UInt256) +
              (UInt256.ofNat j).shiftLeft (2 : UInt256)).toNat) =
        Compression.kValue s j := by
    change UInt256.ofNat 0xffffffff &&&
        MachineState.readWord s.memory
          ((4 : UInt256) +
            (UInt256.ofNat j).shiftLeft (2 : UInt256)).toNat = _
    exact hmaskGoal
  have hwPtrNat :
      (Compression.pairWPtr j).toNat =
        Accessors.slotOffset 800 (UInt256.ofNat j) := by
    have hshift5 :
        (UInt256.ofNat j).shiftLeft (UInt256.ofNat 5) =
          UInt256.ofNat (j * 32) := by
      simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := j) (shift := 5) (by omega) (by decide) (by omega)
    unfold Compression.pairWPtr Accessors.slotOffset
    rw [hshift5, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    repeat' rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hkPtrNat : (Compression.pairKPtr j).toNat = j * 4 + 4 := by
    unfold Compression.pairKPtr
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hreadWPtr :
      MachineState.readWord s.memory (Compression.pairWPtr j).toNat =
        Compression.wValue s j := by
    unfold Compression.wValue
    rw [hwPtrNat]
  have hmaskKPtr :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory (Compression.pairKPtr j).toNat) =
        Compression.kValue s j := by
    rw [hkPtrNat]
    change UInt256.ofNat 0xffffffff &&&
      MachineState.readWord s.memory (j * 4 + 4) = _
    exact hmask'
  have hkPlusH :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory (Compression.pairKPtr j).toNat) +
        Compression.hValue s 7 =
      Compression.hValue s 7 + Compression.kValue s j := by
    rw [hmaskKPtr]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  have hmaskKNat :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory (j * 4 + 4)) =
        Compression.kValue s j := by
    change UInt256.ofNat 0xffffffff &&&
      MachineState.readWord s.memory (j * 4 + 4) = _
    exact hmask'
  simp [Compression.pairFirstSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.afterPairCondition, Compression.callPairT10,
    Compression.firstPairInputsLoaded, Compression.loadedWord,
    Compression.hValue, Compression.wValue,
    BigSigma.t1Entry, Accessors.slotOffset, List.exchange,
    hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hcode, hrun,
    hdest, h163, h288, h320, h352, h384, h416, h448, h480, h512, h800,
    h2, h4, h5, hdirect, hmask', haddr800, hadd4, hmaskRev,
    hoff0, hoff1, hoff2, hoff3, hoff4, hoff5, hoff6, hoff7,
    h163Eq, h717Eq, hmaskEq, hwPtrNat, hkPtrNat, hreadWPtr, hmaskKPtr,
    hmaskLandGoal, hkPlusH,
    State.activeWordsAfterUInt256]
  exact ⟨by
    rw [hmaskKNat]
    exact Challenge.EvmProof.Word.word_add_comm _ _, hmaskKNat⟩

set_option linter.unusedSimpArgs false in
theorem runFirstT2Setup (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairFirstT2SetupPath
      (Compression.afterPairT10 s msgOff returnDest rest j) =
        some (Compression.callPairT20 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 114 = true := by decide
  have h736 : (736 : UInt256).toNat = 736 := by decide
  have h114 : (114 : UInt256).toNat = 114 := by decide
  have h114Eq : (114 : UInt256) = UInt256.ofNat 114 := by decide
  have h737Eq : (737 : UInt256) = UInt256.ofNat 737 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have qrun :
      (Compression.firstPairInputsLoaded s msgOff returnDest rest j).halt =
        .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (Compression.firstPairInputsLoaded s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  simp [Compression.pairFirstT2SetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.afterPairT10, Compression.callPairT20,
    Compression.t10, BigSigma.t1Returned, BigSigma.t2Entry,
    List.exchange, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hcode, hrun, qrun, qcode,
    h736, h114, h114Eq, h737Eq, hmaskEq, hdest]

set_option linter.unusedSimpArgs false in
theorem runSecondT1Setup (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j + 1 < 64)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairSecondT1SetupPath
      (Compression.afterPairT20 s msgOff returnDest rest j) =
        some (Compression.callPairT11 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
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
  have hadd : UInt256.ofNat 1 + UInt256.ofNat j =
      UInt256.ofNat (j + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have qrun :
      (Compression.afterPairT20 s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (Compression.afterPairT20 s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have qrun0 :
      (Compression.afterPairT10 s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode0 :
      (Compression.afterPairT10 s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have h163 : (163 : UInt256).toNat = 163 := by decide
  have h163Eq : (163 : UInt256) = UInt256.ofNat 163 := by decide
  have h805Eq : (805 : UInt256) = UInt256.ofNat 805 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have h1Eq : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h2Eq : (2 : UInt256) = UInt256.ofNat 2 := by decide
  have h4Eq : (4 : UInt256) = UInt256.ofNat 4 := by decide
  have h5Eq : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h800Eq : (800 : UInt256) = UInt256.ofNat 800 := by decide
  have qmem :
      (Compression.afterPairT10 s msgOff returnDest rest j).memory = s.memory := by
    rfl
  have hshift :
      (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 2) =
        UInt256.ofNat ((j + 1) * 4) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
      (value := j + 1) (shift := 2) (by omega) (by decide) (by omega)
  have hdirect :
      ((UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 2) +
        UInt256.ofNat 4).toNat = (j + 1) * 4 + 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkoff :
      ((UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 2) +
        UInt256.ofNat 32).toNat = 32 + (j + 1) * 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmaskK :
      Challenge.EvmProof.Word.mask32
          (MachineState.readWord s.memory ((j + 1) * 4 + 4)) =
        Compression.kValue s (j + 1) := by
    unfold Compression.kValue
    rw [hkoff, PaddedBlockBridge.shiftRight_readWord_224,
      PaddedBlockBridge.mask32_readWord_last4]
    congr 2
    omega
  have hand (a b : UInt256) : a &&& b = b &&& a := by
    apply Challenge.EvmProof.Word.word_ext
    change (a.val &&& b.val).val = (b.val &&& a.val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  have land_eq (a b : UInt256) : UInt256.land a b = a &&& b := rfl
  have hpairE :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (Compression.t10 s j + Compression.hValue s 3) =
        Compression.pairE1 s j := by
    unfold Compression.pairE1 Challenge.EvmProof.Word.mask32
    rw [land_eq, hand (UInt256.ofNat 0xffffffff),
      Challenge.EvmProof.Word.word_add_comm]
  have hpairA :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (Compression.t10 s j + Compression.t20 s) =
        Compression.pairA1 s j := by
    unfold Compression.pairA1 Challenge.EvmProof.Word.mask32
    rw [land_eq, hand (UInt256.ofNat 0xffffffff),
      Challenge.EvmProof.Word.word_add_comm]
  have haddrW :
      UInt256.ofNat 800 +
          (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 5) =
        (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 5) +
          UInt256.ofNat 800 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have haddrK :
      UInt256.ofNat 4 +
          (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 2) =
        (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 2) +
          UInt256.ofNat 4 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hmaskKLand :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory
            (UInt256.ofNat 4 +
              (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 2)).toNat) =
        Compression.kValue s (j + 1) := by
    rw [haddrK, hdirect, land_eq, hand]
    exact hmaskK
  have hreadW :
      MachineState.readWord s.memory
          (UInt256.ofNat 800 +
            (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 5)).toNat =
        Compression.wValue s (j + 1) := by
    unfold Compression.wValue Accessors.slotOffset
    rw [haddrW]
  have hwNext :
      Compression.pairWPtr j + UInt256.ofNat 32 =
        Compression.pairWPtr (j + 1) := by
    unfold Compression.pairWPtr
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega
  have hkNext :
      Compression.pairKPtr j + UInt256.ofNat 4 =
        Compression.pairKPtr (j + 1) := by
    unfold Compression.pairKPtr
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega
  have hwPtrNextNat :
      (Compression.pairWPtr (j + 1)).toNat =
        Accessors.slotOffset 800 (UInt256.ofNat (j + 1)) := by
    have hshift5 :
        (UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 5) =
          UInt256.ofNat ((j + 1) * 32) := by
      simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := j + 1) (shift := 5) (by omega) (by decide) (by omega)
    unfold Compression.pairWPtr Accessors.slotOffset
    rw [hshift5, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    repeat' rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hkPtrNextNat :
      (Compression.pairKPtr (j + 1)).toNat = (j + 1) * 4 + 4 := by
    unfold Compression.pairKPtr
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hwComm :
      UInt256.ofNat 32 + Compression.pairWPtr j =
        Compression.pairWPtr j + UInt256.ofNat 32 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hkComm :
      UInt256.ofNat 4 + Compression.pairKPtr j =
        Compression.pairKPtr j + UInt256.ofNat 4 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hreadWPtr :
      MachineState.readWord s.memory
          (UInt256.ofNat 32 + Compression.pairWPtr j).toNat =
        Compression.wValue s (j + 1) := by
    rw [hwComm, hwNext, hwPtrNextNat]
    rfl
  have hmaskKPtr :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory
            (UInt256.ofNat 4 + Compression.pairKPtr j).toNat) =
        Compression.kValue s (j + 1) := by
    rw [hkComm, hkNext, hkPtrNextNat]
    change UInt256.ofNat 0xffffffff &&&
      MachineState.readWord s.memory ((j + 1) * 4 + 4) = _
    rw [hand]
    simpa [Challenge.EvmProof.Word.mask32] using hmaskK
  have hWAddr :
      (UInt256.ofNat 32 + Compression.pairWPtr j).toNat =
        ((UInt256.ofNat (j + 1)).shiftLeft (UInt256.ofNat 5) +
          UInt256.ofNat 800).toNat := by
    rw [hwComm, hwNext]
    simpa [Accessors.slotOffset] using hwPtrNextNat
  have hmaskKNat :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (MachineState.readWord s.memory ((j + 1) * 4 + 4)) =
        Compression.kValue s (j + 1) := by
    change UInt256.ofNat 0xffffffff &&&
      MachineState.readWord s.memory ((j + 1) * 4 + 4) = _
    rw [hand]
    simpa [Challenge.EvmProof.Word.mask32] using hmaskK
  have h32Eq : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [Compression.pairSecondT1SetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.afterPairT20, Compression.callPairT11,
    Compression.secondPairInputsLoaded, Compression.loadedWord,
    BigSigma.t2Returned, BigSigma.t1Entry, Accessors.slotOffset,
    List.exchange, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21,
    hc22, hc23, hc24, hcode, hrun, qrun, qcode, qrun0, qcode0, hdest, hadd,
    h163, h163Eq, h805Eq, hmaskEq, h1Eq, h2Eq, h4Eq, h5Eq, h800Eq,
    qmem, hadd, hpairE, hpairA, hwNext, hkNext, hwPtrNextNat,
    hkPtrNextNat, hwComm, hkComm, hreadWPtr, hmaskKPtr, hmaskKLand,
    hreadW, State.activeWordsAfterUInt256]
  constructor
  · rw [h32Eq, hWAddr]
  constructor
  · rw [hmaskKNat]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  constructor
  · simpa [h32Eq] using hreadWPtr
  constructor
  · exact hmaskKNat
  constructor
  · simpa [h32Eq] using hreadWPtr
  · simpa [Compression.t20] using hpairA

set_option linter.unusedSimpArgs false in
theorem runSecondT2Setup (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairSecondT2SetupPath
      (Compression.afterPairT11 s msgOff returnDest rest j) =
        some (Compression.callPairT21 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
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
  have h824 : (824 : UInt256).toNat = 824 := by decide
  have h114 : (114 : UInt256).toNat = 114 := by decide
  have h114Eq : (114 : UInt256) = UInt256.ofNat 114 := by decide
  have h825Eq : (825 : UInt256) = UInt256.ofNat 825 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have qrun :
      (Compression.secondPairInputsLoaded s msgOff returnDest rest j).halt =
        .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (Compression.secondPairInputsLoaded s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have qrun1 :
      (Compression.afterPairT11 s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode1 :
      (Compression.afterPairT11 s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  simp [Compression.pairSecondT2SetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.afterPairT11, Compression.callPairT21,
    Compression.t11, BigSigma.t1Returned, BigSigma.t2Entry,
    List.exchange, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21,
    hcode, hrun, qrun, qcode, h824, h114, h114Eq, h825Eq, hmaskEq,
    hdest]

set_option linter.unusedSimpArgs false in
theorem runCommit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j + 2 < 65)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock Compression.pairCommitPath
      (Compression.afterPairT21 s msgOff returnDest rest j) =
        some (Compression.afterPair s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
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
  have hdest : Decode.isValidJumpDest submissionBytecode 637 = true := by decide
  have hadd : UInt256.ofNat 1 + UInt256.ofNat (j + 1) =
      UInt256.ofNat (j + 2) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    simpa [Nat.add_assoc] using
      (Challenge.EvmProof.Word.ofNat_add_ofNat (a := j + 1) (b := 1) (by omega))
  have hand (a b : UInt256) : a &&& b = b &&& a := by
    apply Challenge.EvmProof.Word.word_ext
    change (a.val &&& b.val).val = (b.val &&& a.val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  have land_eq (a b : UInt256) : UInt256.land a b = a &&& b := rfl
  have hpairA :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (Compression.t11 s j + Compression.t21 s j) =
        Compression.pairA2 s j := by
    unfold Compression.pairA2 Challenge.EvmProof.Word.mask32
    rw [land_eq, hand (UInt256.ofNat 0xffffffff),
      Challenge.EvmProof.Word.word_add_comm]
  have hpairE :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (Compression.t11 s j + Compression.hValue s 2) =
        Compression.pairE2 s j := by
    unfold Compression.pairE2 Challenge.EvmProof.Word.mask32
    rw [land_eq, hand (UInt256.ofNat 0xffffffff),
      Challenge.EvmProof.Word.word_add_comm]
  have hpairARaw :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (Challenge.EvmProof.Word.mask32
              (((Word.evmBigSigma1 (Compression.pairE1 s j) +
                Word.evmCh (Compression.pairE1 s j) (Compression.hValue s 4)
                  (Compression.hValue s 5)) +
                (Compression.hValue s 6 + Compression.kValue s (j + 1))) +
                Compression.wValue s (j + 1)) +
            Challenge.EvmProof.Word.mask32
              (Word.evmBigSigma0 (Compression.pairA1 s j) +
                Word.evmMaj (Compression.pairA1 s j) (Compression.hValue s 0)
                  (Compression.hValue s 1))) =
        Compression.pairA2 s j := by
    change UInt256.land (UInt256.ofNat 0xffffffff)
      (Compression.t11 s j + Compression.t21 s j) = _
    exact hpairA
  have hpairERaw :
      UInt256.land (UInt256.ofNat 0xffffffff)
          (Challenge.EvmProof.Word.mask32
              (((Word.evmBigSigma1 (Compression.pairE1 s j) +
                Word.evmCh (Compression.pairE1 s j) (Compression.hValue s 4)
                  (Compression.hValue s 5)) +
                (Compression.hValue s 6 + Compression.kValue s (j + 1))) +
                Compression.wValue s (j + 1)) +
            Compression.hValue s 2) =
        Compression.pairE2 s j := by
    change UInt256.land (UInt256.ofNat 0xffffffff)
      (Compression.t11 s j + Compression.hValue s 2) = _
    exact hpairE
  have h1Eq : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h288 : (288 : UInt256).toNat = 288 := by decide
  have h320 : (320 : UInt256).toNat = 320 := by decide
  have h352 : (352 : UInt256).toNat = 352 := by decide
  have h384 : (384 : UInt256).toNat = 384 := by decide
  have h416 : (416 : UInt256).toNat = 416 := by decide
  have h448 : (448 : UInt256).toNat = 448 := by decide
  have h480 : (480 : UInt256).toNat = 480 := by decide
  have h512 : (512 : UInt256).toNat = 512 := by decide
  have h637 : (637 : UInt256).toNat = 637 := by decide
  have h637Eq : (637 : UInt256) = UInt256.ofNat 637 := by decide
  have hmaskEq : (4294967295 : UInt256) = UInt256.ofNat 4294967295 := by decide
  have hwInc :
      UInt256.ofNat 64 + Compression.pairWPtr j =
        Compression.pairWPtr (j + 2) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    unfold Compression.pairWPtr
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega
  have hkInc :
      UInt256.ofNat 8 + Compression.pairKPtr j =
        Compression.pairKPtr (j + 2) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    unfold Compression.pairKPtr
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega
  have h64Eq : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h8Eq : (8 : UInt256) = UInt256.ofNat 8 := by decide
  have qrun :
      (Compression.secondPairInputsLoaded s msgOff returnDest rest j).halt =
        .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (Compression.secondPairInputsLoaded s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have qrun1 :
      (Compression.afterPairT11 s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode1 :
      (Compression.afterPairT11 s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  simp [Compression.pairCommitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.afterPairT21, Compression.afterPair, Compression.storedWord,
    Compression.t21, Compression.t11, BigSigma.t2Returned,
    BigSigma.t1Returned, List.exchange,
    hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13,
    hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21,
    hcode, hrun, qrun, qcode, qrun1, qcode1, hdest, hadd, hpairA, hpairE,
    hpairARaw, hpairERaw, h1Eq, h288, h320, h352, h384, h416, h448,
    h480, h512, h637, h637Eq, hmaskEq, hwInc, hkInc,
    State.activeWordsAfterUInt256]
  exact ⟨by rw [h64Eq]; exact hwInc, by rw [h8Eq]; exact hkInc⟩

end Challenge.Sha256.Submission.Proofs.Bytecode.PairSegmentTest
