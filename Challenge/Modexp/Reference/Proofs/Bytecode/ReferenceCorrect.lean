import Challenge.Modexp.ProofSupport.Bytecode
import Challenge.Modexp.Reference.Proofs.Bytecode.BigZeroCorrect
import Challenge.Modexp.Reference.Proofs.Bytecode.WordGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
/-! # End-to-end correctness and exact gas for the reference MODEXP bytecode -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem mulWordProgress_callStack (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    (BigMul.mulWordProgress current word a b out modulus count i returnDest rest
      j).callStack = current.callStack := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [BigMul.mulWordProgress, BigMul.mulWordAfterDouble,
        BigMul.mulWordAfterAdd, BigMul.mulInnerState, BigHelpers.addReturned, ih]

@[simp] theorem mulOuterProgress_callStack (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigMul.mulOuterProgress current a b out modulus count returnDest rest
      i).callStack = current.callStack := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [BigMul.mulOuterProgress, BigMul.mulLoadedState, ih]

@[simp] theorem mulResult_callStack (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (BigExponent.mulResult s a b out modulus count returnDest rest).callStack =
      s.callStack := by
  simp [BigExponent.mulResult, BigMul.mulReturned, BigMul.mulAfterCopy,
    BigMul.mulAfterClear]

@[simp] theorem squareReturned_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.squareReturned s accumulatorWord count b e m baseOff expOff
      i j offset byte rest).callStack = s.callStack := by
  simp [BigExponent.squareReturned, BigExponent.innerBody,
    BigExponent.innerLoop]

@[simp] theorem copiedSquare_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.copiedSquare s accumulatorWord count b e m baseOff expOff
      i j offset byte rest).callStack = s.callStack := by
  simp [BigExponent.copiedSquare, BigHelpers.copyReturned]

@[simp] theorem productReturned_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.productReturned s accumulatorWord count b e m baseOff expOff
      i j offset byte rest).callStack = s.callStack := by
  simp [BigExponent.productReturned]

@[simp] theorem selectProgress_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j k : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.selectProgress s accumulatorWord count b e m baseOff expOff
      i j offset byte rest k).callStack = s.callStack := by
  simp [BigExponent.selectProgress]

@[simp] theorem exponentBitProgress_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.exponentBitProgress s accumulatorWord count b e m baseOff
      expOff i offset byte rest j).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih => simp [BigExponent.exponentBitProgress, ih]

@[simp] theorem exponentByteProgress_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (rest : List UInt256) :
    (BigExponent.exponentByteProgress s accumulatorWord count b e m baseOff
      expOff rest i).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [BigExponent.exponentByteProgress, ih]

@[simp] theorem baseBitProgress_callStack (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (BigBase.bitProgress count byte j s).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [BigBase.bitProgress, BigHelpers.addReturned, ih]

@[simp] theorem baseProgress_callStack (count baseOff i : Nat) (s : State) :
    (BigBase.baseProgress count baseOff i s).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [BigBase.baseProgress, ih]

@[simp] theorem setupState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.setupState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  rfl

@[simp] theorem serializeProgress_callStack (s : State) (m k : Nat) :
    (BigSerialize.serializeProgress s m k).callStack = s.callStack := by
  rfl

@[simp] theorem baseState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.baseState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.baseState, BigBase.baseLoopEntry,
    BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero]

@[simp] theorem exponentState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.exponentState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.exponentState, BigBaseLoop.initialAccumulator,
    BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
    BigHelpers.addReturned]

@[simp] theorem exponentProgressState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.exponentProgressState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.exponentProgressState]

@[simp] theorem completedState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.completedState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.completedState, BigSerialize.bigReturned,
    BigSerialize.serializeProgress]

@[simp] theorem zeroFinalState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigZeroCorrect.zeroFinalState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigZeroCorrect.zeroFinalState, BigModulus.scanZeroFinal,
    setupState_callStack]

@[simp] theorem completedState_isDone (input : ByteArray)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.completedState (Main.headerState input) b e m baseOff expOff
      modOff returnDest rest).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning,
    BigComplete.completedState, BigSerialize.bigReturned, Main.headerState,
    initialState]

@[simp] theorem zeroFinalState_isDone (input : ByteArray)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigZeroCorrect.zeroFinalState (Main.headerState input) b e m baseOff
      expOff modOff returnDest rest).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning,
    BigZeroCorrect.zeroFinalState, BigModulus.scanZeroFinal, Main.headerState,
    initialState]

def bigRest (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (Word.modulusOffset input), UInt256.ofNat (Word.expOffset input),
    UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
    UInt256.ofNat (baseSize input)]

def bigReturnDest : UInt256 := UInt256.ofNat 1283

def bigCompletedState (input : ByteArray) : State :=
  BigComplete.completedState (Main.headerState input) (baseSize input)
    (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
    (Word.modulusOffset input) bigReturnDest (bigRest input)

def bigZeroFinalState (input : ByteArray) : State :=
  BigZeroCorrect.zeroFinalState (Main.headerState input) (baseSize input)
    (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
    (Word.modulusOffset input) bigReturnDest (bigRest input)

def gasSteps_bigNonzeroTotal (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) (hmodulusPos : 0 < Word.modulusValue input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (bigCompletedState input) := by
  have hb := hvalid.2.1
  have he := hvalid.2.2.1
  have hm := hvalid.2.2.2
  have hmodOff : Word.modulusOffset input < 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hinputFit : Word.modulusOffset input + modulusSize input ≤ 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hor : BigComplete.modulusOr (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) bigReturnDest (bigRest input) ≠ 0 := by
    intro hz
    have := (BigZeroCorrect.modulusOr_eq_zero_iff input bigReturnDest
      (bigRest input) hvalid).1 hz
    omega
  have hcore := BigComplete.gasSteps_nonzero (Main.headerState input)
    (baseSize input) (exponentSize input) (modulusSize input) 96
    (Word.expOffset input) (Word.modulusOffset input) bigReturnDest
    (bigRest input) hm hmodOff hinputFit (by omega) (by omega) (by omega)
    (by simp [Word.expOffset]; omega) (by simp [bigRest]) hor
    (by rfl) (by rfl) (by rfl)
    deployAddress_not_precompile
  have hcore' : Challenge.EvmProof.GasSteps (BigDispatch.bigEntryState input)
      (bigCompletedState input) := by
    simpa [BigDispatch.bigEntryState, BigSetup.setupEntry, bigCompletedState,
      bigRest, bigReturnDest, Word.expOffset, Word.modulusOffset,
      Nat.add_assoc] using hcore
  exact ((Main.gasSteps_header input hvalid).trans
    (BigDispatch.gasSteps_bigEntry input hvalid (by omega) hbig)).trans hcore'

def gasSteps_bigZeroTotal (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) (hmodulus : Word.modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (bigZeroFinalState input) := by
  have hb := hvalid.2.1
  have he := hvalid.2.2.1
  have hm := hvalid.2.2.2
  have hmodOff : Word.modulusOffset input < 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hinputFit : Word.modulusOffset input + modulusSize input ≤ 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hor : BigComplete.modulusOr (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) bigReturnDest (bigRest input) = 0 :=
    (BigZeroCorrect.modulusOr_eq_zero_iff input bigReturnDest (bigRest input)
      hvalid).2 hmodulus
  have hcore := BigZeroCorrect.gasSteps_zero (Main.headerState input)
    (baseSize input) (exponentSize input) (modulusSize input) 96
    (Word.expOffset input) (Word.modulusOffset input) bigReturnDest
    (bigRest input) hm hmodOff hinputFit (by simp [bigRest]) hor
    (by rfl) (by rfl) (by rfl) deployAddress_not_precompile
  have hcore' : Challenge.EvmProof.GasSteps (BigDispatch.bigEntryState input)
      (bigZeroFinalState input) := by
    simpa [BigDispatch.bigEntryState, BigSetup.setupEntry, bigZeroFinalState,
      bigRest, bigReturnDest, Word.expOffset, Word.modulusOffset,
      Nat.add_assoc] using hcore
  exact ((Main.gasSteps_header input hvalid).trans
    (BigDispatch.gasSteps_bigEntry input hvalid (by omega) hbig)).trans hcore'

def finalState (input : ByteArray) : State :=
  if modulusSize input = 0 then Dispatch.zeroSizeFinalState input
  else if modulusSize input ≤ 32 then
    if Word.modulusValue input = 0 then Word.zeroModulusFinalState input
    else WordExit.wordFinalState input (WordCorrect.wordResult input)
      (WordCorrect.wordBase input)
  else if Word.modulusValue input = 0 then bigZeroFinalState input
  else bigCompletedState input

def gasSteps_reference (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (finalState input) := by
  by_cases hzeroSize : modulusSize input = 0
  · simpa [finalState, hzeroSize] using
      Dispatch.gasSteps_zeroSize_total input hvalid hzeroSize
  have hpositive : 0 < modulusSize input := by omega
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simpa [finalState, hzeroSize, hword, hzeroModulus] using
        Word.gasSteps_zeroModulus_total input hvalid hpositive hword
          hzeroModulus
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      simpa [finalState, hzeroSize, hword, hzeroModulus] using
        WordCorrect.gasSteps_wordNonzeroTotal input hvalid hpositive hword
          hmodulusPos
  · have hbig : 32 < modulusSize input := by omega
    by_cases hzeroModulus : Word.modulusValue input = 0
    · simpa [finalState, hzeroSize, hword, hzeroModulus] using
        gasSteps_bigZeroTotal input hvalid hbig hzeroModulus
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      simpa [finalState, hzeroSize, hword, hzeroModulus] using
        gasSteps_bigNonzeroTotal input hvalid hbig hmodulusPos

@[simp] theorem finalState_isDone (input : ByteArray) :
    (finalState input).isDone = true := by
  by_cases hzeroSize : modulusSize input = 0
  · simp [finalState, hzeroSize]
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simp [finalState, hzeroSize, hword, hzeroModulus]
    · simp [finalState, hzeroSize, hword, hzeroModulus]
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simp [finalState, hzeroSize, hword, hzeroModulus, bigZeroFinalState]
    · simp [finalState, hzeroSize, hword, hzeroModulus, bigCompletedState]

theorem finalState_result (input : ByteArray) (hvalid : ValidInput input) :
    (finalState input).toResult = .returned (spec input) := by
  by_cases hzeroSize : modulusSize input = 0
  · simpa [finalState, hzeroSize] using
      Dispatch.zeroSizeFinalState_result input hzeroSize
  have hpositive : 0 < modulusSize input := by omega
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simpa [finalState, hzeroSize, hword, hzeroModulus] using
        Word.zeroModulusFinalState_result input hpositive hzeroModulus
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      simpa [finalState, hzeroSize, hword, hzeroModulus] using
        WordCorrect.wordFinalState_result input hvalid hpositive hword
          hmodulusPos
  · have hbig : 32 < modulusSize input := by omega
    by_cases hzeroModulus : Word.modulusValue input = 0
    · simpa [finalState, hzeroSize, hword, hzeroModulus, bigZeroFinalState] using
        BigZeroCorrect.zeroFinalState_result input bigReturnDest (bigRest input)
          hvalid hbig hzeroModulus
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      simpa [finalState, hzeroSize, hword, hzeroModulus, bigCompletedState] using
        BigSerializeCorrect.completedState_result input bigReturnDest
          (bigRest input) hvalid hbig hmodulusPos

@[simp] theorem withGas_initialState_zero (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState referenceBytecode input 0) gas =
      initialState referenceBytecode input gas := by
  rfl

theorem referenceDirectProof :
    Challenge.Modexp.ProofSupport.Bytecode.DirectProof referenceBytecode := by
  let Input := { calldata : ByteArray // ValidInput calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState referenceBytecode input.1 0)
    (final := fun input : Input => finalState input.1)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => gasSteps_reference input.1 input.2)
    (fun input => finalState_isDone input.1)
    (fun input => finalState_result input.1 input.2)
  simpa [Challenge.Modexp.ProofSupport.Bytecode.DirectProof, Input] using h

theorem reference_correct : Correct referenceBytecode :=
  Challenge.Modexp.ProofSupport.Bytecode.correct_of_directProof
    referenceDirectProof

end Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect
