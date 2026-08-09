import Challenge.Sha256.Submission.Proofs.Bytecode.PairCorrectTest

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ResidentLoop

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

private theorem readW_of_memory_eq (base s : State) (j : Nat) (hj : j < 64)
    (hmem : base.memory = s.memory) :
    MachineState.readWord base.memory (Compression.pairWPtr j).toNat =
      Compression.wValue s j := by
  have hwPtrNat : (Compression.pairWPtr j).toNat =
      Accessors.slotOffset 800 (UInt256.ofNat j) := by
    have hshift : (UInt256.ofNat j).shiftLeft (UInt256.ofNat 5) =
        UInt256.ofNat (j * 32) := by
      simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := j) (shift := 5) (by omega) (by decide) (by omega)
    unfold Compression.pairWPtr Accessors.slotOffset
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    repeat' rw [Nat.mod_eq_of_lt (by omega)]
    omega
  unfold Compression.wValue
  rw [hmem, hwPtrNat]

private theorem readK_of_memory_eq (base s : State) (j : Nat) (hj : j < 64)
    (hmem : base.memory = s.memory) :
    UInt256.ofNat 0xffffffff &&&
        MachineState.readWord base.memory (Compression.pairKPtr j).toNat =
      Compression.kValue s j := by
  have hkPtrNat : (Compression.pairKPtr j).toNat = j * 4 + 4 := by
    unfold Compression.pairKPtr
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hshift : (UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) =
      UInt256.ofNat (j * 4) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
      (value := j) (shift := 2) (by omega) (by decide) (by omega)
  have hkoff :
      ((UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) +
        UInt256.ofNat 32).toNat = 32 + j * 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmask : Challenge.EvmProof.Word.mask32
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
  rw [hmem, hkPtrNat, hand]
  simpa [Challenge.EvmProof.Word.mask32] using hmask

def actualBaseState (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => base
  | n + 1 => Compression.residentAfterPair
      (actualBaseState base ghost msgOff returnDest rest n)
      (ResidentBridge.ghostLoopState ghost msgOff returnDest rest n)
      msgOff returnDest rest (2 * n)

def loopState (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n : Nat) : State :=
  Compression.residentAt
    (actualBaseState base ghost msgOff returnDest rest n)
    (ResidentBridge.ghostLoopState ghost msgOff returnDest rest n)
    msgOff returnDest rest (2 * n)

@[simp] theorem residentBase_executionEnv (s : State) :
    (Compression.residentBase s).executionEnv = s.executionEnv := by rfl

@[simp] theorem residentBase_halt (s : State) :
    (Compression.residentBase s).halt = s.halt := by rfl

@[simp] theorem residentBase_callStack (s : State) :
    (Compression.residentBase s).callStack = s.callStack := by rfl

@[simp] theorem residentAt_executionEnv (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAt base ghost msgOff returnDest rest j).executionEnv =
      base.executionEnv := by rfl

@[simp] theorem residentAt_halt (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAt base ghost msgOff returnDest rest j).halt =
      base.halt := by rfl

@[simp] theorem residentAt_callStack (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAt base ghost msgOff returnDest rest j).callStack =
      base.callStack := by rfl

@[simp] theorem residentAfterPair_memory (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAfterPair base ghost msgOff returnDest rest j).memory =
      base.memory := by rfl

@[simp] theorem residentAfterPair_executionEnv (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAfterPair base ghost msgOff returnDest rest j).executionEnv =
      base.executionEnv := by rfl

@[simp] theorem residentAfterPair_halt (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAfterPair base ghost msgOff returnDest rest j).halt =
      base.halt := by rfl

@[simp] theorem residentAfterPair_callStack (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.residentAfterPair base ghost msgOff returnDest rest j).callStack =
      base.callStack := by rfl

@[simp] theorem actualBaseState_memory (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (actualBaseState base ghost msgOff returnDest rest n).memory = base.memory := by
  induction n with
  | zero => rfl
  | succ n ih => simp [actualBaseState, ih]

@[simp] theorem actualBaseState_executionEnv (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (actualBaseState base ghost msgOff returnDest rest n).executionEnv =
      base.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simp [actualBaseState, ih]

@[simp] theorem actualBaseState_halt (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (actualBaseState base ghost msgOff returnDest rest n).halt = base.halt := by
  induction n with
  | zero => rfl
  | succ n ih => simp [actualBaseState, ih]

@[simp] theorem actualBaseState_callStack (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (actualBaseState base ghost msgOff returnDest rest n).callStack =
      base.callStack := by
  induction n with
  | zero => rfl
  | succ n ih => simp [actualBaseState, ih]

@[simp] theorem loopState_executionEnv (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (loopState base ghost msgOff returnDest rest n).executionEnv =
      base.executionEnv := by simp [loopState]

@[simp] theorem loopState_halt (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (loopState base ghost msgOff returnDest rest n).halt = base.halt := by
  simp [loopState]

@[simp] theorem loopState_callStack (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (loopState base ghost msgOff returnDest rest n).callStack =
      base.callStack := by simp [loopState]

private theorem pairWPtr_next (j : Nat) (hj : j + 1 < 65) :
    UInt256.ofNat 32 + Compression.pairWPtr j =
      Compression.pairWPtr (j + 1) := by
  rw [Challenge.EvmProof.Word.word_add_comm]
  unfold Compression.pairWPtr
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

private theorem pairKPtr_next (j : Nat) (hj : j + 1 < 65) :
    UInt256.ofNat 4 + Compression.pairKPtr j =
      Compression.pairKPtr (j + 1) := by
  rw [Challenge.EvmProof.Word.word_add_comm]
  unfold Compression.pairKPtr
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

def gasStepsLoop (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hmem : base.memory = ghost.memory)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loopState base ghost msgOff returnDest rest 0)
      (loopState base ghost msgOff returnDest rest 32) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 32)
  intro n hn
  let qbase := actualBaseState base ghost msgOff returnDest rest n
  let qghost := ResidentBridge.ghostLoopState ghost msgOff returnDest rest n
  let j := 2 * n
  have hj : j + 2 ≤ 64 := by
    dsimp only [j]
    omega
  have hj0 : j < 64 := by omega
  have hj1 : j + 1 < 64 := by omega
  have qmem : qbase.memory = ghost.memory := by
    calc
      qbase.memory = base.memory := by simp [qbase]
      _ = ghost.memory := hmem
  have qcode : qbase.executionEnv.code = submissionBytecode := by
    simpa [qbase] using hcode
  have qfork : qbase.fork = .Osaka := by
    simpa [qbase, State.fork] using hfork
  have qrun : qbase.halt = .Running := by
    simpa [qbase] using hrun
  have qnp : Precompile.isPrecompileWithConfig
      qbase.executionEnv.precompileConfig qbase.executionEnv.fork
      qbase.executionEnv.codeAddr = false := by
    simpa [qbase] using hnp
  have hp0 := PairCorrectTest.pairLoopState_inputs
    ghost msgOff returnDest rest n j hj0
  have hp1 := PairCorrectTest.pairLoopState_inputs
    ghost msgOff returnDest rest n (j + 1) hj1
  have hW0 : MachineState.readWord qbase.memory
        (Compression.pairWPtr j).toNat = Compression.wValue qghost j := by
    exact (readW_of_memory_eq qbase ghost j hj0 qmem).trans hp0.2.symm
  have hK0 : UInt256.ofNat 0xffffffff &&&
        MachineState.readWord qbase.memory (Compression.pairKPtr j).toNat =
      Compression.kValue qghost j := by
    exact (readK_of_memory_eq qbase ghost j hj0 qmem).trans hp0.1.symm
  have hW1 : MachineState.readWord qbase.memory
        (UInt256.ofNat 32 + Compression.pairWPtr j).toNat =
      Compression.wValue qghost (j + 1) := by
    rw [pairWPtr_next j (by omega)]
    exact (readW_of_memory_eq qbase ghost (j + 1) hj1 qmem).trans hp1.2.symm
  have hK1 : UInt256.land (UInt256.ofNat 0xffffffff)
        (MachineState.readWord qbase.memory
          (UInt256.ofNat 4 + Compression.pairKPtr j).toNat) =
      Compression.kValue qghost (j + 1) := by
    rw [pairKPtr_next j (by omega)]
    change UInt256.ofNat 0xffffffff &&&
        MachineState.readWord qbase.memory (Compression.pairKPtr (j + 1)).toNat = _
    exact (readK_of_memory_eq qbase ghost (j + 1) hj1 qmem).trans hp1.1.symm
  have g := ResidentComposition.gasStepsPair qbase qghost msgOff returnDest
    rest j hj hcap qcode qfork qrun qnp hW0 hK0 hW1 hK1
  have hs : Compression.residentAt qbase qghost msgOff returnDest rest j =
      loopState base ghost msgOff returnDest rest n := by rfl
  have ht : Compression.residentAfterPair qbase qghost msgOff returnDest rest j =
      loopState base ghost msgOff returnDest rest (n + 1) := by
    have hnext := ResidentBridge.residentAfterPair_eq_next
      qbase qghost msgOff returnDest rest j
    simpa [loopState, actualBaseState, ResidentBridge.ghostLoopState,
      qbase, qghost, j, Nat.mul_add, Nat.add_assoc] using hnext
  exact Challenge.EvmProof.GasSteps.cast g hs ht

end Challenge.Sha256.Submission.Proofs.Bytecode.ResidentLoop
