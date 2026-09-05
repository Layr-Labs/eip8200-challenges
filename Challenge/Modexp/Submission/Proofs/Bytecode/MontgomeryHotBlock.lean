import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHotValue

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHotBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

def hotEntry (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) : State :=
  MontgomeryWrapperBlock.wrapperEntryAt 2254 s 2048 bPtr 3072 0 n ret saved

def hotAt (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (pc : Nat) : State :=
  MontgomeryWrapperBlock.wrapperEntryAt pc s 2048 bPtr 3072 0 n ret saved

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def zeroGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1621 .JUMPDEST,
   opAt 1622 (.Dup ⟨4, by decide⟩),
   opAt 1623 .ISZERO,
   pushAt 1624 2 2293,
   opAt 1625 .JUMPI]

def largeGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1626 1 32,
   opAt 1627 (.Dup ⟨5, by decide⟩),
   opAt 1628 .GT,
   pushAt 1629 2 2293,
   opAt 1630 .JUMPI]

def parityGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1631 0 0,
   opAt 1632 .MLOAD,
   pushAt 1633 1 1,
   opAt 1634 .AND,
   opAt 1635 .ISZERO,
   pushAt 1636 2 2293,
   opAt 1637 .JUMPI]

def coreCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1638 (.Swap ⟨0, by decide⟩),
   pushAt 1639 2 11264,
   opAt 1640 .MLOAD,
   opAt 1641 (.Swap ⟨4, by decide⟩),
   opAt 1642 (.Swap ⟨3, by decide⟩),
   opAt 1643 (.Swap ⟨2, by decide⟩),
   opAt 1644 (.Swap ⟨1, by decide⟩),
   opAt 1645 (.Swap ⟨0, by decide⟩),
   pushAt 1646 2 1625,
   opAt 1647 .JUMP]

def fallbackPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1648 .JUMPDEST, pushAt 1649 2 2019, opAt 1650 .JUMP]

@[simp] private theorem hotPCs (i : Nat) (hi : 1621 ≤ i) (hii : i ≤ 1650) :
    Artifact.submissionArtifact.instructionPC i =
      [2254,2255,2256,2257,2260,2261,2263,2264,2265,2268,
       2269,2270,2271,2273,2274,2275,2278,2279,2280,2283,
       2284,2285,2286,2287,2288,2289,2292,2293,2294,2297][i - 1621]! := by
  interval_cases i <;> decide

@[simp] private theorem fallbackDest :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2293 = true :=
  Artifact.isValidJumpDest_index 1648 (by rfl)

@[simp] private theorem normalDest :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2019 = true :=
  Artifact.isValidJumpDest_index 1476 (by rfl)

@[simp] private theorem coreDest :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1625 = true :=
  Artifact.isValidJumpDest_index 1227 (by rfl)

private theorem lowBit (w : UInt256) :
    (UInt256.land (UInt256.ofNat 1) w).toNat = w.toNat % 2 := by
  rw [Word.word_toNat_land, Word.word_toNat_ofNat]
  change 1 &&& w.toNat = w.toNat % 2
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

set_option linter.unusedSimpArgs false

theorem run_zeroPass (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hn : 1 ≤ n) (hbound : n < 2 ^ 256) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath (hotEntry s bPtr n ret saved) =
      some (hotAt s bPtr n ret saved 2261) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero (UInt256.ofNat n)) := by
    simp only [UInt256.isZero, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound,
      if_neg (show n ≠ 0 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [zeroGuardPath, hotEntry, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_zeroFallback (s : State) (bPtr ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath (hotEntry s bPtr 0 ret saved) =
      some (hotAt s bPtr 0 ret saved 2293) := by
  have hc : UInt256.isTrue (UInt256.isZero (UInt256.ofNat 0)) := by decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [zeroGuardPath, hotEntry, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_largePass (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hN : n ≤ 32) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath (hotAt s bPtr n ret saved 2261) =
      some (hotAt s bPtr n ret saved 2269) := by
  have hc : ¬ UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (show n < 2 ^ 256 by omega),
      Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide),
      if_neg (show ¬n > 32 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_largeFallback (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hlarge : 32 < n) (hbound : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath (hotAt s bPtr n ret saved 2261) =
      some (hotAt s bPtr n ret saved 2293) := by
  have hc : UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide), if_pos hlarge]
    decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_parityOdd (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath (hotAt s bPtr n ret saved 2269) =
      some (hotAt (MontgomeryWrapperBlock.loadLowLeaf s 0) bPtr n ret saved 2279) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, hodd]
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hzeroNat,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_parityEven (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (heven : (MachineState.readWord s.memory 0).toNat % 2 = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath (hotAt s bPtr n ret saved 2269) =
      some (hotAt (MontgomeryWrapperBlock.loadLowLeaf s 0) bPtr n ret saved 2293) := by
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, heven]
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hzeroNat, hcode,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256]

theorem run_coreCall (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock coreCallPath (hotAt s bPtr n ret saved 2279) =
      some (MontgomerySetupBlock.coreEntry
        (MontgomeryWrapperBlock.loadLowLeaf s 11264) bPtr 2048 3072 0 n
        (MachineState.readWord
          (MontgomeryWrapperBlock.loadLowLeaf s 11264).memory 11264) ret saved) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [coreCallPath, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, List.exchange, cap, hrun, hcode,
    MontgomerySetupBlock.coreEntry, MontgomeryWrapperBlock.loadLowLeaf,
    State.activeWordsAfterUInt256]

theorem run_fallback (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fallbackPath (hotAt s bPtr n ret saved 2293) =
      some (MontgomeryWrapperBlock.normalEntry s bPtr n ret saved) := by
  have cap : ∀ k, k ≤ 24 → saved.length + k < 1024 := by omega
  simp [fallbackPath, opAt, pushAt, wfOp, hotAt,
    MontgomeryWrapperBlock.wrapperEntryAt, MontgomeryWrapperBlock.oldFrame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hcode,
    MontgomeryWrapperBlock.normalEntry, MontgomeryWrapperBlock.oldAt]

private theorem returnedState_effects (s t : State)
    (effects : MontgomeryWrapperBlock.Effects) (ret : UInt256)
    (saved : List UInt256) :
    MontgomeryWrapperBlock.returnedState s
      (MontgomeryWrapperBlock.effectsOf
        (MontgomeryWrapperBlock.returnedState t effects ret saved)) ret saved =
      MontgomeryWrapperBlock.returnedState s effects ret saved := rfl

private theorem returnedState_loadLow (s : State)
    (effects : MontgomeryWrapperBlock.Effects) (ptr ret : UInt256)
    (saved : List UInt256) :
    MontgomeryWrapperBlock.returnedState s effects ret saved =
      MontgomeryWrapperBlock.returnedState
        (MontgomeryWrapperBlock.loadLowLeaf s ptr) effects ret saved := by
  cases s
  rfl

private theorem erased_of_frame (s t : State)
    (hframe : { t with memory := s.memory, activeWords := s.activeWords } = s) :
    MontgomeryWrapperBlock.eraseEffects t = MontgomeryWrapperBlock.eraseEffects s := by
  have h := congrArg MontgomeryWrapperBlock.eraseEffects hframe
  exact h

theorem hotReturned_zero (s : State) (bPtr ret : UInt256) (saved : List UInt256) :
    MontgomeryHotValue.hotReturned s bPtr 0 ret saved =
      MontgomeryWrapperBlock.normalReturned s bPtr 0 ret saved := by
  unfold MontgomeryHotValue.hotReturned MontgomeryHotValue.hotEffects
  rw [if_pos rfl]
  exact returnedState_effects s s
    (MontgomeryWrapperBlock.normalEffects s bPtr 0 ret saved) ret saved

theorem hotReturned_large (s : State) (bPtr : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) (hlarge : 32 < n) :
    MontgomeryHotValue.hotReturned s bPtr n ret saved =
      MontgomeryWrapperBlock.normalReturned s bPtr n ret saved := by
  unfold MontgomeryHotValue.hotReturned MontgomeryHotValue.hotEffects
  rw [if_neg (by omega : n ≠ 0), if_pos hlarge]
  exact returnedState_effects s s
    (MontgomeryWrapperBlock.normalEffects s bPtr n ret saved) ret saved

theorem hotReturned_even (s : State) (bPtr : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (heven : (MachineState.readWord s.memory 0).toNat % 2 = 0) :
    MontgomeryHotValue.hotReturned s bPtr n ret saved =
      MontgomeryWrapperBlock.normalReturned
        (MontgomeryWrapperBlock.loadLowLeaf s 0) bPtr n ret saved := by
  unfold MontgomeryHotValue.hotReturned MontgomeryHotValue.hotEffects
  rw [if_neg (by omega : n ≠ 0), if_neg (by omega : ¬32 < n), if_pos heven]
  change MontgomeryWrapperBlock.returnedState s
    (MontgomeryWrapperBlock.effectsOf
      (MontgomeryWrapperBlock.returnedState (MontgomeryWrapperBlock.loadLowLeaf s 0)
        (MontgomeryWrapperBlock.normalEffects
          (MontgomeryWrapperBlock.loadLowLeaf s 0) bPtr n ret saved) ret saved)) ret saved = _
  rw [returnedState_effects]
  exact returnedState_loadLow s
    (MontgomeryWrapperBlock.normalEffects
      (MontgomeryWrapperBlock.loadLowLeaf s 0) bPtr n ret saved) 0 ret saved

theorem hotReturned_core (s : State) (bPtr : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1) :
    let cached := MontgomeryWrapperBlock.loadLowLeaf
      (MontgomeryWrapperBlock.loadLowLeaf s 0) 11264
    { MontgomeryWrapperValue.coreLeaf cached bPtr.toNat 2048 3072 n
        (MachineState.readWord cached.memory 11264) with pc := ret, stack := saved } =
      MontgomeryHotValue.hotReturned s bPtr n ret saved := by
  let cached := MontgomeryWrapperBlock.loadLowLeaf
    (MontgomeryWrapperBlock.loadLowLeaf s 0) 11264
  let core := MontgomeryWrapperValue.coreLeaf cached bPtr.toNat 2048 3072 n
    (MachineState.readWord cached.memory 11264)
  have cachedErased :
      MontgomeryWrapperBlock.eraseEffects cached = MontgomeryWrapperBlock.eraseEffects s := by
    cases s
    rfl
  have coreErased : MontgomeryWrapperBlock.eraseEffects core =
      MontgomeryWrapperBlock.eraseEffects s :=
    (erased_of_frame cached core
      (MontgomeryWrapperValue.coreLeaf_frame cached bPtr.toNat 2048 3072 n
        (MachineState.readWord cached.memory 11264))).trans cachedErased
  have hreturn := MontgomeryWrapperBlock.returnedState_of_erased s core ret saved coreErased.symm
  simpa only [MontgomeryHotValue.hotReturned, MontgomeryHotValue.hotEffects,
    if_neg (by omega : n ≠ 0), if_neg (by omega : ¬32 < n), hodd,
    if_neg (by decide : ¬(1 : Nat) = 0)] using hreturn.symm


private def gasSteps_fallbackNormal (s : State) (bPtr : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) (hcap : saved.length < 980)
    (hcount : n < 2 ^ 256) (hbPtr : bPtr.toNat ≤ 2048)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true) :
    GasSteps (hotAt s bPtr n ret saved 2293)
      (MontgomeryWrapperBlock.normalReturned s bPtr n ret saved) := by
  have jump := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka fallbackPath
    (s := hotAt s bPtr n ret saved 2293) hcode hfork (run_fallback s bPtr n ret saved hcap hcode hrun) hrun hnp
  exact jump.trans (MontgomeryWrapperBlock.gasSteps_normal s bPtr n ret saved
    hcap hcount hbPtr hcode hfork hrun hnp hret)

/-- The exact hot block for every word-sized count, with all fallbacks and touches. -/
def gasSteps_hot (s : State) (bPtr : UInt256) (n : Nat) (ret : UInt256)
    (saved : List UInt256) (hcap : saved.length < 980) (hcount : n < 2 ^ 256)
    (hbPtr : bPtr.toNat ≤ 2048)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true) :
    GasSteps (hotEntry s bPtr n ret saved)
      (MontgomeryHotValue.hotReturned s bPtr n ret saved) := by
  by_cases hzero : n = 0
  · subst n
    have guard := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka zeroGuardPath
      (s := hotEntry s bPtr 0 ret saved) hcode hfork (run_zeroFallback s bPtr ret saved hcap hcode hrun) hrun hnp
    rw [hotReturned_zero]
    exact guard.trans (gasSteps_fallbackNormal s bPtr 0 ret saved
      hcap hcount hbPtr hcode hfork hrun hnp hret)
  · have hn : 1 ≤ n := by omega
    have zeroPass := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka zeroGuardPath
      (s := hotEntry s bPtr n ret saved) hcode hfork (run_zeroPass s bPtr n ret saved hcap hn hcount hrun) hrun hnp
    by_cases hlarge : 32 < n
    · have guard := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka largeGuardPath
        (s := hotAt s bPtr n ret saved 2261) hcode hfork (run_largeFallback s bPtr n ret saved hcap hlarge hcount hcode hrun)
        hrun hnp
      rw [hotReturned_large s bPtr n ret saved hlarge]
      exact zeroPass.trans (guard.trans (gasSteps_fallbackNormal s bPtr n ret saved
        hcap hcount hbPtr hcode hfork hrun hnp hret))
    · have hN : n ≤ 32 := by omega
      have largePass := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka largeGuardPath
        (s := hotAt s bPtr n ret saved 2261) hcode hfork (run_largePass s bPtr n ret saved hcap hN hrun) hrun hnp
      by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
      · have parity := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka parityGuardPath
          (s := hotAt s bPtr n ret saved 2269) hcode hfork (run_parityEven s bPtr n ret saved hcap heven hcode hrun) hrun hnp
        rw [hotReturned_even s bPtr n ret saved hn hN heven]
        exact zeroPass.trans (largePass.trans (parity.trans
          (gasSteps_fallbackNormal (MontgomeryWrapperBlock.loadLowLeaf s 0)
            bPtr n ret saved hcap hcount hbPtr hcode hfork hrun hnp hret)))
      · have hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1 := by omega
        let touched := MontgomeryWrapperBlock.loadLowLeaf s 0
        let cached := MontgomeryWrapperBlock.loadLowLeaf touched 11264
        let np := MachineState.readWord cached.memory 11264
        have parity := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka parityGuardPath
          (s := hotAt s bPtr n ret saved 2269) hcode hfork (run_parityOdd s bPtr n ret saved hcap hodd hrun) hrun hnp
        have call := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka coreCallPath
          (s := hotAt touched bPtr n ret saved 2279) hcode hfork (run_coreCall touched bPtr n ret saved hcap hcode hrun) hrun hnp
        have core : GasSteps
            (MontgomerySetupBlock.coreEntry cached bPtr 2048 3072 0 n np ret saved)
            { MontgomeryWrapperValue.coreLeaf cached bPtr.toNat 2048 3072 n np with
                pc := ret, stack := saved } := by
          simpa only [← Word.word_eq_ofNat_toNat bPtr, Word.literal_eq_ofNat] using
            MontgomeryCoreBridge.gasSteps_coreLeaf cached bPtr.toNat 2048 3072 n np ret saved
              hN (by omega) (by decide) (by omega) hcode hfork hrun hnp hret
        rw [← hotReturned_core s bPtr n ret saved hn hN hodd]
        exact zeroPass.trans (largePass.trans (parity.trans (call.trans core)))

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHotBlock
