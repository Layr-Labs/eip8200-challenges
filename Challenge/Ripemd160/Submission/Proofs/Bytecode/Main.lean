import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Direct execution of the RIPEMD-160 main-body initialization

The compact entry stores the five chaining words consecutively.  After the
first explicit offset, each next offset is the current memory size.  Push and
store instructions use located paths; the four `MSIZE` instructions use the
submission-local gas-accounted EVM rule.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Exact state transformer for one initialization store. -/
def applyInitStore (s : State) (w : Artifact.InitStore) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.instructionPC (w.index + 3))
    stack := []
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded w.value.toNat 32) w.offset.toNat
    activeWords := s.activeWordsAfterUInt256 w.offset.toNat 32 }

private theorem valueFits (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) :
    w.value.toNat < 256 ^ w.valueWidth.val := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem offsetFits (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) :
    w.offset.toNat < 256 ^ w.offsetWidth.val := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem pushAvailable (width : Fin 33) :
    (Operation.Push ⟨width⟩).availableInFork .Osaka = true := by
  change (if width.val = 0 then decide (.Osaka ≥ Fork.Shanghai) else true) = true
  by_cases h : width.val = 0
  · rw [if_pos h]
    decide
  · rw [if_neg h]

@[simp] private theorem pushZeroWord :
    (⟨0⟩ : UInt256) = UInt256.ofNat 0 := rfl

@[simp] private theorem toNatZero : (0 : UInt256).toNat = 0 := rfl

def afterInitValue (s : State) (w : Artifact.InitStore) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.instructionPC (w.index + 1))
    stack := [w.value] }

def afterInitOffset (s : State) (w : Artifact.InitStore) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.instructionPC (w.index + 2))
    stack := [w.offset, w.value] }

def locatedInitValue (w : Artifact.InitStore) (hw : w ∈ Artifact.initStores) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  let hv := Artifact.initStore_valid w hw
  [⟨w.index, .push w.valueWidth w.value, hv.1,
      ⟨valueFits w hw, pushAvailable w.valueWidth⟩⟩]

def locatedInitOffset (w : Artifact.InitStore) (hw : w ∈ Artifact.initStores)
    (hm : w.useMsize = false) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  let hv := Artifact.initStore_valid w hw
  [⟨w.index + 1, .push w.offsetWidth w.offset, by
      change Artifact.submissionInstructions[w.index + 1]? = _
      simpa [hm] using hv.2.2.1,
      ⟨offsetFits w hw, pushAvailable w.offsetWidth⟩⟩]

def locatedInitWrite (w : Artifact.InitStore) (hw : w ∈ Artifact.initStores) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  let hv := Artifact.initStore_valid w hw
  [⟨w.index + 2, .op .MSTORE, hv.2.2.2.2.1,
      wfOp (by decide) trivial rfl⟩]

def initializedState (input : ByteArray) : State :=
  Artifact.initStores.foldl applyInitStore (Execution.mainStart input)

@[simp] theorem initializedState_pc (input : ByteArray) :
    (initializedState input).pc = UInt256.ofNat (Artifact.instructionPC 221) := by
  rfl

@[simp] theorem initializedState_stack (input : ByteArray) :
    (initializedState input).stack = [] := by rfl

@[simp] theorem initializedState_halt (input : ByteArray) :
    (initializedState input).halt = .Running := by rfl

@[simp] theorem initializedState_fork (input : ByteArray) :
    (initializedState input).fork = .Osaka := by rfl

@[simp] theorem initializedState_code (input : ByteArray) :
    (initializedState input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem initializedState_codeAddr (input : ByteArray) :
    (initializedState input).executionEnv.codeAddr = deployAddress := by rfl

theorem run_initValue (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (locatedInitValue w hw) s =
      some (afterInitValue s w) := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { maxSteps := 200000 })
      [locatedInitValue, afterInitValue, hpc, hstack, hrun,
        Artifact.instructionPC,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_initOffset (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) (hm : w.useMsize = false)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 1)))
    (hstack : s.stack = [w.value]) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (locatedInitOffset w hw hm) s =
      some (afterInitOffset s w) := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals simp at hm
  simp (config := { maxSteps := 200000 })
    [locatedInitOffset, afterInitOffset, hpc, hstack, hrun,
      Artifact.instructionPC, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_initWrite (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 2)))
    (hstack : s.stack = [w.offset, w.value]) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (locatedInitWrite w hw) s =
      some (applyInitStore s w) := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { maxSteps := 200000 })
      [locatedInitWrite, applyInitStore, hpc, hstack, hrun,
        Artifact.instructionPC,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem msizeDecoded (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) (hm : w.useMsize = true)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 1)))
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) : s.decodedOp = some .MSIZE := by
  have hv := Artifact.initStore_valid w hw
  have hget : Artifact.submissionInstructions[w.index + 1]? = some (.op .MSIZE) := by
    simpa [hm] using hv.2.2.1
  have hdecode := Artifact.submissionArtifact.decodeAt_op_index
    (w.index + 1) .MSIZE hget (by decide) trivial
  have hpcNat : s.pc.toNat =
      Artifact.submissionArtifact.instructionPC (w.index + 1) := by
    rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Artifact.submissionArtifact.instructionPC_le_code_size (w.index + 1))
      (by change submissionBytecode.size < 2 ^ 256
          rw [referenceBytecode_size]
          decide))
  exact Artifact.submissionArtifact.state_decodedOp_of s (w.index + 1)
    hcode hpcNat .MSIZE none hdecode (by rw [hfork]; decide)

def gasSteps_initStore (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hmsize : w.useMsize = true →
      UInt256.ofNat (32 * s.activeWords.toNat) = w.offset)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s (applyInitStore s w) := by
  have gvalue := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (locatedInitValue w hw)
    (by simpa [Artifact.submissionArtifact] using hcode) hfork
    (run_initValue s w hw hpc hstack hrun) hrun hnp
  by_cases hm : w.useMsize = true
  · let sv := afterInitValue s w
    let so := afterInitOffset s w
    have hop : sv.decodedOp = some .MSIZE := msizeDecoded sv w hw hm
      (by rfl) (by simpa [sv, afterInitValue] using hcode)
      (by simpa [sv, afterInitValue] using hfork)
    have gmraw := Msize.step hop (by simp [sv, afterInitValue])
      (by simpa [sv, afterInitValue] using hrun)
      (by simpa [sv, afterInitValue] using hnp)
    have gm : Challenge.EvmProof.GasSteps sv so :=
      Challenge.EvmProof.GasSteps.cast gmraw rfl (by
        have hv := Artifact.initStore_valid w hw
        have hnextpc : Artifact.instructionPC (w.index + 2) =
            Artifact.instructionPC (w.index + 1) + 1 := by
          simpa [hm] using hv.2.2.2.1
        simp [sv, so, afterInitValue, afterInitOffset, hmsize hm,
          Challenge.EvmProof.Word.succ_ofNat_mod, hnextpc])
    have gw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka (locatedInitWrite w hw)
      (by simpa [so, afterInitOffset, Artifact.submissionArtifact] using hcode)
      (by simpa [so, afterInitOffset] using hfork)
      (run_initWrite so w hw (by rfl) (by rfl)
        (by simpa [so, afterInitOffset] using hrun))
      (by simpa [so, afterInitOffset] using hrun)
      (by simpa [so, afterInitOffset] using hnp)
    exact gvalue.trans (gm.trans gw)
  · have hmfalse : w.useMsize = false := Bool.eq_false_of_not_eq_true hm
    let sv := afterInitValue s w
    let so := afterInitOffset s w
    have go := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka (locatedInitOffset w hw hmfalse)
      (by simpa [sv, afterInitValue, Artifact.submissionArtifact] using hcode)
      (by simpa [sv, afterInitValue] using hfork)
      (run_initOffset sv w hw hmfalse (by rfl) (by rfl)
        (by simpa [sv, afterInitValue] using hrun))
      (by simpa [sv, afterInitValue] using hrun)
      (by simpa [sv, afterInitValue] using hnp)
    have gw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka (locatedInitWrite w hw)
      (by simpa [so, afterInitOffset, Artifact.submissionArtifact] using hcode)
      (by simpa [so, afterInitOffset] using hfork)
      (run_initWrite so w hw (by rfl) (by rfl)
        (by simpa [so, afterInitOffset] using hrun))
      (by simpa [so, afterInitOffset] using hrun)
      (by simpa [so, afterInitOffset] using hnp)
    exact gvalue.trans (go.trans gw)

def InitChain : List Artifact.InitStore → Prop
  | [] | [_] => True
  | a :: b :: rest => b.index = a.index + 3 ∧ InitChain (b :: rest)

theorem nextActive_after (s : State) (w next : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) (hn : next ∈ Artifact.initStores)
    (hnext : next.index = w.index + 3)
    (hactive : s.activeWords.toNat ≤ w.offset.toNat / 32) :
    (applyInitStore s w).activeWords.toNat = next.offset.toNat / 32 := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw hn
  rcases hw with rfl | rfl | rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [applyInitStore, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals
    simp only [Nat.max_def]
    split <;> omega

theorem nextMsize_after (s : State) (w next : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) (hn : next ∈ Artifact.initStores)
    (hnext : next.index = w.index + 3)
    (hactive : s.activeWords.toNat ≤ w.offset.toNat / 32) :
    next.useMsize = true →
      UInt256.ofNat (32 * (applyInitStore s w).activeWords.toNat) = next.offset := by
  intro _
  rw [nextActive_after s w next hw hn hnext hactive]
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

def gasSteps_initStores (s : State) :
    (ws : List Artifact.InitStore) →
    (∀ w, w ∈ ws → w ∈ Artifact.initStores) →
    InitChain ws →
    (∀ w, ws.head? = some w →
      s.pc = UInt256.ofNat (Artifact.instructionPC w.index)) →
    s.stack = [] →
    (∀ w, ws.head? = some w → s.activeWords.toNat ≤ w.offset.toNat / 32) →
    (∀ w, ws.head? = some w → w.useMsize = true →
      UInt256.ofNat (32 * s.activeWords.toNat) = w.offset) →
    s.executionEnv.code = submissionBytecode →
    s.fork = .Osaka →
    s.halt = .Running →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false →
    Challenge.EvmProof.GasSteps s (ws.foldl applyInitStore s)
  | [], _, _, _, _, _, _, _, _, _, _ => Challenge.EvmProof.GasSteps.refl s
  | [w], hmem, _, hpc, hstack, _, hmsize, hcode, hfork, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      have gone := gasSteps_initStore s w hw hpcw hstack hcode hfork hrun
        (hmsize w (by simp)) hnp
      exact Challenge.EvmProof.GasSteps.cast gone rfl (by simp)
  | w :: next :: rest, hmem, hchain, hpc, hstack, hactive, hmsize, hcode, hfork, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      have gone := gasSteps_initStore s w hw hpcw hstack hcode hfork hrun
        (hmsize w (by simp)) hnp
      have hnext : next.index = w.index + 3 := hchain.1
      have htail : InitChain (next :: rest) := hchain.2
      have grest := gasSteps_initStores (applyInitStore s w) (next :: rest)
        (fun x hx => hmem x (List.mem_cons_of_mem w hx)) htail
        (fun x hx => by
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          simp [applyInitStore, hnext])
        (by simp [applyInitStore])
        (fun x hx => by
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          exact (nextActive_after s w next hw (hmem next (by simp))
            hnext (hactive w (by simp))).le)
        (fun x hx => by
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          exact nextMsize_after s w next hw
            (hmem next (by simp)) hnext (hactive w (by simp)))
        (by simpa [applyInitStore] using hcode)
        (by simpa [applyInitStore] using hfork)
        (by simpa [applyInitStore] using hrun)
        (by simpa [applyInitStore] using hnp)
      exact Challenge.EvmProof.GasSteps.cast (gone.trans grest) rfl
        (by simp [List.foldl])

def gasSteps_bodyInitialization (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Execution.mainStart input)
      (initializedState input) := by
  have body := gasSteps_initStores (Execution.mainStart input)
    Artifact.initStores (fun _ h => h)
    (by norm_num [InitChain, Artifact.initStores])
    (by
      intro w hw
      simp only [Artifact.initStores, List.head?_cons, Option.some.injEq] at hw
      subst w
      rfl)
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by
      intro w hw
      simp only [Artifact.initStores, List.head?_cons, Option.some.injEq] at hw
      subst w
      simp [Execution.mainStart, Execution.atPC, initialState])
    (by
      intro w hw
      simp only [Artifact.initStores, List.head?_cons, Option.some.injEq] at hw
      subst w
      simp)
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState,
      deployAddress_not_precompile])
  exact Challenge.EvmProof.GasSteps.cast body rfl
    (by simp [initializedState])

def gasSteps_initialize (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x170)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (initializedState input) :=
  (Execution.gasSteps_entry input entryPrefix).trans (gasSteps_bodyInitialization input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
