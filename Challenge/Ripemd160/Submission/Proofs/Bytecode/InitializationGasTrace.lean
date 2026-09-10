import Challenge.EvmProof.Meter
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionLegacy

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationGasTrace

open Challenge.Ripemd160
open EvmSemantics EvmSemantics.EVM

private theorem entry_start_cost (input : ByteArray) :
    (Execution.gasSteps_start input).cost = 11 := by rfl
private theorem entry_1b_cost (input : ByteArray) :
    (Execution.gasSteps_1b input).cost = 12 := by rfl
private theorem entry_2e_cost (input : ByteArray) :
    (Execution.gasSteps_2e input).cost = 12 := by rfl
private theorem entry_46_cost (input : ByteArray) :
    (Execution.gasSteps_46 input).cost = 12 := by rfl
private theorem entry_5a_cost (input : ByteArray) :
    (Execution.gasSteps_5a input).cost = 12 := by rfl
private theorem entry_73_cost (input : ByteArray) :
    (Execution.gasSteps_73 input).cost = 12 := by rfl
private theorem entry_8e_cost (input : ByteArray) :
    (Execution.gasSteps_8e input).cost = 12 := by rfl
private theorem entry_10f_cost (input : ByteArray) :
    (Execution.gasSteps_10f input).cost = 12 := by rfl
private theorem entry_1b2_cost (input : ByteArray) :
    (Execution.gasSteps_1b2 input).cost = 12 := by rfl
private theorem entry_1db_cost (input : ByteArray) :
    (Execution.gasSteps_1db input).cost = 12 := by rfl
private theorem entry_231_cost (input : ByteArray) :
    (Execution.gasSteps_231 input).cost = 12 := by rfl
private theorem entry_268_cost (input : ByteArray) :
    (Execution.gasSteps_268 input).cost = 12 := by rfl
private theorem entry_3c1_cost (input : ByteArray) :
    (Execution.gasSteps_3c1 input).cost = 12 := by rfl
private theorem entry_3ee_cost (input : ByteArray) :
    (Execution.gasSteps_3ee input).cost = 1 := by rfl

theorem entry_cost (input : ByteArray) :
    (Execution.gasSteps_entry input).cost = 12 := by
  unfold Execution.gasSteps_entry
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [entry_start_cost input, entry_3ee_cost input]

private def initStoreWork (w : Artifact.InitStore) : Nat :=
  Challenge.EvmProof.Meter.instrStaticCost .Osaka
      (.push w.valueWidth w.value) +
    (if w.useMsize then 2 else
      Challenge.EvmProof.Meter.instrStaticCost .Osaka
        (.push w.offsetWidth w.offset)) +
    Challenge.EvmProof.Meter.instrStaticCost .Osaka (.op .MSTORE)

private theorem initValue_cost_potential (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = []) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
        (Main.locatedInitValue w hw) s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.instrStaticCost .Osaka
          (.push w.valueWidth w.value) +
        MachineState.memCost (Main.afterInitValue s w).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    (Main.locatedInitValue w hw)
    (Main.run_initValue s w hw hpc hstack hrun) hfork]
  · simp [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Main.locatedInitValue]
  · intro located hmem q hq
    simp [Main.locatedInitValue] at hmem
    rcases hmem with rfl
    simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem initOffset_cost_potential (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) (hm : w.useMsize = false)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 1)))
    (hstack : s.stack = [w.value]) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
        (Main.locatedInitOffset w hw hm) s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.instrStaticCost .Osaka
          (.push w.offsetWidth w.offset) +
        MachineState.memCost (Main.afterInitOffset s w).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    (Main.locatedInitOffset w hw hm)
    (Main.run_initOffset s w hw hm hpc hstack hrun) hfork]
  · simp [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Main.locatedInitOffset]
  · intro located hmem q hq
    simp [Main.locatedInitOffset] at hmem
    rcases hmem with rfl
    simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem initWrite_cost_potential (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 2)))
    (hstack : s.stack = [w.offset, w.value]) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
        (Main.locatedInitWrite w hw) s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.instrStaticCost .Osaka (.op .MSTORE) +
        MachineState.memCost (Main.applyInitStore s w).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    (Main.locatedInitWrite w hw)
    (Main.run_initWrite s w hw hpc hstack hrun) hfork]
  · simp [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Main.locatedInitWrite]
  · intro located hmem q hq
    simp [Main.locatedInitWrite] at hmem
    rcases hmem with rfl
    simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem initStore_cost_potential (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hmsize : w.useMsize = true →
      UInt256.ofNat (32 * s.activeWords.toNat) = w.offset)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Main.gasSteps_initStore s w hw hpc hstack hcode hfork hrun hmsize hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      initStoreWork w +
        MachineState.memCost (Main.applyInitStore s w).activeWords.toNat := by
  have hvalue := initValue_cost_potential s w hw hpc hstack hfork hrun
  by_cases hm : w.useMsize = true
  · let sv := Main.afterInitValue s w
    let so := Main.afterInitOffset s w
    have hwrite := initWrite_cost_potential so w hw (by rfl) (by rfl)
      (by simpa [so, Main.afterInitOffset] using hfork)
      (by simpa [so, Main.afterInitOffset] using hrun)
    simp only [Main.gasSteps_initStore, hm,
      Challenge.EvmProof.GasSteps.trans_cost,
      Challenge.EvmProof.GasSteps.cast_cost,
      Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
      Msize.step_cost]
    simp only [initStoreWork, hm, ↓reduceIte]
    omega
  · have hmfalse : w.useMsize = false := Bool.eq_false_of_not_eq_true hm
    let sv := Main.afterInitValue s w
    let so := Main.afterInitOffset s w
    have hoffset := initOffset_cost_potential sv w hw hmfalse (by rfl) (by rfl)
      (by simpa [sv, Main.afterInitValue] using hfork)
      (by simpa [sv, Main.afterInitValue] using hrun)
    have hwrite := initWrite_cost_potential so w hw (by rfl) (by rfl)
      (by simpa [so, Main.afterInitOffset] using hfork)
      (by simpa [so, Main.afterInitOffset] using hrun)
    simp only [Main.gasSteps_initStore, hm,
      Challenge.EvmProof.GasSteps.trans_cost,
      Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
    simp only [initStoreWork, hmfalse, Bool.false_eq_true, ↓reduceIte]
    omega

private theorem initStores_cost_potential (s : State)
    (ws : List Artifact.InitStore)
    (hmem : ∀ w, w ∈ ws → w ∈ Artifact.initStores)
    (hchain : Main.InitChain ws)
    (hpc : ∀ w, ws.head? = some w →
      s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hmsize : ∀ w, ws.head? = some w → w.useMsize = true →
      UInt256.ofNat (32 * s.activeWords.toNat) = w.offset)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Main.gasSteps_initStores s ws hmem hchain hpc hstack hmsize hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      (ws.map initStoreWork).sum +
        MachineState.memCost (ws.foldl Main.applyInitStore s).activeWords.toNat := by
  induction ws generalizing s with
  | nil => simp [Main.gasSteps_initStores]
  | cons w tail ih =>
      cases tail with
      | nil =>
          have hw : w ∈ Artifact.initStores := hmem w (by simp)
          have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
            hpc w (by simp)
          have hone := initStore_cost_potential s w hw hpcw hstack hcode hfork
            hrun (hmsize w (by simp)) hnp
          simpa [Main.gasSteps_initStores] using hone
      | cons next rest =>
          have hw : w ∈ Artifact.initStores := hmem w (by simp)
          have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
            hpc w (by simp)
          have hnext : next.index = w.index + 3 := hchain.1
          have htail : Main.InitChain (next :: rest) := hchain.2
          have hfirst := initStore_cost_potential s w hw hpcw hstack hcode hfork
            hrun (hmsize w (by simp)) hnp
          have hrest := ih (s := Main.applyInitStore s w)
            (fun x hx => hmem x (List.mem_cons_of_mem w hx)) htail
            (fun x hx => by
              simp only [List.head?_cons, Option.some.injEq] at hx
              subst x
              simp [Main.applyInitStore, hnext])
            (by simp [Main.applyInitStore])
            (fun x hx => by
              simp only [List.head?_cons, Option.some.injEq] at hx
              subst x
              exact Main.nextMsize_after s w next hw
                (hmem next (by simp)) hnext)
            (by simpa [Main.applyInitStore] using hcode)
            (by simpa [Main.applyInitStore] using hfork)
            (by simpa [Main.applyInitStore] using hrun)
            (by simpa [Main.applyInitStore] using hnp)
          simp only [List.map_cons, List.sum_cons, List.foldl_cons] at hrest
          simp only [Main.gasSteps_initStores,
            Challenge.EvmProof.GasSteps.cast_cost,
            Challenge.EvmProof.GasSteps.trans_cost, List.map_cons,
            List.sum_cons, List.foldl_cons]
          omega

theorem bodyInitialization_cost_potential (input : ByteArray) :
    (Main.gasSteps_bodyInitialization input).cost +
        MachineState.memCost (Execution.mainStart input).activeWords.toNat =
      41 + MachineState.memCost (Main.initializedState input).activeWords.toNat := by
  have h := initStores_cost_potential (Execution.mainStart input)
    Artifact.initStores (fun _ hw => hw)
    (by norm_num [Main.InitChain, Artifact.initStores])
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
      simp)
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState,
      deployAddress_not_precompile])
  have hwork : (Artifact.initStores.map initStoreWork).sum = 41 := by
    norm_num [Artifact.initStores, initStoreWork,
      Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]
  rw [hwork] at h
  unfold Main.gasSteps_bodyInitialization
  rw [Challenge.EvmProof.GasSteps.cast_cost]
  change _ = 41 + MachineState.memCost
    (Artifact.initStores.foldl Main.applyInitStore
      (Execution.mainStart input)).activeWords.toNat
  convert h using 1

theorem initialize_cost_of_active (input : ByteArray)
    (hactive : (Main.initializedState input).activeWords.toNat = 5) :
    (Main.gasSteps_initialize input).cost = 68 := by
  have hbody := bodyInitialization_cost_potential input
  rw [hactive] at hbody
  norm_num [MachineState.memCost, Execution.mainStart, Execution.atPC,
    initialState] at hbody
  unfold Main.gasSteps_initialize
  rw [Challenge.EvmProof.GasSteps.trans_cost, entry_cost input]
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationGasTrace
