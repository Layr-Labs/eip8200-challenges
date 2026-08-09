import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGasBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private theorem potential_trans {a b p q r k l : Nat}
    (h₁ : a + p = k + q) (h₂ : b + q = l + r) :
    (a + b) + p = (k + l) + r := by
  omega

private theorem shift_cost_potential
    (path : List
      (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (q : State) (src dest loadReturn storeReturn startPC work : Nat)
    (context : List UInt256)
    (hmatch :
      (path = Compression.shift76Path ∧ src = 6 ∧ dest = 7 ∧
        loadReturn = 796 ∧
        storeReturn = 803 ∧ startPC = 783) ∨
      (path = Compression.shift65Path ∧ src = 5 ∧ dest = 6 ∧
        loadReturn = 817 ∧
        storeReturn = 824 ∧ startPC = 803) ∨
      (path = Compression.shift32Path ∧ src = 2 ∧ dest = 3 ∧
        loadReturn = 872 ∧
        storeReturn = 879 ∧ startPC = 858) ∨
      (path = Compression.shift21Path ∧ src = 1 ∧ dest = 2 ∧
        loadReturn = 893 ∧ storeReturn = 900 ∧ startPC = 879))
    (hpc : q.pc = UInt256.ofNat startPC) (hstack : q.stack = context)
    (hcap : context.length < 1016)
    (hcode : q.executionEnv.code = submissionBytecode)
    (hfork : q.fork = .Osaka) (hrun : q.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false)
    (hwork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    (Compression.gasSteps_shift path q src dest loadReturn
      storeReturn startPC context hmatch hpc hstack hcap hcode hfork hrun
      hnp).cost + MachineState.memCost q.activeWords.toNat =
      work + MachineState.memCost
        (Compression.shiftReturned q src dest loadReturn storeReturn context).activeWords.toNat := by
  have hdirect := blockCost_potential_of_static path work
    (Compression.run_shiftDirect path q src dest loadReturn storeReturn startPC
      context hmatch hpc hstack (by omega) hrun) hfork
    (by rcases hmatch with h | h | h | h <;>
        rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp [Compression.shift76Path, Compression.shift65Path,
          Compression.shift32Path, Compression.shift21Path, CopyFree])
    hwork
  unfold Compression.gasSteps_shift
  simpa only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost] using hdirect

theorem updates_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_updates s msgOff returnDest rest j hj hcap hcode
      hfork hrun hnp).cost + MachineState.memCost
        (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat =
      150 + MachineState.memCost
        (Compression.afterSecondIteration s msgOff returnDest rest j).activeWords.toNat := by
  let ctx := Compression.roundContext s msgOff returnDest rest j
  have hctx : ctx.length < 1016 := by simp [ctx, Compression.roundContext]; omega
  let q0 := Compression.afterT2 s msgOff returnDest rest j
  have q0code : q0.executionEnv.code = submissionBytecode := by
    simpa [q0] using hcode
  have q0fork : q0.fork = .Osaka := by simpa [q0, State.fork] using hfork
  have q0run : q0.halt = .Running := by simpa [q0] using hrun
  have q0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0] using hnp
  have hs7 := shift_cost_potential Compression.shift76Path
    q0 6 7 796 803 783 13 ctx
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by rfl) (by rfl) hctx q0code q0fork q0run q0np (by rfl)
  let q1 := Compression.afterShift7 s msgOff returnDest rest j
  have q1code : q1.executionEnv.code = submissionBytecode := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q0code
  have q1fork : q1.fork = .Osaka := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q0fork
  have q1run : q1.halt = .Running := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q0run
  have q1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q0np
  have hs6 := shift_cost_potential Compression.shift65Path
    q1 5 6 817 824 803 13 ctx
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))
    (by rfl) (by rfl) hctx q1code q1fork q1run q1np (by rfl)
  let q2 := Compression.afterShift6 s msgOff returnDest rest j
  have q2code : q2.executionEnv.code = submissionBytecode := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q1code
  have q2fork : q2.fork = .Osaka := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q1fork
  have q2run : q2.halt = .Running := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q1run
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q1np
  have hstoreE := blockCost_potential_of_static Compression.storeEPath 10
    (Compression.run_storeE s msgOff returnDest rest j (by omega) hrun)
    q2fork (by simp [Compression.storeEPath, CopyFree]) (by rfl)
  let q3 := Compression.afterStoreE s msgOff returnDest rest j
  have q3code : q3.executionEnv.code = submissionBytecode := by
    simpa [q3, Compression.afterStoreE, Compression.directStored] using q2code
  have q3fork : q3.fork = .Osaka := by
    simpa [q3, Compression.afterStoreE, Compression.directStored, State.fork]
      using q2fork
  have q3run : q3.halt = .Running := by
    simpa [q3, Compression.afterStoreE, Compression.directStored] using q2run
  have q3np : Precompile.isPrecompileWithConfig q3.executionEnv.precompileConfig q3.executionEnv.fork
      q3.executionEnv.codeAddr = false := by
    simpa [q3, Compression.afterStoreE, Compression.directStored] using q2np
  have hupdateH4 := blockCost_potential_of_static
    Compression.setupH3ForH4Path 24
    (Compression.run_updateH4 s msgOff returnDest rest j (by omega) hrun)
    q3fork (by simp [Compression.setupH3ForH4Path, CopyFree]) (by rfl)
  let q4 := Compression.afterStoreH4 s msgOff returnDest rest j
  have q4code : q4.executionEnv.code = submissionBytecode := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned] using q3code
  have q4fork : q4.fork = .Osaka := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned, State.fork] using q3fork
  have q4run : q4.halt = .Running := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned] using q3run
  have q4np : Precompile.isPrecompileWithConfig q4.executionEnv.precompileConfig q4.executionEnv.fork
      q4.executionEnv.codeAddr = false := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned] using q3np
  have hs3 := shift_cost_potential Compression.shift32Path
    q4 2 3 872 879 858 13 ctx
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))
    (by rfl) (by rfl) hctx q4code q4fork q4run q4np (by rfl)
  let q5 := Compression.afterShift3 s msgOff returnDest rest j
  have q5code : q5.executionEnv.code = submissionBytecode := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q4code
  have q5fork : q5.fork = .Osaka := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q4fork
  have q5run : q5.halt = .Running := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q4run
  have q5np : Precompile.isPrecompileWithConfig q5.executionEnv.precompileConfig q5.executionEnv.fork
      q5.executionEnv.codeAddr = false := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q4np
  let q5rawState := Compression.shiftReturned q4 2 3 872 879 ctx
  have q5rawCode : q5rawState.executionEnv.code = submissionBytecode := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned] using q4code
  have q5rawFork : q5rawState.fork = .Osaka := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned, State.fork] using q4fork
  have q5rawRun : q5rawState.halt = .Running := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned] using q4run
  have q5rawNp : Precompile.isPrecompileWithConfig q5rawState.executionEnv.precompileConfig q5rawState.executionEnv.fork
      q5rawState.executionEnv.codeAddr = false := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned] using q4np
  have hs2 := shift_cost_potential Compression.shift21Path
    q5rawState 1 2 893 900 879 13 ctx
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))
    (by rfl) (by rfl) hctx q5rawCode q5rawFork q5rawRun q5rawNp (by rfl)
  have hfinish := blockCost_potential_of_static Compression.finishRoundPath 64
    (Compression.run_finishRound s msgOff returnDest rest j hj (by omega)
      hcode hrun)
    (by simpa [Compression.afterShift2, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q5fork)
    (by simp [Compression.finishRoundPath, CopyFree]) (by rfl)
  unfold Compression.gasSteps_updates
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  change _ = 13 + MachineState.memCost q1.activeWords.toNat at hs7
  change _ = 13 + MachineState.memCost q2.activeWords.toNat at hs6
  change _ = 24 + MachineState.memCost q4.activeWords.toNat at hupdateH4
  change _ = 13 + MachineState.memCost q5rawState.activeWords.toNat at hs3
  change _ = 13 + MachineState.memCost
    (Compression.afterShift2 s msgOff returnDest rest j).activeWords.toNat at hs2
  dsimp only [q0, q1, q2, q3, q4, q5, q5rawState, ctx] at *
  have h₁ := potential_trans hs7 hs6
  have h₂ := potential_trans h₁ hstoreE
  have h₃ := potential_trans h₂ hupdateH4
  have h₄ := potential_trans h₃ hs3
  have h₅ := potential_trans h₄ hs2
  have h₆ := potential_trans h₅ hfinish
  unfold Compression.gasSteps_shift at h₆ ⊢
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Compression.afterShift2, Compression.afterShift3] at h₆ ⊢
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h₆


end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas
