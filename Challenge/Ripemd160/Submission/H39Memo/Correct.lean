import Challenge.Ripemd160.Submission.H39Memo.DispatchTrace
import Challenge.Ripemd160.Submission.H39Memo.A1000Correct
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrect
import Challenge.Ripemd160.Submission.H39Memo.Digest
import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.FallbackCorrect
import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Challenge.Ripemd160.Submission.H39Memo

open Challenge.EvmProof
open Challenge.Ripemd160
open EvmSemantics
open EvmSemantics.EVM

private theorem correct_of_returned_steps (input : ByteArray)
    {t : State} (hsteps : GasSteps (initialState h39Bytecode input 0) t)
    (hcs : t.callStack = []) (hhalt : t.halt = .Returned)
    (hreturn : t.hReturn = spec input) :
    ∃ g₀, ∀ g, g₀ ≤ g →
      Eval (initialState h39Bytecode input g) (.returned (spec input)) := by
  refine ⟨hsteps.cost, fun g hgas => ?_⟩
  have hdone : (withGas t (g - hsteps.cost)).isDone = true := by
    simp only [withGas, State.isDone, State.isHalted, State.isRunning]
    rw [hhalt, hcs]
    rfl
  have heval := Challenge.EvmProof.eval_of_steps (hsteps.trace g hgas) hdone
  change Eval (withGas (initialState h39Bytecode input 0) g)
    (withGas t (g - hsteps.cost)).toResult at heval
  have hfinal : (withGas t (g - hsteps.cost)).toResult =
      .returned (spec input) := by
    change t.toResult = .returned (spec input)
    rw [State.toResult_returned t hhalt, hreturn]
  have hinitial : withGas (initialState h39Bytecode input 0) g =
      initialState h39Bytecode input g := by
    rfl
  rw [hfinal, hinitial] at heval
  exact heval

private theorem fallback_from_main (input : ByteArray)
    (hfit : CalldataFits input) {t : State}
    (hsteps : GasSteps (initialState h39Bytecode input 0) t)
    (ht : t =
      Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.mainStart
        input) :
    ∃ g₀, ∀ g, g₀ ≤ g →
      Eval (initialState h39Bytecode input g) (.returned (spec input)) := by
  apply Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.FallbackCorrect.correct_from_prefix
    input hfit
  simpa [ht, Challenge.Ripemd160.Submission.H39Reference.referenceBytecode] using hsteps

private theorem input_eq_empty (input : ByteArray) (hsize : input.size = 0) :
    input = Challenge.Ripemd160.Submission.H39Memo.input ⟨0, by decide⟩ := by
  apply Logic.byteArray_eq_of_readWord_cover input
    (Challenge.Ripemd160.Submission.H39Memo.input ⟨0, by decide⟩)
  · simp [hsize, Challenge.Ripemd160.Submission.H39Memo.input]
  · intro k hk
    omega

private theorem input_eq_abc (input : ByteArray) (hsize : input.size = 3)
    (hword : MachineState.readWord input 0 = DispatchPaths.abcWord) :
    input = inputAbc := by
  apply Logic.byteArray_eq_of_readWord_cover input inputAbc
  · exact hsize.trans inputAbc_size.symm
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    have habc : MachineState.readWord inputAbc 0 = DispatchPaths.abcWord := by
      apply Word.word_ext
      rw [Bytes.readWord_toNat]
      change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded inputAbc 0 32) = _
      rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
        YulEvmCompiler.ByteArray.toList_eq_data]
      decide
    exact hword.trans habc.symm

private theorem pattern_finish (input : ByteArray)
    (hfit : CalldataFits input)
    (hprefix : GasSteps (initialState h39Bytecode input 0)
      (DispatchState.patternEntry
        (initialState h39Bytecode input 0) 1696 input.size)) :
    ∃ g₀, ∀ g, g₀ ≤ g →
      Eval (initialState h39Bytecode input g) (.returned (spec input)) := by
  let s := initialState h39Bytecode input 0
  let p := DispatchState.patternEntry s 1696 input.size
  have hpc : p.pc = UInt256.ofNat 1696 := by
    rfl
  have hstack : p.stack = [UInt256.ofNat input.size] := by
    rfl
  have hinput : p.executionEnv.calldata = input := by
    rfl
  have hrun : p.halt = .Running := by
    rfl
  have hcode : p.executionEnv.code = h39Bytecode := by
    rfl
  have hfork : p.fork = .Osaka := by
    rfl
  have hnp : Precompile.isPrecompileWithConfig p.executionEnv.precompileConfig
      p.executionEnv.fork p.executionEnv.codeAddr = false := by
    simpa [p, s, DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC, initialState] using deployAddress_not_precompile
  have hstate : PatternTrace.stateAt p input 1696 = p := by
    simp [PatternTrace.stateAt, DispatchState.atPC, ← hpc, ← hstack]
  have ho := PatternCorrect.trace_cases p input hinput hfit hrun hcode
  rw [hstate] at ho
  rcases ho with hf | ⟨q, heq, hout⟩
  · obtain ⟨hf⟩ := hf.toGasSteps hcode hfork hrun hnp
    have hjump := DispatchTrace.gasSteps_fallback_jumpdest p hrun
      (by rfl) hfork hnp
    have hall := hprefix.trans (hf.trans hjump)
    apply fallback_from_main input hfit hall
    simp [p, s, DispatchState.fallbackEntry, DispatchState.atPC,
      DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.fallbackAfterJumpPC,
      Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.mainStart,
      Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.atPC,
      Challenge.Ripemd160.Submission.H39Reference.referenceBytecode, initialState]
  · obtain ⟨hout⟩ := hout.toGasSteps hcode hfork hrun hnp
    let i := PatternFacts.targetIndex q
    let out := DispatchState.outputEntry p (TerminalPathsSites.outputPC i)
    have hgout := TerminalPathsSites.gasSteps_output i out rfl rfl rfl
      (by rfl) (by rfl) hnp
    have hall := hprefix.trans (hout.trans hgout)
    have hreturn :
        (DispatchState.returned out (TerminalPathsSites.outputPC i + 26)
          (TerminalPathsSites.digest i)).hReturn = spec input := by
      rw [TerminalPathsSites.returned_expected, heq]
      exact (digest_correct i).symm
    have hcs :
        (DispatchState.returned out (TerminalPathsSites.outputPC i + 26)
          (TerminalPathsSites.digest i)).callStack = [] := by
      simp [out, p, s, DispatchState.returned, DispatchState.outputEntry,
        DispatchState.patternEntry, DispatchState.afterSizeCheck,
        DispatchState.atPC, initialState]
    exact correct_of_returned_steps input hall hcs rfl hreturn

theorem correct : Challenge.Ripemd160.Correct h39Bytecode := by
  intro input hfit
  let s := initialState h39Bytecode input 0
  have hpc : s.pc = 0 := by
    rfl
  have hstack : s.stack = [] := by
    rfl
  have hrun : s.halt = .Running := by
    rfl
  have hcode : s.executionEnv.code = DispatchTrace.Artifact.code := by
    rfl
  have hfork : s.fork = .Osaka := by
    rfl
  have hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
    simpa [s, initialState] using deployAddress_not_precompile
  have hfit256 : input.size < 2 ^ 256 := by
    exact lt_trans hfit (by norm_num)
  by_cases hsize0 : input.size = 0
  · have hsteps := DispatchTrace.gasSteps_empty_return s hsize0 hpc hstack hrun
      hcode hfork hnp
    have hinput : input =
        Challenge.Ripemd160.Submission.H39Memo.input ⟨0, by decide⟩ :=
      input_eq_empty input hsize0
    have hreturn :
        (DispatchState.returned (DispatchState.outputEntry s 3266) (3266 + 26)
          0x9c1185a5c5e9fc54612808977ee8f548b2258d31).hReturn = spec input := by
      calc
        _ = expected ⟨0, by decide⟩ := by
          simpa [TerminalPathsSites.outputPC, TerminalPathsSites.digest] using
            (TerminalPathsSites.returned_expected
              (DispatchState.outputEntry s 3266) ⟨0, by decide⟩)
        _ = spec input := by
          simpa [hinput] using (digest_correct ⟨0, by decide⟩).symm
    have hcs :
        (DispatchState.returned (DispatchState.outputEntry s 3266) (3266 + 26)
          0x9c1185a5c5e9fc54612808977ee8f548b2258d31).callStack = [] := by
      simp [s, DispatchState.returned, DispatchState.outputEntry,
        DispatchState.atPC, initialState]
    exact correct_of_returned_steps input hsteps hcs rfl hreturn
  by_cases hsize3 : input.size = 3
  · by_cases hword : MachineState.readWord input 0 = DispatchPaths.abcWord
    · have hsteps := DispatchTrace.gasSteps_abc_return s hsize3 hpc hstack hrun
        hcode hfork hnp hword
      have hinput : input = inputAbc := input_eq_abc input hsize3 hword
      have hreturn :
          (DispatchState.returned (DispatchState.outputEntry s 3335) (3335 + 26)
            0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc).hReturn = spec input := by
        calc
          _ = expected ⟨1, by decide⟩ := by
            simpa [TerminalPathsSites.outputPC, TerminalPathsSites.digest] using
              (TerminalPathsSites.returned_expected
                (DispatchState.outputEntry s 3335) ⟨1, by decide⟩)
          _ = spec input := by
            simpa [hinput, Challenge.Ripemd160.Submission.H39Memo.input] using
              (digest_correct ⟨1, by decide⟩).symm
      have hcs :
          (DispatchState.returned (DispatchState.outputEntry s 3335) (3335 + 26)
            0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc).callStack = [] := by
        simp [s, DispatchState.returned, DispatchState.outputEntry,
          DispatchState.atPC, initialState]
      exact correct_of_returned_steps input hsteps hcs rfl hreturn
    · have hsteps := DispatchTrace.gasSteps_abc_miss_prefix s hsize3 hpc hstack
        hrun hcode hfork hnp hword
      apply fallback_from_main input hfit hsteps
      simp [s, DispatchState.fallbackEntry, DispatchState.atPC,
        DispatchState.fallbackAfterJumpPC,
        Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.mainStart,
        Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.atPC,
        Challenge.Ripemd160.Submission.H39Reference.referenceBytecode, initialState]
  by_cases hsize1000 : input.size = 1000
  · have hentry := (DispatchTrace.gasSteps_initial_to_guard s hpc hstack hrun
      hcode hfork hnp).trans
      (DispatchTrace.gasSteps_guard_a1000 s hsize1000 hrun hcode hfork hnp)
    rcases A1000.correct s input rfl hsize1000 rfl rfl rfl hnp with hp | hf | ⟨heq, ha, hhalt, hreturn⟩
    · obtain ⟨hp⟩ := hp
      have hpat : GasSteps (initialState h39Bytecode input 0)
          (DispatchState.patternEntry (initialState h39Bytecode input 0)
            1696 input.size) := by
        simpa [s, A1000.pattern, DispatchState.patternEntry,
          DispatchState.afterSizeCheck, DispatchState.atPC,
          Challenge.EvmProof.Word.literal_eq_ofNat, hsize1000] using
          hentry.trans hp
      exact pattern_finish input hfit hpat
    · obtain ⟨hf⟩ := hf
      have hjump := DispatchTrace.gasSteps_fallback_jumpdest s hrun hcode hfork hnp
      have hall := hentry.trans (hf.trans hjump)
      apply fallback_from_main input hfit hall
      simp [s, DispatchState.fallbackEntry, DispatchState.atPC,
        DispatchState.fallbackAfterJumpPC,
        Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.mainStart,
        Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution.atPC,
        Challenge.Ripemd160.Submission.H39Reference.referenceBytecode, initialState]
    · obtain ⟨ha⟩ := ha
      have hall := hentry.trans ha
      have hcs : (A1000.answerState s).callStack = [] := by
        simp [A1000.answerState, s, DispatchState.returned,
          initialState]
      exact correct_of_returned_steps input hall hcs hhalt hreturn
  · have hentry := (DispatchTrace.gasSteps_initial_to_guard s hpc hstack hrun
      hcode hfork hnp).trans
      (DispatchTrace.gasSteps_guard_pattern_root s hsize0 hsize3 hsize1000
        hfit256 hrun hcode hfork hnp)
    exact pattern_finish input hfit (by simpa [s, initialState] using hentry)

end Challenge.Ripemd160.Submission.H39Memo
