import Challenge.Ripemd160.Submission.H39Memo.A1000Advance

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

def answerWord : UInt256 := 972889429405991776604892044862621566948497025487

def answerState (s : State) : State := DispatchState.returned s 3250 answerWord

theorem run_answer (s : State) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock answerPath (answerEntry s) = some (answerState s) := by
  simp [answerPath, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, answerEntry, answerState, answerWord, DispatchState.returned,
    atPC, hrun, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

end Challenge.Ripemd160.Submission.H39Memo.A1000
