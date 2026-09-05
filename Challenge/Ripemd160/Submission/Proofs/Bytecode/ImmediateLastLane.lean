import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLastRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLastLane

open EvmSemantics EvmSemantics.EVM
open CompressionRightTrace

def gasSteps_rightLast (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
    (hstack : rest.length < 977)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ImmediateLaneTrace.rightAt s messageOffset returnDest rest 79)
      {rightStates s messageOffset returnDest rest 80 with
        pc := UInt256.ofNat 0x324
        stack := [UInt256.ofNat 0, messageOffset, returnDest] ++ rest} := by
  let q := rightStates s messageOffset returnDest rest 79
  have hqcode : q.executionEnv.code = submissionBytecode := by
    rw [rightStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, rightStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by rw [rightStates_halt]; exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    rw [rightStates_executionEnv]
    exact hnp
  have hqactive : 67 ≤ q.activeWords.toNat := by
    rw [ImmediateStateFacts.rightStates_activeWords s messageOffset returnDest rest
      tables hactive 79 (by omega)]
    exact hactive
  have hqtables := ImmediateStateFacts.rightStates_tables_preserved
    s messageOffset returnDest rest 79 tables
  have hqconstants : ∀ j, j < 5 →
      InitializationCorrect.slotWord q.memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
    intro j hj
    rw [ImmediateStateFacts.rightStates_slotWord s messageOffset returnDest rest
      79 0x6c0 j (by omega)]
    exact constants j hj
  have hpinned := ImmediateModelMatch.rightRoundState_pinned q messageOffset returnDest
    rest 79 (by omega) hqactive hqtables hqconstants (UInt256.ofNat 0x324)
    ([UInt256.ofNat 0, messageOffset, returnDest] ++ rest)
  have hmodel := ImmediateLastRound.lastRoundModel_of_pinned q messageOffset returnDest
    rest (UInt256.ofNat 0x324) ([UInt256.ofNat 0, messageOffset, returnDest] ++ rest)
    hpinned rfl rfl
  have g := ImmediateLastRound.gasSteps_lastRound q messageOffset returnDest rest
    ImmediateLastRound.artifactLastRoundCertificate hmodel hstack
    hqcode hqfork hqrun hqnp
  exact g.cast rfl rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLastLane
