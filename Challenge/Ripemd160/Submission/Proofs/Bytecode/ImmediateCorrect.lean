import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateBlockTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLastLane
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFastPC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateRunTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open ImmediateBlockTrace

noncomputable def blockTrace (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) : ImmediateRunTrace.RestrictedBlockTrace s input i hfit := by
  intro hi htables hconstants hcode hfork hrun hnp
  let q0 := blockInitialState s input i
  let msg := blockMessageOffset input i
  let rest := blockRest input i
  have h0active : 67 ≤ q0.activeWords.toNat :=
    blockInitial_activeWords_ge67 s input i hfit hi blockReturnDest rest
  have h0tables : InitializationCorrect.TablesCorrect q0.memory :=
    leftInitialState_tables_of_tables s msg blockReturnDest rest htables
  have h0constants := leftInitialState_constants_of_constants s msg
    blockReturnDest rest hconstants
  let q := CompressionTrace.leftStates q0 msg blockReturnDest rest 80
  have hactive : 67 ≤ q.activeWords.toNat := by
    rw [ImmediateStateFacts.leftStates_activeWords q0 msg blockReturnDest rest
      h0tables h0active 80 (by omega)]
    exact h0active
  have tables : InitializationCorrect.TablesCorrect q.memory :=
    ImmediateStateFacts.leftStates_tables_preserved q0 msg blockReturnDest rest 80 h0tables
  have constants : ∀ j, j < 5 →
      InitializationCorrect.slotWord q.memory 0x6c0 j =
        Word.ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
    intro j hj
    rw [ImmediateStateFacts.leftStates_slotWord q0 msg blockReturnDest rest
      80 0x6c0 j (by omega)]
    exact h0constants.2 j hj
  have henv : q.executionEnv = s.executionEnv := by
    rw [CompressionTrace.leftStates_executionEnv]
    exact leftInitialState_executionEnv s msg blockReturnDest rest
  have hhalt : q.halt = s.halt := by
    rw [CompressionTrace.leftStates_halt]
    exact leftInitialState_halt s msg blockReturnDest rest
  have qcode : q.executionEnv.code = submissionBytecode := by rw [henv]; exact hcode
  have qfork : q.fork = .Osaka := by rw [State.fork, henv]; exact hfork
  have qrun : q.halt = .Running := by rw [hhalt]; exact hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [henv]; exact hnp
  have hstack : rest.length < 977 := by
    simp [rest, blockRest, CompressionModel.driverRest]
  have glast := ImmediateLastLane.gasSteps_rightLast q msg blockReturnDest rest
    hactive tables constants hstack qcode qfork qrun qnp
  exact gasSteps_compressBlock s input i hfit hi htables hconstants hcode hfork hrun hnp
    ImmediateSiteCertificates.leftCertificate80 ImmediateFastPC.leftNextPC
    ImmediateSiteCertificates.rightCertificate79 ImmediateFastPC.rightNextPC glast

theorem correct : Correct submissionBytecode :=
  ImmediateRunTrace.correct_of_restrictedBlockTrace
    (fun input hfit i => blockTrace (ImmediateRunTrace.states input i) input i hfit)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateCorrect
