import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneModel

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneStep

open EvmSemantics EvmSemantics.EVM
open ImmediateIteration ImmediateWrapper

def gasSteps_leftRound (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (cert : WrapperSiteCertificate (leftSite i))
    (hvalid : Decode.isValidJumpDest submissionBytecode (leftSite i).ret.toNat = true)
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x620 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wrapperEntryAt (leftSite i) s messageOffset returnDest rest)
      {CompressionTrace.leftRoundState s messageOffset returnDest rest i with
        pc := (leftSite i).ret
        stack := [messageOffset, returnDest] ++ rest} := by
  have hj : (leftSite i).j.toNat < 5 := by
    change (UInt256.ofNat (i / 16)).toNat < 5
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have gw := gasSteps_wrapper_site (leftSite i) cert s messageOffset returnDest rest
    hstack hcode hfork hrun hnp
  have hstackRound : ([messageOffset, returnDest] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have gr := RoundTrace.gasSteps_round s (leftSite i).base (leftSite i).j.toNat hj
    (leftSite i).wordIndex (leftSite i).rotation (leftSite i).k (leftSite i).ret
    ([messageOffset, returnDest] ++ rest) hstackRound hcode hfork hrun hnp hvalid
  exact gw.trans (gr.cast rfl
    (ImmediateLaneModel.leftSite_roundReturned s messageOffset returnDest rest
      i hi hactive tables constants))

def gasSteps_rightRound (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (cert : WrapperSiteCertificate (rightSite i))
    (hvalid : Decode.isValidJumpDest submissionBytecode (rightSite i).ret.toNat = true)
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wrapperEntryAt (rightSite i) s messageOffset returnDest rest)
      {CompressionRightTrace.rightRoundState s messageOffset returnDest rest i with
        pc := (rightSite i).ret
        stack := [messageOffset, returnDest] ++ rest} := by
  have hj : (rightSite i).j.toNat < 5 := by
    change (UInt256.ofNat (4 - i / 16)).toNat < 5
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have gw := gasSteps_wrapper_site (rightSite i) cert s messageOffset returnDest rest
    hstack hcode hfork hrun hnp
  have hstackRound : ([messageOffset, returnDest] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have gr := RoundTrace.gasSteps_round s (rightSite i).base (rightSite i).j.toNat hj
    (rightSite i).wordIndex (rightSite i).rotation (rightSite i).k (rightSite i).ret
    ([messageOffset, returnDest] ++ rest) hstackRound hcode hfork hrun hnp hvalid
  exact gw.trans (gr.cast rfl
    (ImmediateLaneModel.rightSite_roundReturned s messageOffset returnDest rest
      i hi hactive tables constants))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneStep
