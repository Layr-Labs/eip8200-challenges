import Challenge.Modexp.Submission.Proofs.Fast.CsubFixedFour

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local irreducible] csStep

def gasSteps_csub (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hml : MachineState.readWord memory 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n))
    (hs32 : MachineState.readWord (csStep memory n n).memory 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (csStep memory n n).memory 8224).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
      (csReturnedState s memory n n pdst ret rest) := by
  have hnn : n - 1 + 1 = n := by omega
  have hsrcFit : (csSrc memory n n).toNat + 32 * n ≤ 9472 := by
    rw [csSrc_toNat memory n n (csUse_le_one memory n n htn)]
    split <;> omega
  have hs : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n) := by
    rw [csStep_readWord_disjoint memory n 9344 (by omega) (by omega) n le_rfl] at hs32
    exact hs32
  by_cases hn8 : n = 8
  · subst n
    exact gasSteps_csFixed8 s memory pdst ret rest hcap hrun hcode hact hfork hnp hs hjump hs32 hdstFit hsrcFit
  by_cases hn4 : n = 4
  · subst n
    exact gasSteps_csFixed4 s memory pdst ret rest hcap hrun hcode hact hfork hnp hs hjump hs32 hdstFit hsrcFit
  exact (((gasSteps_csEntry s memory n pdst ret rest hcap hcode hfork hrun hnp hs hn8 hn4 hact hn hn32
        hml htl).trans
      (gasSteps_csLoop s memory n pdst ret rest hcap hcode hfork hrun hnp hact hn32)).trans
      (gasSteps_csExit s memory n pdst ret rest hcap hcode hfork hrun hnp hact hn hn32)).trans
    (Challenge.EvmProof.GasSteps.cast
      (gasSteps_csTailStep s memory n n pdst ret rest hcap hcode hfork hrun hnp hact hn
        hn32 hjump hs32 hdstFit hsrcFit)
      (by rw [hnn]) rfl)

end Challenge.Modexp.Submission.Proofs.Fast.Csub
