import Challenge.Modexp.Submission.Proofs.Fast.TnM128R4Reduction
import Challenge.Modexp.Submission.Proofs.Fast.TnM128R8Reduction

set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128ReductionSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory

def middlePC (n : Nat) : Nat := if n = 4 then 5431 else 3832
def l2PC (n : Nat) : Nat := if n = 4 then 3987 else 3851

noncomputable def reduction_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi tn : UInt256) (n : Nat) (hn : n = 4 ∨ n = 8)
    (pbi hd pb ent m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache q.memory n tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache q.memory m96 m64 m32)
    (hi : inverseInvariant q.memory n)
    (hcache : m128 = MachineState.readWord q.memory 128)
    (hjd : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    GasSteps
      (framed {s with memory := q.memory} (UInt256.ofNat (middlePC n))
        ([q.carry,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest))
      (framed {s with memory := (TnCacheSquareModel.fromL1 q tn n).memory}
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd else UInt256.ofNat 4138)
        (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
          (TnCacheSquareModel.fromL1 q tn n).tn m128 inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  by_cases h4 : n = 4
  · subst n
    exact TnM128R4Reduction.reduction_steps s env q bi tn pbi hd pb ent m128 tl inv m0
      aEnd m96 m64 m32 dst ret rest hcap hact hc he hi hcache hjd
  · have h8 : n = 8 := hn.resolve_left h4
    subst n
    exact TnM128R8Reduction.reduction_steps s env q bi tn pbi hd pb ent m128 tl inv m0
      aEnd m96 m64 m32 dst ret rest hcap hact hc he hi hcache hjd

#print axioms reduction_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128ReductionSteps
