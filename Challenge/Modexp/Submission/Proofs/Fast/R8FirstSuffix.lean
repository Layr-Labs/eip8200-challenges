import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8FirstSuffix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open CiosCached CarryRowBlocks CarryRowModel CarryRowGas
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

/-- The current U first-row result already enters at the eight-limb JUMPDEST.
Execute that destination and the seven existing reduction cells to the tail,
without replaying the obsolete L2 dispatch. Memory and carry are arbitrary. -/
opaque gasSteps (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 3782 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 8 7).memory
        (l2Step mid mu c0 8 7).carry mu bi pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (l2Join8.steps (environment (l2At 3782 s mid bi mu c0 pb 8 i 0 hd ent inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (run_l2Join8 s mid bi mu c0 pb 8 i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap')).trans <|
  (gasSteps_l2Mac 3783 10 192 2304 2336 l2Mac0 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 3827 1 160 2272 2304 l2Mac1 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 3862 1 128 2240 2272 l2Mac2 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_extraL2 0 3897 96 2208 2240 l2Mac3 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2Join s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_extraL2 1 3931 64 2176 2208 l2Mac4 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_extraL2 2 3964 32 2144 2176 l2Mac5 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2Final s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

#print axioms gasSteps
end Challenge.Modexp.Submission.Proofs.Fast.R8FirstSuffix
