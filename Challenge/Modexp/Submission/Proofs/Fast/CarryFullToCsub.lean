import Challenge.Modexp.Submission.Proofs.Fast.CarryFullFallback
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSquare

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CarryRowGas CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand

attribute [local irreducible] SquarePrepared.prepared SquarePrepared.before Monpro.mpZeroed
  SquareRowsModel.rows CarryRowModel.rowsCarry Monpro.rowsMem

opaque gasSteps_toCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2784 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 2880 = UInt256.ofNat (2080 + 32 * n))
    (hml : MachineState.readWord mem 2848 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (SquarePrepared.prepared s mem pa pb n) pa pb n n) pdst ret rest) := by
  by_cases hn4 : n = 4
  · subst n
    rw [SquarePrepared.prepared, if_neg (show ¬(4=8 ∧ pa=pb) by simp),
      selectedRows, if_neg (show ¬(4=8 ∧ pa=pb) by simp), if_pos (show 4=4 ∨ 4=8 from Or.inl rfl)]
    exact gasSteps_specializedFour s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact
      hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv
  by_cases hn8 : n = 8
  · subst n
    by_cases hp : pa=pb
    · subst pb
      rw [selectedRows, if_pos ⟨rfl,rfl⟩]
      exact gasSteps_square s mem pa pdst ret rest hcap hact hpa hpaFit hcds hs32 htl hml hminv
        (EarlyCsub.environment s hcode hfork hrun hnp)
    · rw [SquarePrepared.prepared, if_neg (show ¬(8=8 ∧ pa=pb) by simp [hp]),
        selectedRows, if_neg (show ¬(8=8 ∧ pa=pb) by simp [hp]), if_pos (show 8=4 ∨ 8=8 from Or.inr rfl)]
      exact gasSteps_specializedEight s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact
        hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv hp
  rw [SquarePrepared.prepared, if_neg (show ¬(n=8 ∧ pa=pb) by simp [hn8]),
    SquarePrepared.before, SquarePrepared.selected, inputMemory,
    if_neg (show ¬(n=4 ∨ n=8) by simp [hn4, hn8]),
    if_neg (show ¬(n=4 ∨ n=8) by simp [hn4, hn8])]
  exact gasSteps_fallback s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn hn32
    hpa (by omega) hpb (by omega) hcds hs32 htl hml hminv hn4 hn8

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
