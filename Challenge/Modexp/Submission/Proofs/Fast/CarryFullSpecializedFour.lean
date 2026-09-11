import Challenge.Modexp.Submission.Proofs.Fast.CarryFullRowsFour
import Challenge.Modexp.Submission.Proofs.Fast.SquareEntry

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CarryRowGas CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared (before)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

opaque gasSteps_specializedFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsCarry (mpZeroed s (before mem pa pb 4) 4) pa pb 4 4) pdst ret rest) := by
  have env := EarlyCsub.environment s hcode hfork hrun hnp
  have hguard : ¬UInt256.isTrue (SquareSelect.guard mem (UInt256.ofNat pa) (UInt256.ofNat pb)) := by
    rw [SquareEntry.guard_iff mem pa pb 4 (by decide) (by omega) (by omega) hs32]
    simp
  have hctrl := SquareEntry.control_before mem pa pb 4 (Or.inl rfl) hguard
  have hread (addr : Nat) (hd : addr+32 ≤ 8192 ∨ 9312 ≤ addr) :
      MachineState.readWord (before mem pa pb 4) addr = MachineState.readWord mem addr :=
    SquarePrepared.read_before_outside mem pa pb 4 addr hd
  have hminv' : inverseInvariant (before mem pa pb 4) 4 := by
    simpa only [inverseInvariant, hread (32*4-32) (Or.inl (by decide)),
      hread 9376 (Or.inr (by decide))] using hminv
  have hsz : StagedOperand.Snapshot (before mem pa pb 4) pa 4 := by
    have h := snapshot_stage (SquarePrepared.selected mem pa pb 4) pa 4 hpaFit
    simpa only [SquarePrepared.before, inputMemory, if_pos (show 4=4 ∨ 4=8 from Or.inl rfl),
      or_true, true_or, ite_true] using h
  refine (SquareEntry.gasSteps_header s mem pa pb 4 pdst ret rest hcap hact (Or.inl rfl)
    hpa hpaFit hpb hpbFit hcds hs32 hml env).trans ?_
  have hr : Challenge.EvmProof.GasSteps
      {SquareEntry.out s mem pa pb 4 pdst ret rest with pc := UInt256.ofNat 4159}
      (SquareEntry.out s mem pa pb 4 pdst ret rest) := by
    exact SquareEntry.gasSteps_route s (mpZeroed s (before mem pa pb 4) 4) (UInt256.ofNat 4164)
      (SquareEntry.out s mem pa pb 4 pdst ret rest).stack
      (by simp only [SquareEntry.out, outState, SquareEntry.args, List.length_append, List.length_cons, List.length_nil]; omega)
      hact (hctrl.zeroed s 4 (by decide)).route
      (Artifact.isValidJumpDest_index 3147 (by rfl)) env
  refine hr.trans ?_
  exact gasSteps_rowsFour s (before mem pa pb 4) pa pb
    (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
    (MachineState.readWord mem (32*4-32)) (UInt256.ofNat (pa+32*4-32))
    (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) pdst ret rest hcap hrun hcode hfork hnp hact
    hpa hpaFit hpb (by omega)
    ((hread 9344 (Or.inr (by decide))).trans hs32)
    ((hread 9440 (Or.inr (by decide))).trans htl)
    ((hread 9408 (Or.inr (by decide))).trans hml) hminv'
    ⟨htl, (hread 9376 (Or.inr (by decide))).symm,
      (hread (32*4-32) (Or.inl (by decide))).symm⟩
    ⟨(hread 96 (Or.inl (by decide))).symm,
      (hread 64 (Or.inl (by decide))).symm,
      (hread 32 (Or.inl (by decide))).symm⟩ rfl hsz hctrl

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
