import Challenge.Modexp.Submission.Proofs.Fast.SquareEntry
import Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsGas
import Challenge.Modexp.Submission.Proofs.Fast.SquareFourPreparedCorrect

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMidMemory SquareInit StagedOperand SquarePrepared

attribute [local irreducible] SquareInit.initMemory SquareFourInit.initMemory Monpro.mpZeroed SquarePrepared.before SquareFourRowsModel.rows

opaque gasSteps_square_four (s : State) (mem : ByteArray) (pa : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpafit : pa+128 ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2784 = UInt256.ofNat 128)
    (htl : MachineState.readWord mem 2880 = UInt256.ofNat 2208)
    (hml : MachineState.readWord mem 2848 = UInt256.ofNat 96)
    (hinv : inverseInvariant mem 4)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (Cios2Dispatch.dispatchState s mem pa pa dst ret rest)
      (mpCsubState s (SquareFourRowsModel.rows (prepared s mem pa pa 4) pa 4) dst ret rest) := by
  let initial := mpZeroed s (before mem pa pa 4) 4
  let start := SquareEntry.out s mem pa pa 4 dst ret rest
  have hlen : start.stack.length ≤ 1018 := by
    simp only [start, SquareEntry.out, CiosCached.outState, SquareEntry.args,
      List.length_append, List.length_cons, List.length_nil]
    omega
  have hg : UInt256.isTrue (SquareSelect.guard mem (UInt256.ofNat pa) (UInt256.ofNat pa)) :=
    (SquareEntry.guard_iff mem pa pa 4 (by decide) (by omega) (by omega) hs32).2 rfl
  have hr : MachineState.readWord initial 2720 = UInt256.ofNat 5040 := by
    rw [mpZeroed_readWord_outside s _ 4 2720 (Or.inr (by decide))]
    simp only [before, inputMemory, selected, if_pos (show 4=4 ∨ 4=8 from Or.inl rfl),
      or_true, true_or, ite_true, SquareSelect.selectedMemory, if_pos hg]
    rw [read_stage_outside _ _ _ _ (Or.inr (by decide)), read_storeWord]
  have hheader := SquareEntry.gasSteps_header s mem pa pa 4 dst ret rest hcap hact (Or.inl rfl)
    hpa hpafit hpa hpafit hcds hs32 hml env
  have hroute := SquareEntry.gasSteps_route s initial (UInt256.ofNat 5040) start.stack
    (by omega) hact hr SquareParts.jump_init env
  have hinit := gasSteps_init4 s initial start.stack hlen hact env
    (by rfl)
  have hprepared : prepared s mem pa pa 4 = SquareFourInit.initMemory initial := by
    rw [prepared, if_neg (by simp : ¬(4=8 ∧ pa=pa)), if_pos ⟨rfl,rfl⟩]
  have hentry : Challenge.EvmProof.GasSteps (Cios2Dispatch.dispatchState s mem pa pa dst ret rest)
      (SquareFourRowsGas.state s (prepared s mem pa pa 4) pa 0
        (MachineState.readWord mem 2880) (MachineState.readWord mem 2816) (MachineState.readWord mem 96)
        (UInt256.ofNat (pa+96)) (MachineState.readWord mem 96) (MachineState.readWord mem 64)
        (MachineState.readWord mem 32) dst ret rest) := by
    have hpadd : pa+32*4-32 = pa+96 := by omega
    simpa only [SquareFourRowsGas.state, SquareFourRowsGas.tag, hprepared,
      initial, start, SquareEntry.out, CiosCached.outState, SquareEntry.args, Nat.reduceLT,
      ite_true, true_and, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, hpadd,
      ptrAt_zero, show l2Target 4 = UInt256.ofNat 4661 by decide, SquareDiagonal.base, stateAt, List.cons_append, List.nil_append] using
      hheader.trans (hroute.trans hinit)
  have hread (addr : Nat) (hd : addr+32 ≤ 2048 ∨ 2752 ≤ addr) := read_prepared_outside s mem pa pa 4 addr (by decide) hd
  refine hentry.trans <| SquareFourRowsGas.gasSteps_rows s (prepared s mem pa pa 4) pa
    (MachineState.readWord mem 2880) (MachineState.readWord mem 2816) (MachineState.readWord mem 96)
    (UInt256.ofNat (pa+96)) (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) dst ret rest hcap hact hpa hpafit
    ⟨htl, (hread 2816 (Or.inr (by decide))).symm, (hread 96 (Or.inl (by decide))).symm⟩
    ⟨(hread 96 (Or.inl (by decide))).symm, (hread 64 (Or.inl (by decide))).symm,
      (hread 32 (Or.inl (by decide))).symm⟩
    (by simpa only [inverseInvariant, hread 96 (Or.inl (by decide)), hread 2816 (Or.inr (by decide))] using hinv)
    ?_ ?_ env
  · rw [prepared, if_neg (by simp : ¬(4=8 ∧ pa=pa)), if_pos ⟨rfl,rfl⟩]; exact SquareFourInit.read_init_route _
  · rw [prepared, if_neg (by simp : ¬(4=8 ∧ pa=pa)), if_pos ⟨rfl,rfl⟩]; exact init_high_clear_four _

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
