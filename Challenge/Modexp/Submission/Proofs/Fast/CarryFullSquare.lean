import Challenge.Modexp.Submission.Proofs.Fast.SquareEntry
import Challenge.Modexp.Submission.Proofs.Fast.SquareRowsGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMidMemory SquareInit StagedOperand SquarePrepared

attribute [local irreducible] SquareInit.initMemory Monpro.mpZeroed SquarePrepared.before SquareRowsModel.rows

opaque gasSteps_square (s : State) (mem : ByteArray) (pa : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpafit : pa+256 ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2784 = UInt256.ofNat 256)
    (htl : MachineState.readWord mem 2880 = UInt256.ofNat 2336)
    (hml : MachineState.readWord mem 2848 = UInt256.ofNat 224)
    (hinv : inverseInvariant mem 8)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (Cios2Dispatch.dispatchState s mem pa pa dst ret rest)
      (mpCsubState s (SquareRowsModel.rows (prepared s mem pa pa 8) pa 8) dst ret rest) := by
  let initial := mpZeroed s (before mem pa pa 8) 8
  let start := SquareEntry.out s mem pa pa 8 dst ret rest
  have hlen : start.stack.length ≤ 1018 := by
    simp only [start, SquareEntry.out, CiosCached.outState, SquareEntry.args,
      List.length_append, List.length_cons, List.length_nil]
    omega
  have hg : UInt256.isTrue (SquareSelect.guard mem (UInt256.ofNat pa) (UInt256.ofNat pa)) :=
    (SquareEntry.guard_iff mem pa pa 8 (by decide) (by omega) (by omega) hs32).2 rfl
  have hr : MachineState.readWord initial 2720 = UInt256.ofNat 5040 := by
    rw [mpZeroed_readWord_outside s _ 8 2720 (Or.inr (by decide))]
    simp only [before, inputMemory, selected, if_pos (show 8=4 ∨ 8=8 from Or.inr rfl),
      or_true, ite_true, SquareSelect.selectedMemory, if_pos hg]
    rw [read_stage_outside _ _ _ _ (Or.inr (by decide)), read_storeWord]
  have hheader := SquareEntry.gasSteps_header s mem pa pa 8 dst ret rest hcap hact (Or.inr rfl)
    hpa hpafit hpa hpafit hcds hs32 hml env
  have hroute := SquareEntry.gasSteps_route s initial (UInt256.ofNat 5040) start.stack
    (by omega) hact hr SquareParts.jump_init env
  have hinit := gasSteps_init s initial start.stack hlen hact env.code env.forkEq env.running env.noPrecompile
    (by rfl)
  have hentry : Challenge.EvmProof.GasSteps (Cios2Dispatch.dispatchState s mem pa pa dst ret rest)
      (SquareRowsGas.state s (prepared s mem pa pa 8) pa 0
        (MachineState.readWord mem 2880) (MachineState.readWord mem 2816) (MachineState.readWord mem 224)
        (UInt256.ofNat (pa+224)) (MachineState.readWord mem 96) (MachineState.readWord mem 64)
        (MachineState.readWord mem 32) dst ret rest) := by
    have hpadd : pa+32*8-32 = pa+224 := by omega
    simpa only [SquareRowsGas.state, SquareRowsGas.tag, prepared, if_pos (show 8=8 ∧ pa=pa from ⟨rfl,rfl⟩),
      initial, start, SquareEntry.out, CiosCached.outState, SquareEntry.args, Nat.reduceLT,
      ite_true, true_and, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, hpadd,
      ptrAt_zero, show l2Target 8 = UInt256.ofNat 4518 by decide, SquareDiagonal.base, stateAt, List.cons_append, List.nil_append] using
      hheader.trans (hroute.trans hinit)
  have hread (addr : Nat) (hd : addr+32 ≤ 2048 ∨ 2752 ≤ addr) := read_prepared_outside s mem pa pa 8 addr (by decide) hd
  refine hentry.trans <| SquareRowsGas.gasSteps_rows s (prepared s mem pa pa 8) pa
    (MachineState.readWord mem 2880) (MachineState.readWord mem 2816) (MachineState.readWord mem 224)
    (UInt256.ofNat (pa+224)) (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) dst ret rest hcap hact hpa hpafit
    ⟨htl, (hread 2816 (Or.inr (by decide))).symm, (hread 224 (Or.inl (by decide))).symm⟩
    ⟨(hread 96 (Or.inl (by decide))).symm, (hread 64 (Or.inl (by decide))).symm,
      (hread 32 (Or.inl (by decide))).symm⟩
    (by simpa only [inverseInvariant, hread 224 (Or.inl (by decide)), hread 2816 (Or.inr (by decide))] using hinv)
    ?_ ?_ env
  · rw [prepared, if_pos ⟨rfl,rfl⟩]; exact read_init_route _
  · rw [prepared, if_pos ⟨rfl,rfl⟩]; exact init_high_clear _

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
