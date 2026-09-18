import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandCarrySnapshot
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult

/-- The eight rows of an eight-limb multiply, from the row-0 head (`hd = 3481`, the
cell holding the zero-filled scratch word the staging reload E15 installed) to the final
subtraction, whose memory is exactly the specification `rowsCarry` thanks to the exit
flush (E14). -/
opaque gasSteps_rowsEight (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hpbS : pb + 32 * 8 ≤ 2048 ∨ 2112 ≤ pb)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 8) pb 8 0 (UInt256.ofNat 3481) (l1Base 8)
        (MachineState.readWord (mpZeroed s mem 8) 2080) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) := by
  have hsz := hsnapshot.zeroed_stage s (by decide) hpaFit
  have hminvz := inverse_mpZeroed s mem 8 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s 8 (by decide)
  have hpaS : pa + 32 * 8 ≤ 2048 ∨ 2112 ≤ pa := by
    rcases hpaFit with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  rw [← rowsS_flush (mpZeroed s mem 8) pa pb 8 (size_mpZeroed s mem 8) hpaS hpbS
    (by decide) (by decide) 8 (by decide)]
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s
      (rowsS (mpZeroed s mem 8) (MachineState.readWord (mpZeroed s mem 8) 2080) pa pb 8 i).memory
      pb 8 i (UInt256.ofNat 3481) (l1Base 8)
      (rowsS (mpZeroed s mem 8) (MachineState.readWord (mpZeroed s mem 8) 2080) pa pb 8 i).slot
      inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) 7 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowEightNext L s
      (rowsS (mpZeroed s mem 8) (MachineState.readWord (mpZeroed s mem 8) 2080) pa pb 8 i).memory
      pa pb i
      (rowsS (mpZeroed s mem 8) (MachineState.readWord (mpZeroed s mem 8) 2080) pa pb 8 i).slot
      tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by omega)
      hpaFit hpb hpbFit
      (inverse_rowsS (mpZeroed s mem 8) _ pa pb 8 i (by decide) hminvz)
      (readonlyCache_rowsS hcz (by decide) _ pa pb i)
      (extraCache_rowsS hez _ pa pb 8 i (by decide)) hAend
      (hsz.rowsS_stage _ pb i (by decide) hpaFit)
  · exact
      gasSteps_rowEightLast L s
        (rowsS (mpZeroed s mem 8) (MachineState.readWord (mpZeroed s mem 8) 2080) pa pb 8 7).memory
        pa pb 7
        (rowsS (mpZeroed s mem 8) (MachineState.readWord (mpZeroed s mem 8) 2080) pa pb 8 7).slot
        tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide)
        hpaFit hpb hpbFit
        (inverse_rowsS (mpZeroed s mem 8) _ pa pb 8 7 (by decide) hminvz)
        (readonlyCache_rowsS hcz (by decide) _ pa pb 7)
        (extraCache_rowsS hez _ pa pb 8 7 (by decide)) hAend
        (hsz.rowsS_stage _ pb 7 (by decide) hpaFit)

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
