import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstModel
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareScratchAgreement

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult CarryRowModel CarryScratchAgreement
open R8ZeroFirstRow TnCacheMemory TnCacheSquareModel

/-! The first square row agrees with the machine-carry model for arbitrary
incoming scratch.  This is an agreement theorem, not an exact-memory theorem. -/
theorem firstRow_agree (s : State) (mem : ByteArray) :
    CarryScratchAgreement.Agree
      (TnCacheMemory.lift (TnM128SquareFirstModel.first mem).memory
        (TnM128SquareFirstModel.first mem).tn)
      (SquareResult.sqRowCarry (Monpro.mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) := by
  let q := sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)
  have hzero := CarryScratchAgreement.write_same
    (R8ZeroFirstRow.firstMemory_bridge s mem)
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 0).toNat 32) 2080
  have hzero' :
      CarryScratchAgreement.Agree
        (TnCacheMemory.lift (R8ZeroFirstRow.firstMemory mem) (UInt256.ofNat 0))
        (TnCacheMemory.lift
          (midMem1 q.memory q.carry) (UInt256.ofNat 0)) := by
    simpa only [TnCacheMemory.lift] using hzero
  have hleft :
      TnCacheMemory.lift (R8ZeroFirstRow.firstMemory mem) (UInt256.ofNat 0) =
        TnCacheMemory.lift (firstProduct mem).memory (UInt256.ofNat 0) := by
    change
      TnCacheMemory.lift
        (TnCacheMemory.lift (firstProduct mem).memory (firstProduct mem).carry)
        (UInt256.ofNat 0) =
        TnCacheMemory.lift (firstProduct mem).memory (UInt256.ofNat 0)
    exact TnCacheMemory.lift_overwrite _ _ _
  have hright :
      TnCacheMemory.lift (midMem1 q.memory q.carry) (UInt256.ofNat 0) =
        TnCacheMemory.lift q.memory (UInt256.ofNat 0) := by
    change
      TnCacheMemory.lift
        (TnCacheMemory.lift q.memory
          (MachineState.readWord q.memory 2080 + q.carry))
        (UInt256.ofNat 0) =
        TnCacheMemory.lift q.memory (UInt256.ofNat 0)
    exact TnCacheMemory.lift_overwrite _ _ _
  have hproduct_lift :
      CarryScratchAgreement.Agree
        (TnCacheMemory.lift (firstProduct mem).memory (UInt256.ofNat 0))
        (TnCacheMemory.lift q.memory (UInt256.ofNat 0)) := by
    rw [hleft, hright] at hzero'
    exact hzero'
  have hqeq : q = TnCacheSquareModel.liftMac q (UInt256.ofNat 0) := by
    have h := TnCacheSquareModel.squareL1_lift
      (mpZeroed s mem 8) (UInt256.ofNat 0) 8 0 (UInt256.ofNat 0) (by decide)
    rw [TnCacheInitialMemory.lift_zeroed s mem 8] at h
    exact h
  have hqmem : TnCacheMemory.lift q.memory (UInt256.ofNat 0) = q.memory := by
    have h := congrArg (fun z : MacState => z.memory) hqeq
    simpa only [TnCacheSquareModel.liftMac] using h.symm
  have hq : CarryScratchAgreement.Agree
      (TnCacheMemory.lift q.memory (UInt256.ofNat 0)) q.memory := by
    rw [hqmem]
    exact CarryScratchAgreement.refl q.memory
  have hproduct :
      CarryScratchAgreement.Agree
        (TnCacheMemory.lift (firstProduct mem).memory (UInt256.ofNat 0)) q.memory :=
    CarryScratchAgreement.trans hproduct_lift hq
  have hcarry :
      (TnCacheSquareModel.liftMac (firstProduct mem) (UInt256.ofNat 0)).carry = q.carry :=
    (R8ZeroFirstRow.firstProduct_bridge s mem).2
  have hrow := SquareResult.rowFrom_agree
    (TnCacheSquareModel.liftMac (firstProduct mem) (UInt256.ofNat 0)) q hproduct hcarry
    8 (by decide)
  have hself := SquareResult.rowFrom_agree q q
    (CarryScratchAgreement.refl q.memory) rfl 8 (by decide)
  have hfirst :
      CarryScratchAgreement.Agree
        (rowFromCarry (TnCacheSquareModel.liftMac (firstProduct mem) (UInt256.ofNat 0)) 8)
        (rowFromCarry q 8) :=
    CarryScratchAgreement.trans hrow (CarryScratchAgreement.symm hself)
  change CarryScratchAgreement.Agree
    (TnCacheMemory.lift
      (TnCacheSquareModel.fromL1 (firstProduct mem) (UInt256.ofNat 0) 8).memory
      (TnCacheSquareModel.fromL1 (firstProduct mem) (UInt256.ofNat 0) 8).tn)
    (rowFromCarry q 8)
  rw [← TnCacheSquareModel.from_lift (firstProduct mem) (UInt256.ofNat 0) 8
    (by decide) (by decide)]
  exact hfirst

#print axioms firstRow_agree

end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareScratchAgreement
