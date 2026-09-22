import Challenge.Modexp.Submission.Proofs.Fast.M9MacChain
import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates

set_option warningAsError true

/-!
# M9: the MAC section in the shift-reduce routine's own vocabulary

`gasSteps_macChain` instantiated on the conversion routine's frame: `rest := k :: entrySlots um
n bsize esize ++ outer n bsize esize msize` — the counter, the seventeen riding slots and the
five-word outer frame (`Exp.outer`).  The riding hypotheses discharge definitionally:
`entrySlots`' words 1..7 are the `readWord um (1280 + 32 i)` limbs and its word 0 is the
`shiftEntry`/`entryPC` scratch.  `-N` base `Shift.NEG` (= 1280).  This is the statement that
replaces `Shift.gasSteps_macLoop` together with the old `run_macSetup`/`ShiftDispatchTrace.run_dispatch`
prefix: from `macSetupState` pc 2893 with `[q, k] ++ slots ++ outer` over `um` to pc 3171 with
`[carry, q, k] ++ slots ++ outer` over `Monpro.l1Step um q NEG n n`.

## Assumed from the tree (unchanged by the port)
* `Challenge.Modexp.Submission.Proofs.Fast.Exp.outer (n bsize esize msize : Nat) : List UInt256` (five words).
* `Challenge.Modexp.Submission.Proofs.Fast.Shift.NEG : Nat := 1280` (`Proofs/Fast/ShiftModel.lean`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.M9Mac

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro

/-- The conversion frame's riding `-N` slots: `entrySlots`' words 1..7 are exactly the
`readWord um (1280 + 32 i)` limbs `gasSteps_run` wants, by construction. -/
theorem entrySlots_ride (um : ByteArray) (n bsize esize msize k : Nat) :
    ∀ i : Nat, i < 7 →
      (UInt256.ofNat k :: Shift.entrySlots um n bsize esize ++
        Exp.outer n bsize esize msize)[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))) := by
  intro i hi
  interval_cases i <;>
    simp [Shift.entrySlots, Shift.rideSlots, Exp.outer]

/-- The scratch slot: `entrySlots`' word 0 is the section entry `shiftEntry n = entryPC n`
for the two widths the routine runs. -/
theorem entrySlots_scratch (um : ByteArray) (n bsize esize msize k : Nat)
    (hn : n = 4 ∨ n = 8) :
    (UInt256.ofNat k :: Shift.entrySlots um n bsize esize ++
      Exp.outer n bsize esize msize)[1]? =
    some (UInt256.ofNat (entryPC n)) := by
  rcases hn with rfl | rfl <;>
    simp [Shift.entrySlots, Shift.rideSlots, Shift.shiftEntry, entryPC, Exp.outer]

/-- The riding frame is twenty-three words: the counter, seventeen slots, five outer. -/
theorem rest_length (um : ByteArray) (n bsize esize msize k : Nat) :
    (UInt256.ofNat k :: Shift.entrySlots um n bsize esize ++
      Exp.outer n bsize esize msize).length = 23 := by
  simp [Shift.entrySlots, Shift.rideSlots, Exp.outer]

/-- The section on the conversion frame: from `macSetupState` (E6, pc 2893) with the
quotient guess above the counter, slots and outer frame over `um`, to the middle block at
pc 3171 with `[carry, q̂]` above the unchanged riding frame. -/
def gasSteps_macSection (n : Nat) (hn : n = 4 ∨ n = 8) (s : State) (um : ByteArray) (q : UInt256)
    (bsize esize msize k : Nat) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      { s with pc := UInt256.ofNat 2893,
               stack := q :: UInt256.ofNat k :: Shift.entrySlots um n bsize esize ++
                 Exp.outer n bsize esize msize,
               memory := um }
      { s with pc := UInt256.ofNat 3171,
               stack := (Monpro.l1Step um q Shift.NEG n n).carry :: q :: UInt256.ofNat k ::
                 Shift.entrySlots um n bsize esize ++ Exp.outer n bsize esize msize,
               memory := (Monpro.l1Step um q Shift.NEG n n).memory } :=
  gasSteps_macChain n hn s um q
    (UInt256.ofNat k :: Shift.entrySlots um n bsize esize ++ Exp.outer n bsize esize msize)
    (by rw [rest_length um n bsize esize msize k]; omega)
    (by rw [rest_length um n bsize esize msize k]; omega)
    (entrySlots_ride um n bsize esize msize k)
    (entrySlots_scratch um n bsize esize msize k hn)
    hrun hcode hfork hnp hact

end Challenge.Modexp.Submission.Proofs.Fast.M9Mac

#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_macSection
