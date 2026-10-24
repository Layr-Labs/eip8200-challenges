import Challenge.Modexp.Submission.Proofs.CycleGlobal.Setup
import Challenge.Modexp.Submission.Proofs.Fast.Exp
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast.SetupFacts
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Exp
/-- Nothing the setup block writes lands between `0x0400` and `0x1000`. -/
theorem readWord_setupMem_mid (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 256)
    (hlo : 256 ≤ target) (hhi : target + 32 ≤ 1024) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_256 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  -- `setupMem` does not store the R1 seed, so this read-through peels one
  -- `mstoreAt` fewer before the two `writeBytes`.
  rw [Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

/-- `ACC`, `BASE` and the `ONE` slot are all zero when the setup hands over. -/
theorem fastSetup_zero_block (input : ByteArray) (hpath : Setup.FastPath input)
    (ptr : Nat) (hlo : 256 ≤ ptr) (hhi : ptr + 32 * Setup.limbs input ≤ 1024) :
    Model.FastRepresents (Setup.fastSetupMemory input) ptr (Setup.limbs input) 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_mid input (Setup.lowLimb input) (ptr + 32 * j) hpath.2.1.2.2
      (by omega) (by omega),
    toNat_ofNat_self (by norm_num)]

/-- Nothing the setup block writes lands between `0x1020` and the variables. -/
theorem readWord_setupMem_high (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 256)
    (hlo : 2048 ≤ target) (hhi : target + 32 ≤ 2656) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_256 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  -- There is no seed store, so the region starts at 0x1000 rather than
  -- 0x1020 and the `Or.inr` peel that stepped over it is no longer needed.
  rw [Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

/-- The CIOS `t` block is still zero when the setup hands over, which is what
lets `CSUB` compute `radix ^ n - m` from `t[n] = 1` alone. -/
theorem fastSetup_tblock_zero (input : ByteArray) (hpath : Setup.FastPath input)
    (hn32 : Setup.limbs input ≤ 8) :
    Model.FastRepresents (Setup.fastSetupMemory input) 2112 (Setup.limbs input) 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_high input (Setup.lowLimb input) (2112 + 32 * j) hpath.2.1.2.2
      (by omega) (by omega),
    toNat_ofNat_self (by norm_num)]

/-! ## The hand-over state, field by field -/

theorem fastSetup_code (input : ByteArray) :
    (Setup.fastSetupState input).executionEnv.code =
      CycleSubmission.Artifact.bytecode := rfl

theorem fastSetup_fork (input : ByteArray) :
    (Setup.fastSetupState input).fork = .Osaka := rfl

theorem fastSetup_halt (input : ByteArray) :
    (Setup.fastSetupState input).halt = .Running := rfl

theorem fastSetup_calldata (input : ByteArray) :
    (Setup.fastSetupState input).executionEnv.calldata = input := rfl

theorem fastSetup_callStack (input : ByteArray) :
    (Setup.fastSetupState input).callStack = [] := rfl

theorem fastSetup_notPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig
      (Setup.fastSetupState input).executionEnv.precompileConfig
      (Setup.fastSetupState input).executionEnv.fork
      (Setup.fastSetupState input).executionEnv.codeAddr = false :=
  Challenge.Modexp.deployAddress_not_precompile

/-- The setup block ends at the dispatcher (pc 3381) with the plain outer frame,
instead of at the Montgomery-form conversion call.  `Shift.dispState` is definitionally this
state; it cannot be named here because `ShiftStates` sits above this module. -/
theorem fastSetup_entry_eq (input : ByteArray) :
    Setup.fastSetupState input =
      retTo (Setup.fastSetupState input) (Setup.fastSetupMemory input) (UInt256.ofNat 2390)
        (outer (Setup.limbs input) (Challenge.Modexp.baseSize input)
          (Challenge.Modexp.exponentSize input) (Challenge.Modexp.modulusSize input)) := rfl


end CycleSubmission.Global.Fast.SetupFacts
