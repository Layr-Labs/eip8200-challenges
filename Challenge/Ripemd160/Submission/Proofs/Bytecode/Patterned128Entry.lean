import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The appended 128-byte guard and its bridge into the patterned scan. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

abbrev Located := DirectGuard.Located

private def sound (path : List Located) {s t : State}
    (h : DirectGuard.run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

/- The failure path stops at JUMPI.  It must not include the success suffix:
   a taken JUMPI changes the PC to 368, so the next located instruction would
   fail the PC check. -/
private def guardCheckPath : List Located :=
  [DirectGuard.opAt 4116 .JUMPDEST,
   DirectGuard.opAt 4117 .CALLDATASIZE,
   DirectGuard.pushAt 4118 1 128,
   DirectGuard.opAt 4119 .XOR,
   -- ponytail: retain this one-gas pad until earlier guard offsets need relocation.
   DirectGuard.opAt 4120 .JUMPDEST,
   DirectGuard.pushAt 4121 0 0,
   DirectGuard.opAt 4122 .CALLDATALOAD,
   DirectGuard.pushAt 4123 0 0,
   DirectGuard.opAt 4124 .BYTE,
   DirectGuard.pushAt 4125 1 7,
   DirectGuard.opAt 4126 .XOR,
   DirectGuard.opAt 4127 .OR,
   DirectGuard.pushAt 4128 2 368,
   DirectGuard.opAt 4129 .JUMPI]

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4130 0 0,
   DirectGuard.pushAt 4131 1 101,
   DirectGuard.opAt 4132 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 61 .JUMPDEST, DirectGuard.opAt 62 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 101
    stack := [UInt256.ofNat 0] }

private theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (DirectGuard.firstByte input) := by
  simpa [DirectGuard.firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

private theorem wordNat_zero (a : UInt256) : a.toNat = 0 ↔ a = 0 := by
  constructor
  · exact fun h => Word.word_ext h
  · intro h
    rw [h]
    rfl

private theorem word_eq_iff (a b : UInt256) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt256.toNat, Word.word_ext⟩

private theorem guard_condition_zero (size first : Nat)
    (hs : size < 2 ^ 256) (hb : first < 2 ^ 256) :
    (UInt256.lor (UInt256.xor (UInt256.ofNat 7) (UInt256.ofNat first))
      (UInt256.xor (UInt256.ofNat 128) (UInt256.ofNat size))).toNat = 0 ↔
      first = 7 ∧ size = 128 := by
  rw [wordNat_zero, KnownInputLogic.wordOr_eq_zero_iff,
    KnownInputLogic.wordXor_eq_zero_iff, KnownInputLogic.wordXor_eq_zero_iff,
    word_eq_iff, word_eq_iff]
  simp only [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hb]
  norm_num only [eq_comm]

private theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 368 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 205 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 61 (by rfl)

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (DirectGuard.fallbackState input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hbyteLt : DirectGuard.firstByte input < 2 ^ 256 :=
    Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt (by norm_num)
  have hcond :
      (UInt256.lor (UInt256.xor (UInt256.ofNat 7)
          (UInt256.ofNat (DirectGuard.firstByte input)))
        (UInt256.xor (UInt256.ofNat 128)
          (UInt256.ofNat input.size))).toNat ≠ 0 := by
    simp only [Ne, guard_condition_zero input.size (DirectGuard.firstByte input) hlt hbyteLt]
    tauto
  simp (config := { decide := true })
    [guardCheckPath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     DirectGuard.guardEntry, DirectGuard.fallbackState, DirectGuard.atPC,
     hcond, guard_fallback_dest, UInt256.isTrue, List.exchange,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, firstByte_eq_byteAt]

private theorem run_guard_match_helper (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run (guardCheckPath ++ guardMatchSuffix)
      (DirectGuard.guardEntry input) = some (guardJumpState input) := by
  have esize : UInt256.xor (UInt256.ofNat 128) (UInt256.ofNat input.size) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 (by rw [hsize])
  have ebyte' :
      UInt256.xor (UInt256.ofNat 7)
          (UInt256.ofNat (DirectGuard.firstByte input)) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 (by rw [hbyte])
  simp (config := { decide := true })
    [guardCheckPath, guardMatchSuffix, DirectGuard.opAt, DirectGuard.pushAt,
     DirectGuard.wfOp, DirectGuard.guardEntry, guardJumpState,
     DirectGuard.atPC, esize, ebyte', guard_match_dest, UInt256.isTrue,
     UInt256.lor, UInt256.isZero, List.exchange,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, firstByte_eq_byteAt]

private theorem run_guard_match_tail (input : ByteArray) :
    DirectGuard.run guardMatchTail (guardJumpState input) =
      some (PatternedScan.patternedEntry input) := by
  simp (config := { decide := true })
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     guardJumpState, DirectGuard.guardEntry, PatternedScan.patternedEntry,
     DirectGuard.atPC, PatternedScan.atPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  sound guardCheckPath (run_guard_fail input hfit hbad)

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match_helper input hfit hsize hbyte)).trans
    (sound guardMatchTail (run_guard_match_tail input))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize hbyte))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
