import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# Appended 128-byte patterned redirect

Two PUSH2 immediates in the promoted leader now target this suffix:
the original 56/63/120 miss lands at pc 5262, and a successful short
scan with size < 129 lands at pc 5284. Existing PCs are unchanged.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPattern128Hop

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan DirectGuard

abbrev Located := DirectGuard.Located

def missEntry (input : ByteArray) : State := stS input 5262 []

def digest128 : UInt256 :=
  233347948783734465632298330963582576039387513209

def missPath : List Located :=
  [DirectGuard.opAt 4168 .JUMPDEST,
   DirectGuard.opAt 4169 .CALLDATASIZE,
   DirectGuard.pushAt 4170 1 128,
   DirectGuard.opAt 4171 .EQ,
   DirectGuard.opAt 4172 .ISZERO,
   DirectGuard.pushAt 4173 0 0,
   DirectGuard.opAt 4174 .CALLDATALOAD,
   DirectGuard.pushAt 4175 0 0,
   DirectGuard.opAt 4176 .BYTE,
   DirectGuard.pushAt 4177 1 7,
   DirectGuard.opAt 4178 .XOR,
   DirectGuard.opAt 4179 .OR,
   DirectGuard.pushAt 4180 2 363,
   DirectGuard.opAt 4181 .JUMPI]

def missScanTail : List Located :=
  [DirectGuard.pushAt 4182 0 0, DirectGuard.pushAt 4183 1 101, DirectGuard.opAt 4184 .JUMP]

def selHopTaken : List Located :=
  [DirectGuard.opAt 4185 .JUMPDEST,
   DirectGuard.opAt 4186 .CALLDATASIZE,
   DirectGuard.pushAt 4187 1 128,
   DirectGuard.opAt 4188 .EQ,
   DirectGuard.pushAt 4189 2 5297,
   DirectGuard.opAt 4190 .JUMPI]

def selHopPath : List Located :=
  [DirectGuard.opAt 4185 .JUMPDEST,
   DirectGuard.opAt 4186 .CALLDATASIZE,
   DirectGuard.pushAt 4187 1 128,
   DirectGuard.opAt 4188 .EQ,
   DirectGuard.pushAt 4189 2 5297,
   DirectGuard.opAt 4190 .JUMPI,
   DirectGuard.pushAt 4191 2 5200,
   DirectGuard.opAt 4192 .JUMP]

def ret128Path : List Located :=
  [DirectGuard.opAt 4193 .JUMPDEST,
   DirectGuard.pushAt 4194 20 digest128,
   DirectGuard.pushAt 4195 0 0,
   DirectGuard.opAt 4196 .MSTORE]

def ret128Finish : List Located :=
  [DirectGuard.pushAt 4198 0 0, DirectGuard.opAt 4199 .RETURN]

private theorem dest363 :
    Decode.isValidJumpDest submissionBytecode 363 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem dest101 :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private theorem dest5200 :
    Decode.isValidJumpDest submissionBytecode 5200 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4150 (by rfl)

private theorem dest5297 :
    Decode.isValidJumpDest submissionBytecode 5297 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4193 (by rfl)

private theorem dest5262 :
    Decode.isValidJumpDest submissionBytecode 5262 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4168 (by rfl)

private theorem dest5284 :
    Decode.isValidJumpDest submissionBytecode 5284 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4185 (by rfl)

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

private theorem eq128_zero (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 128) :
    UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size) = 0 :=
  DirectGuard.size_eq_zero input 128 (Nat.lt_trans hfit (by norm_num)) (by norm_num) hne

private theorem eq128_one (input : ByteArray) (hsize : input.size = 128) :
    UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size) = 1 := by
  rw [hsize]
  decide

private theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (DirectGuard.firstByte input) := by
  simpa [DirectGuard.firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

/-- Reject flag at the miss redirect: 1 iff the input is not 128-byte with first byte 7. -/
def missReject (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (UInt256.ofNat 7)
      (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)))
    (UInt256.isZero (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size)))

theorem missReject_generic (input : ByteArray) (hfit : CalldataFits input)
    (hgen : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    UInt256.isTrue (missReject input) := by
  intro hz
  have h0 : missReject input = 0 :=
    Challenge.EvmProof.Word.word_ext (by simpa using hz)
  unfold missReject at h0
  obtain ⟨hxor, hsz⟩ := (KnownInputLogic.wordOr_eq_zero_iff _ _).1 h0
  have hbyte := firstByte_eq_byteAt input
  have hsize128 : input.size = 128 := by
    have heq : UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size) ≠ 0 := by
      intro hz'
      rw [hz'] at hsz
      exact (by decide : (UInt256.isZero (0 : UInt256)) ≠ 0) hsz
    have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
    by_contra hne
    exact heq (DirectGuard.size_eq_zero input 128 hlt (by norm_num) hne)
  have hbyte7 : DirectGuard.firstByte input = 7 := by
    rw [hbyte] at hxor
    have hx := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hxor
    have hlt : DirectGuard.firstByte input < 2 ^ 256 := by
      unfold DirectGuard.firstByte
      exact Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt (by norm_num)
    have hn := congrArg UInt256.toNat hx
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt] at hn
    exact hn.symm
  rcases hgen with h | h
  · exact h hsize128
  · exact h hbyte7

theorem missReject_scan (input : ByteArray)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    missReject input = 0 := by
  unfold missReject
  rw [eq128_one input hsize, firstByte_eq_byteAt, hbyte]
  decide

private theorem pc4168 : Artifact.submissionArtifact.instructionPC 4168 = 5262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4169 : Artifact.submissionArtifact.instructionPC 4169 = 5263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4170 : Artifact.submissionArtifact.instructionPC 4170 = 5264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4171 : Artifact.submissionArtifact.instructionPC 4171 = 5266 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4172 : Artifact.submissionArtifact.instructionPC 4172 = 5267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4173 : Artifact.submissionArtifact.instructionPC 4173 = 5268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4174 : Artifact.submissionArtifact.instructionPC 4174 = 5269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4175 : Artifact.submissionArtifact.instructionPC 4175 = 5270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4176 : Artifact.submissionArtifact.instructionPC 4176 = 5271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4177 : Artifact.submissionArtifact.instructionPC 4177 = 5272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4178 : Artifact.submissionArtifact.instructionPC 4178 = 5274 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4179 : Artifact.submissionArtifact.instructionPC 4179 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4180 : Artifact.submissionArtifact.instructionPC 4180 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4181 : Artifact.submissionArtifact.instructionPC 4181 = 5279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4182 : Artifact.submissionArtifact.instructionPC 4182 = 5280 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4183 : Artifact.submissionArtifact.instructionPC 4183 = 5281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4184 : Artifact.submissionArtifact.instructionPC 4184 = 5283 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4185 : Artifact.submissionArtifact.instructionPC 4185 = 5284 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4186 : Artifact.submissionArtifact.instructionPC 4186 = 5285 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4187 : Artifact.submissionArtifact.instructionPC 4187 = 5286 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4188 : Artifact.submissionArtifact.instructionPC 4188 = 5288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4189 : Artifact.submissionArtifact.instructionPC 4189 = 5289 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4190 : Artifact.submissionArtifact.instructionPC 4190 = 5292 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4191 : Artifact.submissionArtifact.instructionPC 4191 = 5293 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4192 : Artifact.submissionArtifact.instructionPC 4192 = 5296 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4193 : Artifact.submissionArtifact.instructionPC 4193 = 5297 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4194 : Artifact.submissionArtifact.instructionPC 4194 = 5298 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4195 : Artifact.submissionArtifact.instructionPC 4195 = 5319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4196 : Artifact.submissionArtifact.instructionPC 4196 = 5320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4197 : Artifact.submissionArtifact.instructionPC 4197 = 5321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4198 : Artifact.submissionArtifact.instructionPC 4198 = 5322 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem pc4199 : Artifact.submissionArtifact.instructionPC 4199 = 5323 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_miss_generic (input : ByteArray) (hfit : CalldataFits input)
    (hgen : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run missPath (missEntry input) =
      some (DirectGuard.fallbackState input) := by
  have ht := missReject_generic input hfit hgen
  have h :
      DirectGuard.run missPath (stS input 5262 []) =
        some (stS input 363 []) := by
    simp (config := { maxSteps := 400000 })
      [missPath, missReject, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
       missEntry, DirectGuard.fallbackState, DirectGuard.atPC, stS,
       Challenge.EvmProof.Stepper.runLocatedBlock,
       Challenge.EvmProof.Stepper.runLocated,
       Challenge.EvmProof.Stepper.runInstr,
       Challenge.EvmProof.Word.literal_eq_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod,
       Challenge.EvmProof.Word.ofNat_add_mod,
       Challenge.EvmProof.Word.word_toNat_ofNat,
       pc4168, pc4169, pc4170, pc4171, pc4172, pc4173, pc4174, pc4175,
       pc4176, pc4177, pc4178, pc4179, pc4180, pc4181, dest363]
    rw [show (((UInt256.ofNat 7).xor
          ((UInt256.ofNat 0).byteAt (MachineState.readWord input 0))).lor
          ((UInt256.ofNat 128).eq (UInt256.ofNat input.size)).isZero) =
        missReject input from rfl, if_pos ht]
  simpa [missEntry, DirectGuard.fallbackState, DirectGuard.atPC, stS] using h

def gasSteps_miss_generic (input : ByteArray) (hfit : CalldataFits input)
    (hgen : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (missEntry input) (DirectGuard.fallbackState input) :=
  sound missPath (run_miss_generic input hfit hgen)

theorem run_sel_not128 (input : ByteArray) (rest : List UInt256)
    (hlen : rest.length < 1020) (hsize : input.size ≠ 128)
    (hfit : CalldataFits input) :
    DirectGuard.run selHopPath (stS input 5284 rest) =
      some (stS input 5200 rest) := by
  have hf : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size)) := by
    rw [eq128_zero input hfit hsize]
    decide
  have hcap : rest.length < 1024 := Nat.lt_trans hlen (by decide)
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hfalse : ¬ (UInt256.ofNat 0).isTrue := by decide
  simp (config := { maxSteps := 400000 })
    [selHopPath, selHopTaken, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp, stS,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     pc4185, pc4186, pc4187, pc4188, pc4189, pc4190, pc4191, pc4192,
     dest5200, dest5297, hf, hfalse, hcap, hcap1, hcap2, hcap3, eq128_zero input hfit hsize]

def gasSteps_sel_not128 (input : ByteArray) (rest : List UInt256)
    (hlen : rest.length < 1020) (hsize : input.size ≠ 128)
    (hfit : CalldataFits input) :
    GasSteps (stS input 5284 rest) (stS input 5200 rest) :=
  sound selHopPath (run_sel_not128 input rest hlen hsize hfit)

theorem run_miss_scan (input : ByteArray)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run (missPath ++ missScanTail) (missEntry input) =
      some (stS input 101 [0]) := by
  have hz := missReject_scan input hsize hbyte
  have hf : ¬ UInt256.isTrue (missReject input) := by
    rw [hz]; decide
  have hcond :
      (((UInt256.ofNat 7).xor
          ((UInt256.ofNat 0).byteAt (MachineState.readWord input 0))).lor
          ((UInt256.ofNat 128).eq (UInt256.ofNat 128)).isZero) =
        missReject input := by
    unfold missReject
    rw [hsize]
  simp (config := { maxSteps := 800000 })
    [missPath, missScanTail, missReject, missEntry, DirectGuard.opAt, DirectGuard.pushAt,
     DirectGuard.wfOp, stS, hsize, hz,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     pc4168, pc4169, pc4170, pc4171, pc4172, pc4173, pc4174, pc4175,
     pc4176, pc4177, pc4178, pc4179, pc4180, pc4181, pc4182, pc4183, pc4184,
     dest363, dest101, eq128_one input hsize]
  rw [hcond, if_neg hf]
  all_goals
    simp [dest101, stS,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_miss_scan (input : ByteArray)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (missEntry input) (stS input 101 [0]) :=
  sound (missPath ++ missScanTail) (run_miss_scan input hsize hbyte)

theorem run_sel_128 (input : ByteArray) (rest : List UInt256)
    (hlen : rest.length < 1020) (hsize : input.size = 128) :
    DirectGuard.run selHopTaken (stS input 5284 rest) =
      some (stS input 5297 rest) := by
  have ht : UInt256.isTrue (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size)) := by
    rw [eq128_one input hsize]; decide
  have hcap : rest.length < 1024 := Nat.lt_trans hlen (by decide)
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have htrue : (UInt256.ofNat 1).isTrue := by decide
  have hone : (UInt256.ofNat 128).eq (UInt256.ofNat 128) = 1 := by decide
  simp (config := { maxSteps := 400000 })
    [selHopTaken, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp, stS,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     pc4185, pc4186, pc4187, pc4188, pc4189, pc4190, dest5297,
     ht, htrue, hone, hsize, hcap, hcap1, hcap2, hcap3, eq128_one input hsize]

def gasSteps_sel_128 (input : ByteArray) (rest : List UInt256)
    (hlen : rest.length < 1020) (hsize : input.size = 128) :
    GasSteps (stS input 5284 rest) (stS input 5297 rest) :=
  sound selHopTaken (run_sel_128 input rest hlen hsize)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPattern128Hop
