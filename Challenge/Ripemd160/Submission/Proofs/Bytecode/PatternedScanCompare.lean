import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedCompare
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar
@[simp] private theorem signedPC127 : Artifact.submissionArtifact.instructionPC 127 = 207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC128 : Artifact.submissionArtifact.instructionPC 128 = 208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC129 : Artifact.submissionArtifact.instructionPC 129 = 209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC130 : Artifact.submissionArtifact.instructionPC 130 = 210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC131 : Artifact.submissionArtifact.instructionPC 131 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC132 : Artifact.submissionArtifact.instructionPC 132 = 212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC133 : Artifact.submissionArtifact.instructionPC 133 = 213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC134 : Artifact.submissionArtifact.instructionPC 134 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC135 : Artifact.submissionArtifact.instructionPC 135 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC136 : Artifact.submissionArtifact.instructionPC 136 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC137 : Artifact.submissionArtifact.instructionPC 137 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC139 : Artifact.submissionArtifact.instructionPC 139 = 220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC140 : Artifact.submissionArtifact.instructionPC 140 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC141 : Artifact.submissionArtifact.instructionPC 141 = 223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC142 : Artifact.submissionArtifact.instructionPC 142 = 224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC143 : Artifact.submissionArtifact.instructionPC 143 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC144 : Artifact.submissionArtifact.instructionPC 144 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC145 : Artifact.submissionArtifact.instructionPC 145 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC146 : Artifact.submissionArtifact.instructionPC 146 = 228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC147 : Artifact.submissionArtifact.instructionPC 147 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC148 : Artifact.submissionArtifact.instructionPC 148 = 230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC149 : Artifact.submissionArtifact.instructionPC 149 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC150 : Artifact.submissionArtifact.instructionPC 150 = 233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC151 : Artifact.submissionArtifact.instructionPC 151 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC152 : Artifact.submissionArtifact.instructionPC 152 = 236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC153 : Artifact.submissionArtifact.instructionPC 153 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC154 : Artifact.submissionArtifact.instructionPC 154 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem signedPC155 : Artifact.submissionArtifact.instructionPC 155 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def comparePrefix : List Located := [opAt 127 .JUMPDEST,
    opAt 128 (.Dup ⟨3, by decide⟩),
    opAt 129 .CALLDATALOAD,
    opAt 130 .XOR,
    opAt 131 (.Dup ⟨3, by decide⟩),
    opAt 132 .CALLDATASIZE,
    opAt 133 .SUB,
    pushAt 134 1 32,
    opAt 135 .SUB,
    pushAt 136 0 0,
    opAt 137 (.Dup ⟨1, by decide⟩)]
private def compareSuffix : List Located := [opAt 139 .MUL,
    pushAt 140 1 3,
    opAt 141 .SHL,
    opAt 142 .SHR,
    opAt 143 (.Dup ⟨4, by decide⟩),
    opAt 144 .OR,
    opAt 145 (.Swap ⟨3, by decide⟩),
    opAt 146 .POP,
    opAt 147 .POP,
    pushAt 148 1 160,
    opAt 149 .ADD,
    pushAt 150 1 255,
    opAt 151 .AND,
    opAt 152 (.Swap ⟨0, by decide⟩),
    pushAt 153 1 32,
    opAt 154 .ADD,
    opAt 155 (.Swap ⟨0, by decide⟩)]
private def blockSound (path : List Located) {s t : State}
    (h : Stepper.runLocatedBlock (artifact := Artifact.submissionArtifact) (fork := .Osaka) path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) : GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_compare_fold (input : ByteArray) (W S sv ov acc : UInt256) :
    GasSteps (stS input 207 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 241 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight (UInt256.xor (MachineState.readWord input ov.toNat) W)
          (maskShift input ov)), P7, M, m7, P, m8]) := by
  let diff := UInt256.xor (MachineState.readWord input ov.toNat) W
  let missing := UInt256.ofNat 32 - (UInt256.ofNat input.size - ov)
  let rest := [diff, S, sv, ov, acc, P7, M, m7, P, m8]
  let before := stS input 219 (missing :: 0 :: missing :: rest)
  let after := stS input 220 (UInt256.sgt missing 0 :: missing :: rest)
  have hpre : Stepper.runLocatedBlock (artifact := Artifact.submissionArtifact) (fork := .Osaka) comparePrefix
      (stS input 207 [W, S, sv, ov, acc, P7, M, m7, P, m8]) = some before := by
    simp (config := { maxSteps := 400000 }) [comparePrefix, opAt, pushAt, wfOp, before, rest,
      diff, missing, stS, initialState, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
      Word.word_toNat_ofNat]
    rfl
  have hd := Artifact.submissionArtifact.decodeAt_op_index 138 .SGT (by rfl) (by decide) trivial
  have hp : before.pc.toNat = Artifact.submissionArtifact.instructionPC 138 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hop : before.decodedOp = some .SGT := Artifact.submissionArtifact.state_decodedOp_of
    before 138 (by rfl) hp .SGT none hd (by rfl)
  have hm : GasSteps before after := by
    simpa [before, after, rest, stS, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using
      (SignedCompare.step hop (by rfl)
        (by simp [before, rest, stS, initialState, Operation.pushArity, Operation.popArity])
        (by rfl) deployAddress_not_precompile)
  have hpost : Stepper.runLocatedBlock (artifact := Artifact.submissionArtifact) (fork := .Osaka) compareSuffix after =
      some (stS input 241 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight (UInt256.xor (MachineState.readWord input ov.toNat) W)
          (maskShift input ov)), P7, M, m7, P, m8]) := by
    simp (config := { maxSteps := 400000 }) [compareSuffix, opAt, pushAt, wfOp, after, rest,
      diff, missing, maskShift, TailProjectionInstances.rawShift, stS, initialState,
      Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
      Word.word_toNat_ofNat, mul_eq, List.exchange, List.set]
  exact (blockSound comparePrefix hpre).trans (hm.trans (blockSound compareSuffix hpost))

theorem offset_step (k : Nat) (hk : k < 32) :
    (32 : UInt256) + UInt256.ofNat (32 * k) = UInt256.ofNat (32 * (k + 1)) := by
  have h : UInt256.ofNat 32 + UInt256.ofNat (32 * k) = UInt256.ofNat (32 + 32 * k) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  rw [show 32 + 32 * k = 32 * (k + 1) from by omega] at h
  exact h

/-- The scalar advances by 160 modulo 256. -/
theorem scalar_step (s k : Nat) (hs : s < 256)
    (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    UInt256.land (255 : UInt256) ((160 : UInt256) + UInt256.ofNat s)
      = UInt256.ofNat (scalarAt (k + 1)) := by
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := rfl
  have h160 : (160 : UInt256) = UInt256.ofNat 160 := rfl
  rw [h255, h160,
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega : 160 + s < 2 ^ 256),
    land_ff _ (by omega), show 160 + s = s + 160 from by omega, hstep]

def nextAcc (input : ByteArray) (k : Nat) (a : UInt256) : UInt256 :=
  UInt256.lor a (UInt256.shiftRight
    (UInt256.xor (MachineState.readWord input (32 * k)) (guardWord k))
    (maskShift input (UInt256.ofNat (32 * k))))

def exitState (input : ByteArray) (k : Nat) (a : UInt256) :=
  stS input 247 [UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a, P7, M, m7, P, m8]

def gasSteps_compare_more_sym (input : ByteArray) (W S sv ov acc : UInt256)
    (hc : UInt256.isTrue (UInt256.lt ((32 : UInt256) + ov) (UInt256.ofNat input.size))) :
    GasSteps (stS input 207 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 152 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight
          (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov)),
        P7, M, m7, P, m8]) := by
  let sv' := UInt256.land 255 (160 + sv)
  let ov' := (32 : UInt256) + ov
  let a' := UInt256.lor acc (UInt256.shiftRight
    (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov))
  have f := gasSteps_compare_fold input W S sv ov acc
  exact f.trans (gasSteps_size_more input sv' ov' [a', P7, M, m7, P, m8] (by simp) hc)

def gasSteps_compare_end_sym (input : ByteArray) (W S sv ov acc : UInt256)
    (hc : ¬ UInt256.isTrue (UInt256.lt ((32 : UInt256) + ov) (UInt256.ofNat input.size))) :
    GasSteps (stS input 207 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 247 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight
          (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov)),
        P7, M, m7, P, m8]) := by
  exact (gasSteps_compare_fold input W S sv ov acc).trans
    (gasSteps_size_end input (UInt256.land 255 (160 + sv)) (32 + ov)
      [UInt256.lor acc (UInt256.shiftRight
        (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov)),
        P7, M, m7, P, m8] (by simp) hc)

theorem compare_cond (input : ByteArray) (k : Nat) (hk : k < 32)
    (hfit : input.size < 2 ^ 256) :
    UInt256.isTrue (UInt256.lt ((32 : UInt256) + UInt256.ofNat (32 * k))
      (UInt256.ofNat input.size)) ↔ 32 * (k + 1) < input.size := by
  rw [offset_step k hk]
  unfold UInt256.lt UInt256.isTrue
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega : 32 * (k + 1) < 2 ^ 256),
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  by_cases h : 32 * (k + 1) < input.size
  · simp only [if_pos h]
    exact ⟨fun _ => h, fun _ => by decide⟩
  · simp only [if_neg h]
    exact ⟨fun hc => absurd (by decide : (UInt256.ofNat 0).toNat = 0) hc,
      fun h' => (h h').elim⟩


def gasSteps_compare_more (input : ByteArray) (k s : Nat) (a : UInt256)
    (hfit : input.size < 2 ^ 256) (hbound : 32 * (k + 1) < input.size)
    (hk : k < 32) (hs : s < 256) (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    GasSteps (compareState input k s a)
      (loopState input (k + 1) (nextAcc input k a)) := by
  have hoff : (UInt256.ofNat (32 * k)).toNat = 32 * k := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h := gasSteps_compare_more_sym input (guardWord k)
    (UInt256.mul M (UInt256.ofNat (scalarAt k))) (UInt256.ofNat s)
    (UInt256.ofNat (32 * k)) a ((compare_cond input k hk hfit).2 hbound)
  simpa only [compareState, loopState, nextAcc, stS, frame, hoff,
    scalar_step s k hs hstep, offset_step k hk] using h

def gasSteps_compare_end (input : ByteArray) (k s : Nat) (a : UInt256)
    (hfit : input.size < 2 ^ 256) (hbound : input.size ≤ 32 * (k + 1))
    (hk : k < 32) (hs : s < 256) (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    GasSteps (compareState input k s a)
      (exitState input (k + 1) (nextAcc input k a)) := by
  have hoff : (UInt256.ofNat (32 * k)).toNat = 32 * k := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h := gasSteps_compare_end_sym input (guardWord k)
    (UInt256.mul M (UInt256.ofNat (scalarAt k))) (UInt256.ofNat s)
    (UInt256.ofNat (32 * k)) a (fun hc => by have := (compare_cond input k hk hfit).1 hc; omega)
  simpa only [compareState, exitState, nextAcc, stS, frame, hoff,
    scalar_step s k hs hstep, offset_step k hk] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan.gasSteps_compare_end
