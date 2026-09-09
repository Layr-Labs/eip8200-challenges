import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar
def gasSteps_compare_fold (input : ByteArray) (W S sv ov acc : UInt256) :
    GasSteps (stS input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 381 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight (UInt256.xor (MachineState.readWord input ov.toNat) W)
          (maskShift input ov)), P7, M, m7, P, m8]) := by
  let v0 : UInt256 := MachineState.readWord input (ov).toNat
  let v1 : UInt256 := UInt256.xor v0 W
  let v2 : UInt256 := UInt256.ofNat input.size
  let v3 : UInt256 := (v2 - ov)
  let v4 : UInt256 := UInt256.shiftRight (1073790976 : UInt256) v3
  let v5 : UInt256 := UInt256.land (255 : UInt256) v4
  let v6 : UInt256 := UInt256.shiftRight v1 v5
  let v7 : UInt256 := UInt256.lor acc v6
  let v8 : UInt256 := ((160 : UInt256) + sv)
  let v9 : UInt256 := UInt256.land (255 : UInt256) v8
  let v10 : UInt256 := ((32 : UInt256) + ov)
  have pos200 : Artifact.submissionArtifact.instructionPC 200 = 348 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step200 := soundS (opAt 200 .JUMPDEST)
    (blockOfS _ (pcFactS input 200 348 [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos200)
      (stepS_jumpdest input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos201 : Artifact.submissionArtifact.instructionPC 201 = 349 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step201 := soundS (opAt 201 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 201 349 [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos201)
      (stepS_dup input 349 3 (by decide) [W, S, sv, ov, acc, P7, M, m7, P, m8] ov (by rfl) (by simp) (by norm_num)))
  have pos202 : Artifact.submissionArtifact.instructionPC 202 = 350 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step202 := soundS (opAt 202 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 202 350 [ov, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos202)
      (stepS_calldataload input 350 ov [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos203 : Artifact.submissionArtifact.instructionPC 203 = 351 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step203 := soundS (opAt 203 .XOR)
    (blockOfS _ (pcFactS input 203 351 [v0, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos203)
      (stepS_xor input 351 v0 W [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos204 : Artifact.submissionArtifact.instructionPC 204 = 352 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step204 := soundS (pushAt 204 4 1073790976)
    (blockOfS _ (pcFactS input 204 352 [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos204)
      (stepS_push input 352 4 (1073790976 : UInt256) [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos205 : Artifact.submissionArtifact.instructionPC 205 = 357 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step205 := soundS (opAt 205 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 205 357 [(1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos205)
      (stepS_dup input 357 4 (by decide) [(1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] ov (by rfl) (by simp) (by norm_num)))
  have pos206 : Artifact.submissionArtifact.instructionPC 206 = 358 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step206 := soundS (opAt 206 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 206 358 [ov, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos206)
      (stepS_calldatasize input 358 [ov, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos207 : Artifact.submissionArtifact.instructionPC 207 = 359 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step207 := soundS (opAt 207 .SUB)
    (blockOfS _ (pcFactS input 207 359 [v2, ov, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos207)
      (stepS_sub input 359 v2 ov [(1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos208 : Artifact.submissionArtifact.instructionPC 208 = 360 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step208 := soundS (opAt 208 .SHR)
    (blockOfS _ (pcFactS input 208 360 [v3, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos208)
      (stepS_shr input 360 v3 (1073790976 : UInt256) [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos209 : Artifact.submissionArtifact.instructionPC 209 = 361 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step209 := soundS (pushAt 209 1 255)
    (blockOfS _ (pcFactS input 209 361 [v4, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos209)
      (stepS_push input 361 1 (255 : UInt256) [v4, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos210 : Artifact.submissionArtifact.instructionPC 210 = 363 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step210 := soundS (opAt 210 .AND)
    (blockOfS _ (pcFactS input 210 363 [(255 : UInt256), v4, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos210)
      (stepS_and input 363 (255 : UInt256) v4 [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos211 : Artifact.submissionArtifact.instructionPC 211 = 364 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step211 := soundS (opAt 211 .SHR)
    (blockOfS _ (pcFactS input 211 364 [v5, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos211)
      (stepS_shr input 364 v5 v1 [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos212 : Artifact.submissionArtifact.instructionPC 212 = 365 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step212 := soundS (opAt 212 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 212 365 [v6, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos212)
      (stepS_dup input 365 4 (by decide) [v6, S, sv, ov, acc, P7, M, m7, P, m8] acc (by rfl) (by simp) (by norm_num)))
  have pos213 : Artifact.submissionArtifact.instructionPC 213 = 366 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step213 := soundS (opAt 213 .OR)
    (blockOfS _ (pcFactS input 213 366 [acc, v6, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos213)
      (stepS_or input 366 acc v6 [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos214 : Artifact.submissionArtifact.instructionPC 214 = 367 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step214 := soundS (opAt 214 (.Swap ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 214 367 [v7, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos214)
      (stepS_swap input 367 3 (by decide) [v7, S, sv, ov, acc, P7, M, m7, P, m8] [acc, S, sv, ov, v7, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have pos215 : Artifact.submissionArtifact.instructionPC 215 = 368 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step215 := soundS (opAt 215 .POP)
    (blockOfS _ (pcFactS input 215 368 [acc, S, sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos215)
      (stepS_pop input 368 acc [S, sv, ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos216 : Artifact.submissionArtifact.instructionPC 216 = 369 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step216 := soundS (opAt 216 .POP)
    (blockOfS _ (pcFactS input 216 369 [S, sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos216)
      (stepS_pop input 369 S [sv, ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos217 : Artifact.submissionArtifact.instructionPC 217 = 370 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step217 := soundS (pushAt 217 1 160)
    (blockOfS _ (pcFactS input 217 370 [sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos217)
      (stepS_push input 370 1 (160 : UInt256) [sv, ov, v7, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos218 : Artifact.submissionArtifact.instructionPC 218 = 372 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step218 := soundS (opAt 218 .ADD)
    (blockOfS _ (pcFactS input 218 372 [(160 : UInt256), sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos218)
      (stepS_add input 372 (160 : UInt256) sv [ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos219 : Artifact.submissionArtifact.instructionPC 219 = 373 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step219 := soundS (pushAt 219 1 255)
    (blockOfS _ (pcFactS input 219 373 [v8, ov, v7, P7, M, m7, P, m8] (by norm_num) pos219)
      (stepS_push input 373 1 (255 : UInt256) [v8, ov, v7, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos220 : Artifact.submissionArtifact.instructionPC 220 = 375 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step220 := soundS (opAt 220 .AND)
    (blockOfS _ (pcFactS input 220 375 [(255 : UInt256), v8, ov, v7, P7, M, m7, P, m8] (by norm_num) pos220)
      (stepS_and input 375 (255 : UInt256) v8 [ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos221 : Artifact.submissionArtifact.instructionPC 221 = 376 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step221 := soundS (opAt 221 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 221 376 [v9, ov, v7, P7, M, m7, P, m8] (by norm_num) pos221)
      (stepS_swap input 376 0 (by decide) [v9, ov, v7, P7, M, m7, P, m8] [ov, v9, v7, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have pos222 : Artifact.submissionArtifact.instructionPC 222 = 377 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step222 := soundS (pushAt 222 1 32)
    (blockOfS _ (pcFactS input 222 377 [ov, v9, v7, P7, M, m7, P, m8] (by norm_num) pos222)
      (stepS_push input 377 1 (32 : UInt256) [ov, v9, v7, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos223 : Artifact.submissionArtifact.instructionPC 223 = 379 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step223 := soundS (opAt 223 .ADD)
    (blockOfS _ (pcFactS input 223 379 [(32 : UInt256), ov, v9, v7, P7, M, m7, P, m8] (by norm_num) pos223)
      (stepS_add input 379 (32 : UInt256) ov [v9, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos224 : Artifact.submissionArtifact.instructionPC 224 = 380 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step224 := soundS (opAt 224 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 224 380 [v10, v9, v7, P7, M, m7, P, m8] (by norm_num) pos224)
      (stepS_swap input 380 0 (by decide) [v10, v9, v7, P7, M, m7, P, m8] [v9, v10, v7, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  exact step200.trans (step201.trans (step202.trans (step203.trans (step204.trans (step205.trans (step206.trans (step207.trans (step208.trans (step209.trans (step210.trans (step211.trans (step212.trans (step213.trans (step214.trans (step215.trans (step216.trans (step217.trans (step218.trans (step219.trans (step220.trans (step221.trans (step222.trans (step223.trans (step224))))))))))))))))))))))))

/-- The offset advances by a word. -/
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
  stS input 168 [UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a, P7, M, m7, P, m8]

def gasSteps_compare_more_sym (input : ByteArray) (W S sv ov acc : UInt256)
    (hc : ¬ UInt256.isTrue (UInt256.gt ((32 : UInt256) + ov) (UInt256.ofNat input.size))) :
    GasSteps (stS input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 322 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight
          (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov)),
        P7, M, m7, P, m8]) := by
  let sv' := UInt256.land 255 (160 + sv)
  let ov' := (32 : UInt256) + ov
  let a' := UInt256.lor acc (UInt256.shiftRight
    (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov))
  have f := gasSteps_compare_fold input W S sv ov acc
  have t := gasSteps_size_skip input sv' ov' [a', P7, M, m7, P, m8] (by simp) hc
  have p := soundS (pushAt 230 2 322)
    (blockOfS _ (pcFactS input 230 387 _ (by norm_num) (by rfl))
      (stepS_push input 387 2 322 [sv', ov', a', P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have j := soundS (opAt 231 .JUMP)
    (blockOfS _ (pcFactS input 231 390 _ (by norm_num) (by rfl))
      (stepS_jump input 390 322 322 [sv', ov', a', P7, M, m7, P, m8]
        (by simp) (by norm_num) rfl
        (Artifact.submissionArtifact.isValidJumpDest_index 178 (by rfl))))
  exact f.trans (t.trans (p.trans j))

def gasSteps_compare_end_sym (input : ByteArray) (W S sv ov acc : UInt256)
    (hc : UInt256.isTrue (UInt256.gt ((32 : UInt256) + ov) (UInt256.ofNat input.size))) :
    GasSteps (stS input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 168 [UInt256.land 255 (160 + sv), 32 + ov,
        UInt256.lor acc (UInt256.shiftRight
          (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov)),
        P7, M, m7, P, m8]) := by
  exact (gasSteps_compare_fold input W S sv ov acc).trans
    (gasSteps_size_done input (UInt256.land 255 (160 + sv)) (32 + ov)
      [UInt256.lor acc (UInt256.shiftRight
        (UInt256.xor (MachineState.readWord input ov.toNat) W) (maskShift input ov)),
        P7, M, m7, P, m8] (by simp) hc)

theorem compare_cond (input : ByteArray) (k : Nat) (hk : k < 32)
    (hfit : input.size < 2 ^ 256) :
    UInt256.isTrue (UInt256.gt ((32 : UInt256) + UInt256.ofNat (32 * k))
      (UInt256.ofNat input.size)) ↔ input.size < 32 * (k + 1) := by
  rw [offset_step k hk]
  unfold UInt256.gt UInt256.isTrue
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega : 32 * (k + 1) < 2 ^ 256),
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  by_cases h : input.size < 32 * (k + 1)
  · simp only [if_pos h]
    exact ⟨fun _ => h, fun _ => by decide⟩
  · simp only [if_neg h]
    exact ⟨fun hc => absurd (by decide : (UInt256.ofNat 0).toNat = 0) hc,
      fun h' => (h h').elim⟩


def gasSteps_compare_more (input : ByteArray) (k s : Nat) (a : UInt256)
    (hfit : input.size < 2 ^ 256) (hbound : 32 * (k + 1) ≤ input.size)
    (hk : k < 32) (hs : s < 256) (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    GasSteps (compareState input k s a)
      (loopState input (k + 1) (nextAcc input k a)) := by
  have hoff : (UInt256.ofNat (32 * k)).toNat = 32 * k := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h := gasSteps_compare_more_sym input (guardWord k)
    (UInt256.mul M (UInt256.ofNat (scalarAt k))) (UInt256.ofNat s)
    (UInt256.ofNat (32 * k)) a (fun hc => by have := (compare_cond input k hk hfit).1 hc; omega)
  simpa only [compareState, loopState, nextAcc, stS, frame, hoff,
    scalar_step s k hs hstep, offset_step k hk] using h

def gasSteps_compare_end (input : ByteArray) (k s : Nat) (a : UInt256)
    (hfit : input.size < 2 ^ 256) (hbound : input.size < 32 * (k + 1))
    (hk : k < 32) (hs : s < 256) (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    GasSteps (compareState input k s a)
      (exitState input (k + 1) (nextAcc input k a)) := by
  have hoff : (UInt256.ofNat (32 * k)).toNat = 32 * k := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h := gasSteps_compare_end_sym input (guardWord k)
    (UInt256.mul M (UInt256.ofNat (scalarAt k))) (UInt256.ofNat s)
    (UInt256.ofNat (32 * k)) a ((compare_cond input k hk hfit).2 hbound)
  simpa only [compareState, exitState, nextAcc, stS, frame, hoff,
    scalar_step s k hs hstep, offset_step k hk] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan.gasSteps_compare_end
