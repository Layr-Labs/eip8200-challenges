import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar
def gasSteps_compare_fold (input : ByteArray) (W S sv ov acc : UInt256) :
    GasSteps (stS input 216 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 249 [UInt256.land 255 (160 + sv), 32 + ov,
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
  have pos200 : Artifact.submissionArtifact.instructionPC 127 = 216 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step200 := soundS (opAt 127 .JUMPDEST)
    (blockOfS _ (pcFactS input 127 216 [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos200)
      (stepS_jumpdest input 216 [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos201 : Artifact.submissionArtifact.instructionPC 128 = 217 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step201 := soundS (opAt 128 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 128 217 [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos201)
      (stepS_dup input 217 3 (by decide) [W, S, sv, ov, acc, P7, M, m7, P, m8] ov (by rfl) (by simp) (by norm_num)))
  have pos202 : Artifact.submissionArtifact.instructionPC 129 = 218 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step202 := soundS (opAt 129 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 129 218 [ov, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos202)
      (stepS_calldataload input 218 ov [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos203 : Artifact.submissionArtifact.instructionPC 130 = 219 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step203 := soundS (opAt 130 .XOR)
    (blockOfS _ (pcFactS input 130 219 [v0, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos203)
      (stepS_xor input 219 v0 W [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos204 : Artifact.submissionArtifact.instructionPC 131 = 220 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step204 := soundS (pushAt 131 4 1073790976)
    (blockOfS _ (pcFactS input 131 220 [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos204)
      (stepS_push input 220 4 (1073790976 : UInt256) [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos205 : Artifact.submissionArtifact.instructionPC 132 = 225 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step205 := soundS (opAt 132 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 132 225 [(1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos205)
      (stepS_dup input 225 4 (by decide) [(1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] ov (by rfl) (by simp) (by norm_num)))
  have pos206 : Artifact.submissionArtifact.instructionPC 133 = 226 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step206 := soundS (opAt 133 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 133 226 [ov, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos206)
      (stepS_calldatasize input 226 [ov, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos207 : Artifact.submissionArtifact.instructionPC 134 = 227 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step207 := soundS (opAt 134 .SUB)
    (blockOfS _ (pcFactS input 134 227 [v2, ov, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos207)
      (stepS_sub input 227 v2 ov [(1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos208 : Artifact.submissionArtifact.instructionPC 135 = 228 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step208 := soundS (opAt 135 .SHR)
    (blockOfS _ (pcFactS input 135 228 [v3, (1073790976 : UInt256), v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos208)
      (stepS_shr input 228 v3 (1073790976 : UInt256) [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos209 : Artifact.submissionArtifact.instructionPC 136 = 229 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step209 := soundS (pushAt 136 1 255)
    (blockOfS _ (pcFactS input 136 229 [v4, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos209)
      (stepS_push input 229 1 (255 : UInt256) [v4, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos210 : Artifact.submissionArtifact.instructionPC 137 = 231 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step210 := soundS (opAt 137 .AND)
    (blockOfS _ (pcFactS input 137 231 [(255 : UInt256), v4, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos210)
      (stepS_and input 231 (255 : UInt256) v4 [v1, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos211 : Artifact.submissionArtifact.instructionPC 138 = 232 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step211 := soundS (opAt 138 .SHR)
    (blockOfS _ (pcFactS input 138 232 [v5, v1, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos211)
      (stepS_shr input 232 v5 v1 [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos212 : Artifact.submissionArtifact.instructionPC 139 = 233 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step212 := soundS (opAt 139 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 139 233 [v6, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos212)
      (stepS_dup input 233 4 (by decide) [v6, S, sv, ov, acc, P7, M, m7, P, m8] acc (by rfl) (by simp) (by norm_num)))
  have pos213 : Artifact.submissionArtifact.instructionPC 140 = 234 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step213 := soundS (opAt 140 .OR)
    (blockOfS _ (pcFactS input 140 234 [acc, v6, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos213)
      (stepS_or input 234 acc v6 [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos214 : Artifact.submissionArtifact.instructionPC 141 = 235 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step214 := soundS (opAt 141 (.Swap ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 141 235 [v7, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pos214)
      (stepS_swap input 235 3 (by decide) [v7, S, sv, ov, acc, P7, M, m7, P, m8] [acc, S, sv, ov, v7, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have pos215 : Artifact.submissionArtifact.instructionPC 142 = 236 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step215 := soundS (opAt 142 .POP)
    (blockOfS _ (pcFactS input 142 236 [acc, S, sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos215)
      (stepS_pop input 236 acc [S, sv, ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos216 : Artifact.submissionArtifact.instructionPC 143 = 237 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step216 := soundS (opAt 143 .POP)
    (blockOfS _ (pcFactS input 143 237 [S, sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos216)
      (stepS_pop input 237 S [sv, ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos217 : Artifact.submissionArtifact.instructionPC 144 = 238 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step217 := soundS (pushAt 144 1 160)
    (blockOfS _ (pcFactS input 144 238 [sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos217)
      (stepS_push input 238 1 (160 : UInt256) [sv, ov, v7, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos218 : Artifact.submissionArtifact.instructionPC 145 = 240 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step218 := soundS (opAt 145 .ADD)
    (blockOfS _ (pcFactS input 145 240 [(160 : UInt256), sv, ov, v7, P7, M, m7, P, m8] (by norm_num) pos218)
      (stepS_add input 240 (160 : UInt256) sv [ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos219 : Artifact.submissionArtifact.instructionPC 146 = 241 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step219 := soundS (pushAt 146 1 255)
    (blockOfS _ (pcFactS input 146 241 [v8, ov, v7, P7, M, m7, P, m8] (by norm_num) pos219)
      (stepS_push input 241 1 (255 : UInt256) [v8, ov, v7, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos220 : Artifact.submissionArtifact.instructionPC 147 = 243 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step220 := soundS (opAt 147 .AND)
    (blockOfS _ (pcFactS input 147 243 [(255 : UInt256), v8, ov, v7, P7, M, m7, P, m8] (by norm_num) pos220)
      (stepS_and input 243 (255 : UInt256) v8 [ov, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos221 : Artifact.submissionArtifact.instructionPC 148 = 244 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step221 := soundS (opAt 148 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 148 244 [v9, ov, v7, P7, M, m7, P, m8] (by norm_num) pos221)
      (stepS_swap input 244 0 (by decide) [v9, ov, v7, P7, M, m7, P, m8] [ov, v9, v7, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have pos222 : Artifact.submissionArtifact.instructionPC 149 = 245 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step222 := soundS (pushAt 149 1 32)
    (blockOfS _ (pcFactS input 149 245 [ov, v9, v7, P7, M, m7, P, m8] (by norm_num) pos222)
      (stepS_push input 245 1 (32 : UInt256) [ov, v9, v7, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have pos223 : Artifact.submissionArtifact.instructionPC 150 = 247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step223 := soundS (opAt 150 .ADD)
    (blockOfS _ (pcFactS input 150 247 [(32 : UInt256), ov, v9, v7, P7, M, m7, P, m8] (by norm_num) pos223)
      (stepS_add input 247 (32 : UInt256) ov [v9, v7, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have pos224 : Artifact.submissionArtifact.instructionPC 151 = 248 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have step224 := soundS (opAt 151 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 151 248 [v10, v9, v7, P7, M, m7, P, m8] (by norm_num) pos224)
      (stepS_swap input 248 0 (by decide) [v10, v9, v7, P7, M, m7, P, m8] [v9, v10, v7, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
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
  stS input 255 [UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a, P7, M, m7, P, m8]

def gasSteps_compare_more_sym (input : ByteArray) (W S sv ov acc : UInt256)
    (hc : UInt256.isTrue (UInt256.lt ((32 : UInt256) + ov) (UInt256.ofNat input.size))) :
    GasSteps (stS input 216 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 155 [UInt256.land 255 (160 + sv), 32 + ov,
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
    GasSteps (stS input 216 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 255 [UInt256.land 255 (160 + sv), 32 + ov,
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
