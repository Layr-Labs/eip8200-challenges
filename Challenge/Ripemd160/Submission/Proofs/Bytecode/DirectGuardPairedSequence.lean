import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawSegment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedSequence
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open DirectGuardPairedRaw RawLocatedSequence

private theorem pair_xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  simp [UInt256.xor, Fin.xor, Nat.xor_comm]

def segment (code : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) : RawLocatedSequence.Segment where
  code := code
  preBytes := pre
  instructions := pairCode
  data := []
  assembly_eq := by simpa only [List.append_nil, pairBytes] using ha

def path (code : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) : List (RawLocatedSequence.Located code .Osaka) :=
  [
    (segment code pre ha).located .Osaka 0 (.op .JUMPDEST) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 1 (.op (.Swap ⟨0, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 2 (.op (.Dup ⟨1, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 3 (.op .CALLDATALOAD) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 4 (.op (.Dup ⟨3, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 5 (.op .XOR) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 6 (.op .OR) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 7 (.op (.Swap ⟨0, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 8 (.push ⟨1, by decide⟩ (UInt256.ofNat 32)) (by rfl) (by exact ⟨by decide, by decide⟩),
    (segment code pre ha).located .Osaka 9 (.op .ADD) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 10 (.op (.Swap ⟨0, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 11 (.op (.Dup ⟨1, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 12 (.op .CALLDATALOAD) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 13 (.op (.Dup ⟨3, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 14 (.op .XOR) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 15 (.op .OR) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 16 (.op (.Swap ⟨0, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 17 (.push ⟨1, by decide⟩ (UInt256.ofNat 32)) (by rfl) (by exact ⟨by decide, by decide⟩),
    (segment code pre ha).located .Osaka 18 (.op .ADD) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 19 (.push ⟨2, by decide⟩ (UInt256.ofNat 992)) (by rfl) (by exact ⟨by decide, by decide⟩),
    (segment code pre ha).located .Osaka 20 (.op (.Dup ⟨1, by decide⟩)) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 21 (.op .LT) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 22 (.push ⟨2, by decide⟩ (UInt256.ofNat 5231)) (by rfl) (by exact ⟨by decide, by decide⟩),
    (segment code pre ha).located .Osaka 23 (.op .JUMPI) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩),
    (segment code pre ha).located .Osaka 24 (.push ⟨1, by decide⟩ (UInt256.ofNat 67)) (by rfl) (by exact ⟨by decide, by decide⟩),
    (segment code pre ha).located .Osaka 25 (.op .JUMP) (by rfl) (by exact ⟨by rfl, trivial, by decide⟩)
  ]

theorem run_pair_more
    (code input : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) (hpre : pre.length = 5231) (n : Nat) (hn : n < 28)
    (hdest : Decode.isValidJumpDest code 5231 = true) :
    RawLocatedSequence.runBlock ((path code pre ha).take 24) (pairLoopState code input n) =
      some (pairLoopState code input (n + 2)) := by
  have hstart : 32 * n + 32 < 2 ^ 256 := by omega
  have hnext : 32 * n + 64 < 2 ^ 256 := by omega
  have hnext2 : 32 * n + 96 < 2 ^ 256 := by omega
  have hlt : 32 * n + 96 < 992 := by omega
  have hmod : (32 * n + 32) % 2 ^ 256 = 32 * n + 32 :=
    Nat.mod_eq_of_lt hstart
  have hnextMod : (32 * n + 64) % 2 ^ 256 = 32 * n + 64 :=
    Nat.mod_eq_of_lt hnext
  have hnextMod2 : (32 * n + 96) % 2 ^ 256 = 32 * n + 96 :=
    Nat.mod_eq_of_lt hnext2
  have hmodN : (32 * n + 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n + 32 := by
    apply Nat.mod_eq_of_lt
    omega
  have hnextN : (32 * n + 64) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n + 64 := by
    apply Nat.mod_eq_of_lt
    omega
  have hnaddr : 32 * (n + 1) + 32 = 32 * n + 64 := by omega
  have hnaddr2 : 32 * (n + 2) + 32 = 32 * n + 96 := by omega
  have hnaddr0 : 32 + 32 * n = 32 * n + 32 := by omega
  have hnaddr1 : 32 + (32 + 32 * n) = 32 * n + 64 := by omega
  have hnaddr1' : 32 + (32 * n + 32) = 32 * n + 64 := by omega
  have hnaddr2' : 32 + (32 + (32 * n + 32)) = 32 * n + 96 := by omega
  have hacc1 : pairLoopAcc input (n + 1) =
      UInt256.lor (UInt256.xor
        (MachineState.readWord input (32 * (n + 1)))
        (pairReferenceWord input)) (pairLoopAcc input n) := by
    rw [pairLoopAcc]
  have hacc2 : pairLoopAcc input (n + 2) =
      UInt256.lor (UInt256.xor
        (MachineState.readWord input (32 * (n + 2)))
        (pairReferenceWord input)) (pairLoopAcc input (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pairLoopAcc]
  have hcond : (UInt256.lt (UInt256.ofNat (32 * n + 96))
      (UInt256.ofNat 992)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, hnextMod2,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256), if_pos hlt]
    decide
  have hcond' : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat (32 + (32 + (32 * n + 32))))
        (UInt256.ofNat 992)) := by
    unfold UInt256.isTrue
    have hform : 32 + (32 + (32 * n + 32)) = 32 * n + 96 := by omega
    rw [hform]
    exact hcond
  simp (config := { maxSteps := 2000000 }) (discharger := omega)
    [path, segment, RawLocatedSequence.Segment.located, RawLocatedSequence.Segment.instructionPC, List.length_append, assembleBytes, hpre, pairCodeMore, pairCode, pairLoopState, pairBytes, hdest, hstart, hnext, hnext2,
      hmod, hnextMod, hnextMod2, hnaddr, hnaddr2, hlt,
      hcond, hcond',
      hacc1, hacc2,
      RawLocatedSequence.runBlock, RawLocatedSequence.runLocated, Challenge.EvmProof.DataStepper.runInstr,
      Instr.size, List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mul_add]
  constructor
  · have hpc : 32 * n + 64 + 32 = 32 * n + 96 := by omega
    rw [hnaddr2', hpc]
  · rw [hnaddr1', hnextN, hmodN,
        pair_xor_comm (pairReferenceWord input)
          (MachineState.readWord input (32 * n + 64)),
        pair_xor_comm (pairReferenceWord input)
          (MachineState.readWord input (32 * n + 32))]

theorem run_pair_terminal
    (code input : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) (hpre : pre.length = 5231)
    (hdest : Decode.isValidJumpDest code 67 = true) :
    RawLocatedSequence.runBlock (path code pre ha) (pairLoopState code input 28) =
      some (pairExitState code input) := by
  have hacc : pairLoopAcc input 30 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 960)
        (pairReferenceWord input))
        (UInt256.lor (UInt256.xor (MachineState.readWord input 928)
          (pairReferenceWord input)) (pairLoopAcc input 28)) := by
    rw [show 30 = 29 + 1 by omega, pairLoopAcc,
      show 29 = 28 + 1 by omega, pairLoopAcc]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)) := by
    decide
  have hcond : (UInt256.lt (UInt256.ofNat 992)
      (UInt256.ofNat 992)).toNat = 0 := by
    decide
  simp (config := { maxSteps := 2000000 }) (discharger := omega)
    [path, segment, RawLocatedSequence.Segment.located, RawLocatedSequence.Segment.instructionPC, List.length_append, assembleBytes, hpre, pairCode, pairLoopState, pairExitState, pairBytes, hdest,
      hacc, hfalse, hcond, RawLocatedSequence.runBlock, RawLocatedSequence.runLocated,
      Challenge.EvmProof.DataStepper.runInstr,
      Instr.size, List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mul_add]
  rw [pair_xor_comm (pairReferenceWord input)
        (MachineState.readWord input 960),
      pair_xor_comm (pairReferenceWord input)
        (MachineState.readWord input 928)]



def gasSteps_more (code input : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) (hpre : pre.length = 5231)
    (n : Nat) (hn : n < 28)
    (hdest : Decode.isValidJumpDest code 5231 = true) :
    GasSteps (pairLoopState code input n) (pairLoopState code input (n + 2)) :=
  RawLocatedSequence.runBlock_sound ((path code pre ha).take 24)
    (by rfl) (by rfl) (run_pair_more code input pre ha hpre n hn hdest)
    (by rfl) Challenge.Ripemd160.deployAddress_not_precompile

def gasSteps_terminal (code input : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) (hpre : pre.length = 5231)
    (hdest : Decode.isValidJumpDest code 67 = true) :
    GasSteps (pairLoopState code input 28) (pairExitState code input) :=
  RawLocatedSequence.runBlock_sound (path code pre ha)
    (by rfl) (by rfl) (run_pair_terminal code input pre ha hpre hdest)
    (by rfl) Challenge.Ripemd160.deployAddress_not_precompile

theorem valid_67 :
    Decode.isValidJumpDest submissionBytecode 67 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 48 = 67 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 48 (by rfl)
  change Decode.isValidJumpDest submissionBytecode
    (Artifact.submissionArtifact.instructionPC 48) = true at h
  rw [hp] at h
  exact h

def gasSteps_pair_loop (code input : ByteArray) (pre : List UInt8)
    (ha : mkCode (pre ++ pairBytes) = code) (hpre : pre.length = 5231)
    (hdest5231 : Decode.isValidJumpDest code 5231 = true)
    (hdest67 : Decode.isValidJumpDest code 67 = true) :
    GasSteps (pairLoopState code input 0) (pairExitState code input) := by
  have g0 := gasSteps_more code input pre ha hpre 0 (by omega) hdest5231
  have g2 := gasSteps_more code input pre ha hpre 2 (by omega) hdest5231
  have g4 := gasSteps_more code input pre ha hpre 4 (by omega) hdest5231
  have g6 := gasSteps_more code input pre ha hpre 6 (by omega) hdest5231
  have g8 := gasSteps_more code input pre ha hpre 8 (by omega) hdest5231
  have g10 := gasSteps_more code input pre ha hpre 10 (by omega) hdest5231
  have g12 := gasSteps_more code input pre ha hpre 12 (by omega) hdest5231
  have g14 := gasSteps_more code input pre ha hpre 14 (by omega) hdest5231
  have g16 := gasSteps_more code input pre ha hpre 16 (by omega) hdest5231
  have g18 := gasSteps_more code input pre ha hpre 18 (by omega) hdest5231
  have g20 := gasSteps_more code input pre ha hpre 20 (by omega) hdest5231
  have g22 := gasSteps_more code input pre ha hpre 22 (by omega) hdest5231
  have g24 := gasSteps_more code input pre ha hpre 24 (by omega) hdest5231
  have g26 := gasSteps_more code input pre ha hpre 26 (by omega) hdest5231
  have gt := gasSteps_terminal code input pre ha hpre hdest67
  have g02 := g0.trans g2
  have g024 := g02.trans g4
  have g0246 := g024.trans g6
  have g02468 := g0246.trans g8
  have g0246810 := g02468.trans g10
  have g024681012 := g0246810.trans g12
  have g02468101214 := g024681012.trans g14
  have g0246810121416 := g02468101214.trans g16
  have g024681012141618 := g0246810121416.trans g18
  have g02468101214161820 := g024681012141618.trans g20
  have g0246810121416182022 := g02468101214161820.trans g22
  have g024681012141618202224 := g0246810121416182022.trans g24
  have g02468101214161820222426 := g024681012141618202224.trans g26
  exact g02468101214161820222426.trans gt

#print axioms gasSteps_more
#print axioms gasSteps_terminal
#print axioms gasSteps_pair_loop

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedSequence
