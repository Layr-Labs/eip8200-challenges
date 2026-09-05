import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P18
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Wide7

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-- A two-limb represented modulus with words `1, 7` is `radix + 7`. -/
theorem modulus_eq_radix_add_seven {mem : ByteArray} {mm : Nat}
    (hrep : Model.FastRepresents mem 0 2 mm)
    (hhi : (MachineState.readWord mem 0).toNat = 1)
    (hlo : (MachineState.readWord mem 32).toNat = 7) :
    mm = Limbs.radix + 7 := by
  have hv := Model.value_of_fastRepresents hrep
  change Nat.ofDigits Limbs.radix
    [(MachineState.readWord mem 32).toNat,
      (MachineState.readWord mem 0).toNat] = mm at hv
  simp [Nat.ofDigits_cons, hhi, hlo] at hv
  simpa [Nat.add_comm] using hv.symm

/-- The Montgomery residue of one for `radix + 7` is `49`. -/
theorem radix_sq_mod_radix_add_seven :
    Limbs.radix ^ 2 % (Limbs.radix + 7) = 49 := by
  have heq : Limbs.radix ^ 2 =
      (Limbs.radix - 7) * (Limbs.radix + 7) + 49 := by
    norm_num [Limbs.radix]
  rw [heq, Nat.add_mod]
  norm_num [Limbs.radix]

/-- The memory produced by the direct two-word residue construction. -/
def directMem (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) 4096)
    (Data.Bytes.natToBytesPadded 49 32) 4128

theorem directMem_represents (mem : ByteArray)
    (hR1 : Model.FastRepresents mem 4096 2 Limbs.radix) :
    Model.FastRepresents (directMem mem) 4096 2 49 := by
  have hzero := Model.fastRepresents_write_limb
    (k := 1) (value' := 0) (UInt256.ofNat 0) hR1 (by omega) (by
      norm_num [Limbs.radix])
  have hlow := Model.fastRepresents_write_low_of_zero
    (word := UInt256.ofNat 49) hzero (by omega)
  simpa [directMem] using hlow

theorem directMem_preserves {mem : ByteArray} {ptr count value : Nat}
    (hdisj : ptr + 32 * count ≤ 4096 ∨ 4160 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr count value) :
    Model.FastRepresents (directMem mem) ptr count value := by
  unfold directMem
  apply Model.fastRepresents_writeWord_disjoint
  · rcases hdisj with hbefore | hafter
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · apply Model.fastRepresents_writeWord_disjoint
    · rcases hdisj with hbefore | hafter
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · exact hrep

theorem readWord_directMem_high (mem : ByteArray) (addr : Nat)
    (haddr : 4160 ≤ addr) :
    MachineState.readWord (directMem mem) addr = MachineState.readWord mem addr := by
  simp only [directMem]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  all_goals rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  all_goals omega

/-! ## Exact runtime guard and execution trace -/

/-- The three comparisons made by the appended guard. -/
def Matches (mem : ByteArray) : Prop :=
  (MachineState.readWord mem 9504).toNat = 2 ∧
    (MachineState.readWord mem 0).toNat = 1 ∧
    (MachineState.readWord mem 32).toNat = 7

instance (mem : ByteArray) : Decidable (Matches mem) := by
  unfold Matches
  infer_instance

/-- Entry reached from the top-bit-clear branch of `R1B`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3086
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Fall-through after the limb-count comparison. -/
def highState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3099
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Fall-through after the high-word comparison. -/
def lowState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3109
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Fall-through after all three comparisons. -/
def directState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3120
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Original `DOUBLE256` entry used by every failed comparison. -/
def fallbackState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1911
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Direct-path return state. -/
def returnedState (s : State) (mem : ByteArray) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := directMem mem }

private theorem activeWords_read_9504 (s : State) (hact : 298 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9504 32) =
      s.activeWords := by
  have h : MachineState.activeWordsAfter s.activeWords.toNat 9504 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬ (32 = 0))]
    exact Nat.max_eq_left (by omega)
  rw [h]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

private theorem activeWords_read_low (s : State) (addr : Nat)
    (hact : 298 ≤ s.activeWords.toNat) (haddr : addr ≤ 32) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat addr 32) =
      s.activeWords := by
  have h : MachineState.activeWordsAfter s.activeWords.toNat addr 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬ (32 = 0))]
    exact Nat.max_eq_left (by omega)
  rw [h]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

private theorem activeWords_store_r1 (s : State) (addr : Nat)
    (hact : 298 ≤ s.activeWords.toNat) (haddr : addr ≤ 4128) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat addr 32) =
      s.activeWords := by
  have h : MachineState.activeWordsAfter s.activeWords.toNat addr 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬ (32 = 0))]
    exact Nat.max_eq_left (by omega)
  rw [h]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

set_option linter.unusedSimpArgs false in
theorem run_count_pass (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat)
    (hcount : (MachineState.readWord mem 9504).toNat = 2) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1883
      (entryState s mem px ret rest) =
      some (highState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat 2) (MachineState.readWord mem 9504) =
      UInt256.ofNat 1 := by
    simp [UInt256.eq, hcount]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1883, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, highState, fastPC24, hc2, hc3, hc4, hrun, heq, hzero, hfalse,
    activeWords_read_9504 s hact,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_count_fail (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat)
    (hcount : (MachineState.readWord mem 9504).toNat ≠ 2) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1883
      (entryState s mem px ret rest) =
      some (fallbackState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hrev : 2 ≠ (MachineState.readWord mem 9504).toNat := by
    intro h
    exact hcount h.symm
  have heq : UInt256.eq (UInt256.ofNat 2) (MachineState.readWord mem 9504) =
      UInt256.ofNat 0 := by
    simp [UInt256.eq, hrev]
  have hzero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 400000 }) [blk1883, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, fallbackState, fastPC24, hc2, hc3, hc4, hcode, hrun, heq, hzero,
    htrue, activeWords_read_9504 s hact, jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_high_pass (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat)
    (hhigh : (MachineState.readWord mem 0).toNat = 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1891
      (highState s mem px ret rest) =
      some (lowState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 1) (MachineState.readWord mem 0) =
      UInt256.ofNat 1 := by
    simp [UInt256.eq, hhigh]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1891, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    highState, lowState, fastPC24, hc2, hc3, hc4, hzeroNat, hrun, heq, hzero, hfalse,
    activeWords_read_low s 0 hact (by omega),
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_high_fail (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat)
    (hhigh : (MachineState.readWord mem 0).toNat ≠ 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1891
      (highState s mem px ret rest) =
      some (fallbackState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hrev : 1 ≠ (MachineState.readWord mem 0).toNat := by
    intro h
    exact hhigh h.symm
  have heq : UInt256.eq (UInt256.ofNat 1) (MachineState.readWord mem 0) =
      UInt256.ofNat 0 := by
    simp [UInt256.eq, hrev]
  have hzero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 400000 }) [blk1891, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    highState, fallbackState, fastPC24, hc2, hc3, hc4, hzeroNat, hcode, hrun, heq, hzero,
    htrue, activeWords_read_low s 0 hact (by omega), jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_low_pass (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat)
    (hlow : (MachineState.readWord mem 32).toNat = 7) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1898
      (lowState s mem px ret rest) =
      some (directState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat 7) (MachineState.readWord mem 32) =
      UInt256.ofNat 1 := by
    simp [UInt256.eq, hlow]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1898, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lowState, directState, fastPC24, hc2, hc3, hc4, hrun, heq, hzero, hfalse,
    activeWords_read_low s 32 hact (by omega),
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_low_fail (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat)
    (hlow : (MachineState.readWord mem 32).toNat ≠ 7) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1898
      (lowState s mem px ret rest) =
      some (fallbackState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hrev : 7 ≠ (MachineState.readWord mem 32).toNat := by
    intro h
    exact hlow h.symm
  have heq : UInt256.eq (UInt256.ofNat 7) (MachineState.readWord mem 32) =
      UInt256.ofNat 0 := by
    simp [UInt256.eq, hrev]
  have hzero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 400000 }) [blk1898, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lowState, fallbackState, fastPC24, hc2, hc3, hc4, hcode, hrun, heq, hzero,
    htrue, activeWords_read_low s 32 hact (by omega), jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_direct (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hrun : s.halt = .Running) (hact : 298 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1905
      (directState s mem px ret rest) =
      some (returnedState s mem ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 }) [blk1905, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    directState, returnedState, directMem, fastPC24, hc1, hc2, hc3, hc4, hzeroNat, hcode, hjump,
    hrun, activeWords_store_r1 s 4096 hact (by omega),
    activeWords_store_r1 s 4128 hact (by omega),
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

/-! ## Gas-carrying composition -/

/-- The complete successful guard trace. -/
def gasSteps_matches (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 298 ≤ s.activeWords.toNat) (hmatches : Matches mem) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (returnedState s mem ret rest) :=
  (((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka blk1883
      (s := entryState s mem px ret rest) hcode hfork
      (run_count_pass s mem px ret rest hcap hrun hact hmatches.1) hrun hnp).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka blk1891
      (s := highState s mem px ret rest) hcode hfork
      (run_high_pass s mem px ret rest hcap hrun hact hmatches.2.1) hrun hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka blk1898
      (s := lowState s mem px ret rest) hcode hfork
      (run_low_pass s mem px ret rest hcap hrun hact hmatches.2.2) hrun hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka blk1905
      (s := directState s mem px ret rest) hcode hfork
      (run_direct s mem px ret rest hcap hcode hjump hrun hact) hrun hnp)

/-- Every failed comparison reaches the unchanged `DOUBLE256` entry. -/
def gasSteps_fallback (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 298 ≤ s.activeWords.toNat) (hnot : ¬ Matches mem) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (fallbackState s mem px ret rest) :=
  if hc : (MachineState.readWord mem 9504).toNat = 2 then
    if hh : (MachineState.readWord mem 0).toNat = 1 then
      if hl : (MachineState.readWord mem 32).toNat = 7 then
        False.elim (hnot ⟨hc, hh, hl⟩)
      else
        ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka blk1883
          (s := entryState s mem px ret rest) hcode hfork
          (run_count_pass s mem px ret rest hcap hrun hact hc) hrun hnp).trans
        (Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka blk1891
          (s := highState s mem px ret rest) hcode hfork
          (run_high_pass s mem px ret rest hcap hrun hact hh) hrun hnp)).trans
        (Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka blk1898
          (s := lowState s mem px ret rest) hcode hfork
          (run_low_fail s mem px ret rest hcap hcode hrun hact hl) hrun hnp)
    else
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1883
        (s := entryState s mem px ret rest) hcode hfork
        (run_count_pass s mem px ret rest hcap hrun hact hc) hrun hnp).trans
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1891
        (s := highState s mem px ret rest) hcode hfork
        (run_high_fail s mem px ret rest hcap hcode hrun hact hh) hrun hnp)
  else
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka blk1883
      (s := entryState s mem px ret rest) hcode hfork
      (run_count_fail s mem px ret rest hcap hcode hrun hact hc) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Wide7
