import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel WindowTwentyOneBinding

def stateAt (pc : Nat) (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

def guardProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2688, .op .MLOAD,
   .push 3 127, .op .AND, .op .ISZERO,
   .push 1 1, .push 2 2720, .op .MLOAD, .op .GT, .op .AND,
   .push 2 3583, .op .JUMPI]

def validWidth (width : UInt256) : Prop :=
  ∃ n : Nat, 2 ≤ n ∧ n ≤ 8 ∧ width = UInt256.ofNat (32*n)

def condition (width inverse : UInt256) : UInt256 :=
  UInt256.land (UInt256.gt inverse (UInt256.ofNat 1))
    (UInt256.isZero (UInt256.land (UInt256.ofNat 127) width))

theorem inverse_ne_zero (low inverse : UInt256)
    (hinv : (low.toNat * inverse.toNat + 1) % 2 ^ 256 = 0) :
    inverse ≠ UInt256.ofNat 0 := by
  intro hz
  rw [hz] at hinv
  norm_num [Challenge.EvmProof.Word.word_toNat_ofNat] at hinv

theorem inverse_gt_one (inverse : UInt256)
    (hzero : inverse ≠ UInt256.ofNat 0) (hone : inverse ≠ UInt256.ofNat 1) :
    1 < inverse.toNat := by
  have hz : inverse.toNat ≠ 0 := by
    intro h
    apply hzero
    apply Challenge.EvmProof.Word.word_ext
    simpa [Challenge.EvmProof.Word.word_toNat_ofNat] using h
  have ho : inverse.toNat ≠ 1 := by
    intro h
    apply hone
    apply Challenge.EvmProof.Word.word_ext
    simpa [Challenge.EvmProof.Word.word_toNat_ofNat] using h
  omega

theorem condition_pass (width inverse : UInt256)
    (hw : width = UInt256.ofNat 128 ∨ width = UInt256.ofNat 256)
    (hz : inverse ≠ UInt256.ofNat 0) (ho : inverse ≠ UInt256.ofNat 1) :
    UInt256.isTrue (condition width inverse) := by
  have hi : UInt256.gt inverse (UInt256.ofNat 1) = UInt256.ofNat 1 := by
    have hh := inverse_gt_one inverse hz ho
    simp [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, hh]
  rcases hw with rfl | rfl <;> rw [condition, hi] <;> decide

theorem condition_width_fallback (width inverse : UInt256)
    (hvalid : validWidth width)
    (h128 : width ≠ UInt256.ofNat 128) (h256 : width ≠ UInt256.ofNat 256) :
    ¬ UInt256.isTrue (condition width inverse) := by
  rcases hvalid with ⟨n, hn, hn8, rfl⟩
  interval_cases n
  all_goals first
    | exact (h128 rfl).elim
    | exact (h256 rfl).elim
    | (unfold condition UInt256.gt; split <;> decide)

theorem condition_inverse_fallback (width : UInt256) :
    ¬ UInt256.isTrue (condition width (UInt256.ofNat 1)) := by
  unfold condition UInt256.gt
  split <;> norm_num [Challenge.EvmProof.Word.word_toNat_ofNat] at *
  unfold UInt256.isZero
  split <;> decide

theorem run_guardPass (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcond : UInt256.isTrue (condition (MachineState.readWord mem 2688)
      (MachineState.readWord mem 2720)))
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3583 = true) :
    runInstructions guardProgram (stateAt 3551 s mem hd pa pb pdst ret rest) =
      some (stateAt 3583 s mem hd pa pb pdst ret rest) := by
  unfold condition at hcond
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have ha := Monpro.activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hb := Monpro.activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [guardProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, stateAt, hc5, hc6, hc7, hc8,
    State.activeWordsAfterUInt256, ha, hb, hcond, hjump,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

theorem run_guardFallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcond : ¬ UInt256.isTrue (condition (MachineState.readWord mem 2688)
      (MachineState.readWord mem 2720))) :
    runInstructions guardProgram (stateAt 3551 s mem hd pa pb pdst ret rest) =
      some (stateAt 3574 s mem hd pa pb pdst ret rest) := by
  unfold condition at hcond
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have ha := Monpro.activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hb := Monpro.activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [guardProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, stateAt, hc5, hc6, hc7, hc8,
    State.activeWordsAfterUInt256, ha, hb, hcond,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
