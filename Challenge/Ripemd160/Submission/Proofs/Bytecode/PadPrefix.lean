import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedSchedule
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace DenseScheduleTemplate

def template (touch : Nat) : List Instr :=
  [.op .JUMPDEST, .push ⟨1, by decide⟩ (UInt256.ofNat touch),
   .op .ADD, .op .MLOAD, .op .POP]

/-- The outer padding pass already allocated the full message. -/
def dropTemplate : List Instr := [.op .JUMPDEST, .op .POP]

theorem run_drop (s : State) (pc ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running) :
    runInstrSeq dropTemplate {s with pc := pc, stack := UInt256.ofNat p :: ret :: rest} =
      some {s with pc := pcAfter pc dropTemplate, stack := ret :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 4) : rest.length + n < 1024 := by omega
  simp (discharger := omega) [dropTemplate, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hcap, List.length_cons, Nat.add_assoc]
  rfl

theorem active_eq (s : State) (p touch : Nat)
    (hbound : p + 64 < 2 ^ 256) (halign : p % 32 = 0)
    (htouch : 1 ≤ touch ∧ touch ≤ 32) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat touch + UInt256.ofNat p).toNat 32) =
      loadedActiveWords s (UInt256.ofNat p) := by
  have hptr : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfirst : MachineState.activeWordsAfter s.activeWords.toNat p 32 < 2 ^ 256 := by
    have hs := s.activeWords.val.isLt
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    constructor
    · exact hs
    · omega
  have hp32 := PairedScheduleContract.pointer_add32_toNat p hbound
  have hpt : (UInt256.ofNat touch + UInt256.ofNat p).toNat = touch + p := by
    rw [Word.ofNat_add_ofNat (by omega), Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold loadedActiveWords activeAfterWord
  dsimp only
  rw [hp32, hptr, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfirst, hpt]
  congr 1
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  have hd : (touch + p + 32 - 1) / 32 = (p + 32 + 32 - 1) / 32 := by omega
  rw [hd]
  have hle : (p + 32 - 1) / 32 + 1 ≤ (p + 32 + 32 - 1) / 32 + 1 := by omega
  simp only [Nat.max_def]
  split_ifs <;> omega

theorem run_template (s : State) (pc ret : UInt256) (p touch : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running)
    (hbound : p + 64 < 2 ^ 256) (halign : p % 32 = 0)
    (htouch : 1 ≤ touch ∧ touch ≤ 32) :
    runInstrSeq (template touch) {s with pc := pc, stack := UInt256.ofNat p :: ret :: rest} =
      some {s with pc := pcAfter pc (template touch), stack := (ret :: rest), activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  have hcap (n : Nat) (hn : n ≤ 4) : rest.length + n < 1024 := by omega
  have ha := active_eq s p touch hbound halign htouch
  simp (discharger := omega) [template, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hcap, List.length_cons, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha]
  rfl
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefix
