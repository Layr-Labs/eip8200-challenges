import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInput
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace CycleSubmission.ZeroBaseDispatch
open Challenge.Modexp Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowTwentyOneEntry WindowNibbleKernel Word

def redirectProgram : List Instr := [.push 2 10947, .op .JUMP]

/-- Keep the decoded base size and jump to general handling if the base is
nonempty or the loaded exponent is zero. -/
def guardProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .CALLDATALOAD,
    .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩),
    .op .ISZERO, .op .OR, .push 1 66, .op .JUMPI]

def returnProgram : List Instr := [.push 1 32, .push 0 0, .op .RETURN]

def frame (input : ByteArray) : List UInt256 :=
  [MachineState.readWord input 160, MachineState.readWord input 128,
    MachineState.readWord input 96]

def frameWithBase (input : ByteArray) : List UInt256 :=
  MachineState.readWord input 0 :: frame input

def condition (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.isZero (MachineState.readWord input 96)) (MachineState.readWord input 0)

theorem run_redirect (template : State) (stack : List UInt256)
    (hcap : stack.length < 1023)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 10947 = true) :
    runInstructions redirectProgram (framed template (UInt256.ofNat 48) stack) =
      some (framed template (UInt256.ofNat 10947) stack) := by
  have hl : stack.length < 1024 := by omega
  have hnext : stack.length + 1 < 1024 := by omega
  simp [redirectProgram, framed, runInstructions, Stepper.runInstr,
    hl, hnext, hjump, literal_eq_ofNat, word_toNat_ofNat]

theorem run_guard (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 66 = true) :
    runInstructions guardProgram (framed template (UInt256.ofNat 52) (frame input)) =
      some (framed template
        (if (condition input).toNat = 0 then UInt256.ofNat 62 else UInt256.ofNat 66)
        (frameWithBase input)) := by
  have hz : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases h : (condition input).toNat = 0 <;>
    simp only [condition] at h <;>
    simp [guardProgram, framed, frame, frameWithBase, runInstructions, Stepper.runInstr,
      condition, h, hdata, hjump, hz, UInt256.isTrue, literal_eq_ofNat, word_toNat_ofNat,
      succ_ofNat_mod, ofNat_add_mod]

theorem condition_of_positive (input : ByteArray) (hb : baseSize input ≠ 0) :
    (condition input).toNat ≠ 0 := by
  intro hc
  rw [condition, word_toNat_lor] at hc
  have h := Nat.right_le_or
    (n := (MachineState.readWord input 96).isZero.toNat)
    (m := (MachineState.readWord input 0).toNat)
  rw [hc, Bytes.readWord_toNat] at h
  exact hb (Nat.eq_zero_of_le_zero h)

theorem condition_zero (input : ByteArray) (hc : (condition input).toNat = 0) :
    baseSize input = 0 ∧ (WindowTwentyOneInput.exponentWord input).toNat ≠ 0 := by
  have hb : baseSize input = 0 := by
    by_contra hn
    exact condition_of_positive input hn hc
  have hx : (MachineState.readWord input 0).toNat = 0 := (Bytes.readWord_toNat input 0).trans hb
  rw [condition, word_toNat_lor, hx, Nat.or_zero, word_toNat_isZero] at hc
  have he : (MachineState.readWord input 96).toNat ≠ 0 := by
    intro hz
    simp [hz] at hc
  refine ⟨hb, ?_⟩
  simpa [WindowTwentyOneInput.exponentWord, hb] using he

def returned (template : State) (stack : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 65
    stack := stack
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded template.memory 0 32 }

theorem run_return (template : State) (stack : List UInt256)
    (hcap : stack.length ≤ 1000) (hact : template.activeWords = UInt256.ofNat 0) :
    runInstructions returnProgram (framed template (UInt256.ofNat 62) stack) =
      some (returned template stack) := by
  have capacity (k : Nat) (hk : k ≤ 10) : stack.length + k < 1024 := by omega
  have hl : stack.length < 1024 := by omega
  have hz : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnProgram, returned, framed, runInstructions, Stepper.runInstr, hact, capacity, hl, hz,
    literal_eq_ofNat, succ_ofNat_mod, ofNat_add_mod, word_toNat_ofNat,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Nat.add_assoc]
end CycleSubmission.ZeroBaseDispatch
