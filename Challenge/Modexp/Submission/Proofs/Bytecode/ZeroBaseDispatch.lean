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

def guardProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .CALLDATALOAD, .op .ISZERO,
    .op (.Dup ⟨3, by decide⟩), .op .MUL, .push 2 11003, .op .JUMPI]

def returnProgram : List Instr :=
  [.op .JUMPDEST, .push 1 32, .push 0 0, .op .RETURN]

def frame (input : ByteArray) : List UInt256 :=
  [MachineState.readWord input 160, MachineState.readWord input 128,
    MachineState.readWord input 96]

def condition (input : ByteArray) : UInt256 :=
  MachineState.readWord input 96 * UInt256.isZero (MachineState.readWord input 0)

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
    (hjump : Decode.isValidJumpDest template.executionEnv.code 11003 = true) :
    runInstructions guardProgram (framed template (UInt256.ofNat 52) (frame input)) =
      some (framed template
        (if (condition input).toNat = 0 then UInt256.ofNat 62 else UInt256.ofNat 11003)
        (frame input)) := by
  have hz : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases h : (condition input).toNat = 0 <;>
    simp only [condition] at h <;>
    simp [guardProgram, framed, frame, runInstructions, Stepper.runInstr, condition,
      h, hdata, hjump, hz, UInt256.isTrue, literal_eq_ofNat, word_toNat_ofNat,
      succ_ofNat_mod, ofNat_add_mod]

private theorem mul_toNat (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % (2 ^ 256) := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem condition_of_zero (input : ByteArray) (h : baseSize input = 0) :
    condition input = WindowTwentyOneInput.exponentWord input := by
  have hh : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  rw [condition, hh, h]
  change MachineState.readWord input 96 * (1 : UInt256) = _
  rw [WindowTwentyOneInput.exponentWord,h,Nat.add_zero]
  apply word_ext
  rw [mul_toNat]
  change ((MachineState.readWord input 96).toNat * 1) % (2 ^ 256) = _
  rw [Nat.mul_one, Nat.mod_eq_of_lt (show (MachineState.readWord input 96).toNat < 2 ^ 256 from
    (MachineState.readWord input 96).val.isLt)]

theorem condition_of_positive (input : ByteArray) (h : baseSize input ≠ 0) :
    (condition input).toNat = 0 := by
  have hz : (MachineState.readWord input 0).toNat = baseSize input := Bytes.readWord_toNat input 0
  simp [condition, mul_toNat, UInt256.isZero,hz,h,word_toNat_ofNat]

def returned (template : State) (stack : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 11007
    stack := stack
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded template.memory 0 32 }

theorem run_return (template : State) (stack : List UInt256)
    (hcap : stack.length ≤ 1000) (hact : template.activeWords = UInt256.ofNat 0) :
    runInstructions returnProgram (framed template (UInt256.ofNat 11003) stack) =
      some (returned template stack) := by
  have capacity (k : Nat) (hk : k ≤ 10) : stack.length + k < 1024 := by omega
  have hl : stack.length < 1024 := by omega
  have hz : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnProgram, returned, framed, runInstructions, Stepper.runInstr, hact, capacity, hl, hz,
    literal_eq_ofNat, succ_ofNat_mod, ofNat_add_mod, word_toNat_ofNat,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Nat.add_assoc]
end CycleSubmission.ZeroBaseDispatch
