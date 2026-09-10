import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory

set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM

def Matched (input : ByteArray) : Prop :=
  MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0 ∧
  MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
instance (input : ByteArray) : Decidable (Matched input) := inferInstanceAs (Decidable (_ ∧ _))


/-- The depth-2 rung additionally pins calldata words 2 and 3. -/
def Matched2 (input : ByteArray) : Prop :=
  MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2 ∧
  MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3
instance (input : ByteArray) : Decidable (Matched2 input) := inferInstanceAs (Decidable (_ ∧ _))

/-- The compact dispatcher consumes one block. The exact 128-byte return is separate. -/
def double (_input : ByteArray) : Bool := false

@[simp] theorem double_eq_false (input : ByteArray) : double input = false := rfl

def prepared (s : State) (i : Nat) : State :=
  if i = 0 then PrefixStateMemory.copied s else s

@[simp] theorem prepared_executionEnv (s : State) (i : Nat) :
    (prepared s i).executionEnv = s.executionEnv := by unfold prepared; split <;> rfl
@[simp] theorem prepared_halt (s : State) (i : Nat) :
    (prepared s i).halt = s.halt := by unfold prepared; split <;> rfl
@[simp] theorem prepared_callStack (s : State) (i : Nat) :
    (prepared s i).callStack = s.callStack := by unfold prepared; split <;> rfl

theorem prepared_word_above (s : State) (i address : Nat) (ha : 32 ≤ address) :
    MachineState.readWord (prepared s i).memory address = MachineState.readWord s.memory address := by
  unfold prepared
  split
  · exact PrefixStateMemory.copied_word_above _ _ ha
  · rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
