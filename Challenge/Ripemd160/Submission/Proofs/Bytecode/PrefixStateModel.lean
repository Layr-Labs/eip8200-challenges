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

/-- The depth-3 rung additionally pins calldata words 4 and 5. -/
def Matched3 (input : ByteArray) : Prop :=
  MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4 ∧
  MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5

instance (input : ByteArray) : Decidable (Matched3 input) := inferInstanceAs (Decidable (_ ∧ _))

/-- The dispatcher consumes exactly two blocks at once when words 0..3 match
and word 4 or word 5 does not. -/
def double (input : ByteArray) : Bool :=
  decide (Matched input ∧ Matched2 input ∧ ¬ Matched3 input)

theorem double_iff (input : ByteArray) :
    double input = true ↔ Matched input ∧ Matched2 input ∧ ¬ Matched3 input := by
  simp [double]

/-- The dispatcher consumes three blocks at once exactly when all six words match. -/
def triple (input : ByteArray) : Bool :=
  decide (Matched input ∧ Matched2 input ∧ Matched3 input)

theorem triple_iff (input : ByteArray) :
    triple input = true ↔ Matched input ∧ Matched2 input ∧ Matched3 input := by
  simp [triple]

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
