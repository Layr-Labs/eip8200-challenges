import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory

set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM

def Matched (input : ByteArray) : Prop :=
  MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0 ∧
  MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
instance (input : ByteArray) : Decidable (Matched input) := inferInstanceAs (Decidable (_ ∧ _))

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
