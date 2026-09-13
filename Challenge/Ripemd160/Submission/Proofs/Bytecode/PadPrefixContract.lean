import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPadZeroMload
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixContract
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open AstraPadPrefixCanonical
/-- Exact canonical MLOAD contract: includes unchanged machine state. -/
def ZeroLoads (s : State) : Prop := ∀ j : Fin 61, j.val ∈ zeroPairPositions →
  MachineState.mload s.toMachineState (UInt256.ofNat (18*j.val)) = (UInt256.ofNat 0, s.toMachineState)
theorem from_pad (s : State) (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    ZeroLoads {s with memory := StaggerTablePad.resultMemory s.memory n} := by
  intro j hj
  exact mload_canonical_pad_zero s.toMachineState n hn j hj
theorem read_zero (s : State) (hz : ZeroLoads s) (j : Fin 61)
    (hj : j.val ∈ zeroPairPositions) :
    MachineState.readWord s.memory (18*j.val) = UInt256.ofNat 0 := by
  have h := congrArg Prod.fst (hz j hj)
  have ha : (UInt256.ofNat (18*j.val)).toNat = 18*j.val := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt]; have := j.isLt; omega
  simpa only [MachineState.mload, ha] using h
#print axioms from_pad
#print axioms read_zero
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixContract
