import Challenge.Ripemd160.Submission.Proofs.Bytecode.NearDenseSelectorRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

abbrev prefixTemplate := NearDenseSelectorRaw.prefixTemplate
abbrev selected := NearDenseSelectorRaw.selected
abbrev run_prefix := NearDenseSelectorRaw.run_prefix

def finish : List Instr := [.push ⟨0, by decide⟩ 0, .op .RETURN]

def returned (s : State) (pc : UInt256) (rho : List UInt256) : State :=
  { s with
    pc := pc + UInt256.ofNat 1
    stack := rho
    activeWords := s.activeWordsAfterUInt256 0 32
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 32 }

theorem run_finish (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1010) (hrun : s.halt = .Running) :
    runInstrSeq finish {s with pc := pc, stack := 32 :: rho} =
      some (returned s pc rho) := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  simp (discharger := omega) [finish, returned, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hzero, State.activeWordsAfterUInt256, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

  all_goals rfl

#print axioms run_prefix
#print axioms run_finish

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
