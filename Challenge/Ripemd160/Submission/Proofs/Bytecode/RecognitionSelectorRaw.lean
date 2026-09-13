import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

def prefixTemplate (table : UInt256) : List Instr :=
  [.push ⟨1, by decide⟩ 20, .push ⟨1, by decide⟩ 15,
   .op .CALLDATASIZE, .push ⟨3, by decide⟩ 16714936, .op .DIV, .op .AND,
   .push ⟨1, by decide⟩ 20, .op .MUL, .push ⟨2, by decide⟩ table,
   .op .ADD, .push ⟨1, by decide⟩ 12]

def selected (table : UInt256) (size : Nat) : UInt256 :=
  UInt256.add table (UInt256.mul 20 (UInt256.land (UInt256.div 16714936 (UInt256.ofNat size)) 15))

theorem run_prefix (s : State) (pc table : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1010) (hrun : s.halt = .Running) :
    runInstrSeq (prefixTemplate table) {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc (prefixTemplate table)
        stack := 12 :: selected table s.executionEnv.calldata.size :: 20 :: rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [prefixTemplate, selected, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

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
