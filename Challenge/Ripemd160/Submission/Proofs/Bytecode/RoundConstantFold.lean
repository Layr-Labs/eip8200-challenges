import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundConstantFold
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
/-- Round-boundary keys, independent of calldata, memory and chaining state. -/
def before16 : UInt256 := UInt256.ofNat 34535016170389834383797866734609369064725060249452544
def after16 : UInt256 := UInt256.ofNat 34535016170389834383797866734609369064725061767952793
def before48 : UInt256 := UInt256.ofNat 45805601672572416830120737830960963807809187239029665
def after48 : UInt256 := UInt256.ofNat 45805601672572416830120737830960963807809187780213980

theorem key16 : UInt256.add (UInt256.ofNat 1518500249) before16 = after16 := by decide
theorem key48 : UInt256.add (UInt256.ofNat 541184315) before48 = after48 := by decide

def old16 : List Instr := [.push ⟨4, by decide⟩ (UInt256.ofNat 1518500249), .op .ADD]
def new16 : List Instr := [.op .POP, .push ⟨22, by decide⟩ after16]
def old48 : List Instr := [.push ⟨4, by decide⟩ (UInt256.ofNat 541184315), .op .ADD]
def new48 : List Instr := [.op .POP, .push ⟨22, by decide⟩ after48]

theorem old16_run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1000) (hr : s.halt = .Running) :
    runInstrSeq old16 {s with pc := pc, stack := before16 :: rho} =
      some {s with pc := (pc + UInt256.ofNat 5).add (UInt256.ofNat 1), stack := after16 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [old16, runInstrSeq, DataStepper.runInstr, hcap,
    hr, UInt256.succ, key16, key48, before16, before48, after16, after48, UInt256.add, Nat.add_assoc, show rho.length < 1024 by omega]

  decide

theorem new16_run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1000) (hr : s.halt = .Running) :
    runInstrSeq new16 {s with pc := pc, stack := before16 :: rho} =
      some {s with pc := pc.add (UInt256.ofNat 1) + UInt256.ofNat 23, stack := after16 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [new16, runInstrSeq, DataStepper.runInstr, hcap,
    hr, UInt256.succ, key16, key48, before16, before48, after16, after48, UInt256.add, Nat.add_assoc, show rho.length < 1024 by omega]

theorem old48_run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1000) (hr : s.halt = .Running) :
    runInstrSeq old48 {s with pc := pc, stack := before48 :: rho} =
      some {s with pc := (pc + UInt256.ofNat 5).add (UInt256.ofNat 1), stack := after48 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [old48, runInstrSeq, DataStepper.runInstr, hcap,
    hr, UInt256.succ, key16, key48, before16, before48, after16, after48, UInt256.add, Nat.add_assoc, show rho.length < 1024 by omega]

  decide

theorem new48_run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1000) (hr : s.halt = .Running) :
    runInstrSeq new48 {s with pc := pc, stack := before48 :: rho} =
      some {s with pc := pc.add (UInt256.ofNat 1) + UInt256.ofNat 23, stack := after48 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [new48, runInstrSeq, DataStepper.runInstr, hcap,
    hr, UInt256.succ, key16, key48, before16, before48, after16, after48, UInt256.add, Nat.add_assoc, show rho.length < 1024 by omega]

#print axioms old16_run
#print axioms new16_run
#print axioms old48_run
#print axioms new48_run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundConstantFold
