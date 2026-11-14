import Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.RecognizerLiteral
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode StackRoundTrace
private theorem value1 : UInt256.shiftLeft (UInt256.ofNat 7) (UInt256.ofNat 248) = ZeroTailModel.expectedLast 1 := by decide +kernel
private theorem value55 : UInt256.shiftLeft (UInt256.ofNat 2106602293574006206576636045388868799142805981471020402999296) (UInt256.ofNat 55) = ZeroTailModel.expectedLast 55 := by decide +kernel
private theorem value56 : UInt256.shiftLeft (UInt256.ofNat 1053301146787003103288318022694434399571402990735510201563648) (UInt256.ofNat 56) = ZeroTailModel.expectedLast 56 := by decide +kernel
private theorem value65 : UInt256.shiftLeft (UInt256.ofNat 71) (UInt256.ofNat 248) = ZeroTailModel.expectedLast 65 := by decide +kernel
private theorem value119 : UInt256.shiftLeft (UInt256.ofNat 24332155171934941907485064014255435932631616300185137378071861526528) (UInt256.ofNat 32) = ZeroTailModel.expectedLast 119 := by decide +kernel
private theorem msize1 : UInt256.ofNat (32 * (UInt256.ofNat 1).toNat) = UInt256.ofNat 32 := by decide
def template : Nat → List Instr
  | 1 => [.push ⟨1, by decide⟩ (UInt256.ofNat 7), .push ⟨1, by decide⟩ (UInt256.ofNat 248), .op .SHL]
  | 55 => [.push ⟨26, by decide⟩ (UInt256.ofNat 2106602293574006206576636045388868799142805981471020402999296), .op .CALLDATASIZE, .op .SHL]
  | 56 => [.push ⟨25, by decide⟩ (UInt256.ofNat 1053301146787003103288318022694434399571402990735510201563648), .op .CALLDATASIZE, .op .SHL]
  | 65 => [.push ⟨1, by decide⟩ (UInt256.ofNat 71), .push ⟨1, by decide⟩ (UInt256.ofNat 248), .op .SHL]
  | 119 => [.push ⟨28, by decide⟩ (UInt256.ofNat 24332155171934941907485064014255435932631616300185137378071861526528), .op .MSIZE, .op .SHL]
  | n => [.push ⟨32, by decide⟩ (ZeroTailModel.expectedLast n)]
theorem run (s : State) (pc : UInt256) (n : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hr : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1)
    (hsz : n = 55 ∨ n = 56 → s.executionEnv.calldata.size = n) :
    runInstrSeq (template n) {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc (template n), stack := ZeroTailModel.expectedLast n :: rho} := by
  have hcap (j : Nat) (hj : j ≤ 20) : rho.length+j < 1024 := by omega
  by_cases h1 : n=1
  · subst n
    simp [template, runInstrSeq, DataStepper.runInstr, pcAfter, hr, hcap,
      show rho.length < 1024 by omega, UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat, value1]
    all_goals rfl
  by_cases h55 : n=55
  · subst n
    simp [template, runInstrSeq, DataStepper.runInstr, pcAfter, hr, hcap,
      show rho.length < 1024 by omega, UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat,
      hsz (Or.inl rfl), value55]
    all_goals rfl
  by_cases h56 : n=56
  · subst n
    simp [template, runInstrSeq, DataStepper.runInstr, pcAfter, hr, hcap,
      show rho.length < 1024 by omega, UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat,
      hsz (Or.inr rfl), value56]
    all_goals rfl
  by_cases h65 : n=65
  · subst n
    simp [template, runInstrSeq, DataStepper.runInstr, pcAfter, hr, hcap,
      show rho.length < 1024 by omega, UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat, value65]
    all_goals rfl
  by_cases h119 : n=119
  · subst n
    simp [template, runInstrSeq, DataStepper.runInstr, pcAfter, hr, hcap,
      show rho.length < 1024 by omega, UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat,
      List.getElem?_cons_zero, MachineState.msize, ha, msize1, value119]
    all_goals rfl
  simp [template, h1, h55, h56, h65, h119, runInstrSeq, DataStepper.runInstr, pcAfter, hr,
    show rho.length < 1024 by omega, Instr.size]
#print axioms run
end RipemdSubmission20261101.RecognizerLiteral
