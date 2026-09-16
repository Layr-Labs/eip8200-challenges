import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
structure Input where
  h0 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h4 : UInt256
  off : UInt256
  limit : UInt256
/-- The six round constants are resident in the persistent frame (pushed once at
entry), so the bootstrap only copies the chaining words and pushes the first right
round constant. -/
def template : List Instr := [.op .JUMPDEST]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.ofNat 158456325065422163343096938526),
    (UInt256.ofNat 4294967323),
    (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324124),
    (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284956),
    (UInt256.ofNat 1109194275457955143345843994653),
    (UInt256.ofNat 475368975196266490007815979037),
    x.h4,
    x.h3,
    x.h2,
    x.h1,
    x.h0,
    x.off,
    x.limit ] ++ rho
def outputStack (_memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 := inputStack x rho
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, outputStack,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual

theorem factorWord_eq : Paired144WordRound.factorPlusWord = UInt256.ofNat 158456325065422163343096938526 := by decide
theorem fusedMinus_eq : Paired144WordRound.fusedModulusWord 5 7 = UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324124 := by decide
theorem coefficient02_eq : Paired144WordRound.fusedCoefficientWord 0 2 = UInt256.ofNat 475368975196266490007815979037 := by decide
theorem coefficient03_eq : Paired144WordRound.fusedCoefficientWord 0 3 = UInt256.ofNat 1109194275457955143345843994653 := by decide
theorem coefficient30_eq : Paired144WordRound.fusedModulusWord 8 5 = UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284956 := by decide
#print axioms factorWord_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapRaw
