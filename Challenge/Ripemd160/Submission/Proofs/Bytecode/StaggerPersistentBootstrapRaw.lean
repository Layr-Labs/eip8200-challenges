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
def template : List Instr :=
  [ .op .JUMPDEST,
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
    .op (.Dup ⟨15, by decide⟩) ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.ofNat 20282409608374036907091774406720),
    (UInt256.ofNat 4294967295),
    (UInt256.ofNat 20282409603651670423942956318720),
    (UInt256.ofNat 20282409608374036906851256238088),
    (UInt256.ofNat 162259276866992295254539466964993),
    (UInt256.ofNat 81129638433496147627271880966145),
    x.h4, x.h1, x.h2, x.h3, x.h0, x.off, x.limit] ++ rho
def outputStack (_memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.h0,
    (UInt256.ofNat 1352829926),
    x.h1,
    x.h2,
    x.h3,
    x.h4,
    (UInt256.ofNat 20282409608374036907091774406720),
    (UInt256.ofNat 4294967295),
    (UInt256.ofNat 20282409603651670423942956318720),
    (UInt256.ofNat 20282409608374036906851256238088),
    (UInt256.ofNat 162259276866992295254539466964993),
    (UInt256.ofNat 81129638433496147627271880966145),
    x.h4,
    x.h1,
    x.h2,
    x.h3,
    x.h0,
    x.off,
    x.limit ] ++ rho
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

theorem factorWord_eq : Paired144WordRound.factorWord = UInt256.ofNat 20282409608374036907091774406720 := by decide
theorem compactMaskWord_eq : Paired144WordRound.compactMaskWord = UInt256.ofNat 20282409603651670423942956318720 := by decide
theorem coefficient02_eq : Paired144WordRound.coefficientWord 0 2 = UInt256.ofNat 81129638433496147627271880966145 := by decide
theorem coefficient03_eq : Paired144WordRound.coefficientWord 0 3 = UInt256.ofNat 162259276866992295254539466964993 := by decide
theorem coefficient30_eq : Paired144WordRound.coefficientWord 3 0 = UInt256.ofNat 20282409608374036906851256238088 := by decide
#print axioms factorWord_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapRaw
