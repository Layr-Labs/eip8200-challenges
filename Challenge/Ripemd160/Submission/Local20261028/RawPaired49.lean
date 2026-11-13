import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawPaired49
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Swap ⟨9, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨11, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨9, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op .OR,
    .op (.Dup ⟨13, by decide⟩),
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .push ⟨2, by decide⟩ (UInt256.ofNat 882),
    .op .MLOAD,
    .op .ADD,
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .MULMOD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Swap ⟨5, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op .JUMPDEST ]
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 3253).take 41 =
      PcEncoding.assembleBytes template := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (3200+53)).take 41 = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop50]
  decide +kernel
#print axioms exact_bytes

def inputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [x.v0,
    (UInt256.ofNat 475368975196266490007815979009),
    (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096),
    (UInt256.ofNat 45805601672572416830120737830960963807809187780213980),
    x.v4,
    (UInt256.ofNat 95780971281817308448866066055358605703522837925462015),
    (UInt256.ofNat 95780971281817308448866066055358605703522833630494720),
    x.v7,
    x.v8,
    (MachineState.readWord memory 604),
    x.v10,
    x.v11,
    (UInt256.ofNat 158456325065422163343096938498),
    (UInt256.ofNat 4294967295),
    (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096),
    (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928),
    (UInt256.ofNat 1109194275457955143345843994625),
    (UInt256.ofNat 475368975196266490007815979009),
    x.v18] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [(UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 158456325065422163343096938498) x.v8) (UInt256.ofNat 23))),
    (UInt256.ofNat 45805601672572416830120737830960963807809187780213980),
    x.v4,
    (UInt256.ofNat 95780971281817308448866066055358605703522837925462015),
    (UInt256.ofNat 95780971281817308448866066055358605703522833630494720),
    x.v7,
    (UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) (UInt256.add x.v7 (UInt256.shiftRight (UInt256.mulMod (UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) (UInt256.add (UInt256.ofNat 45805601672572416830120737830960963807809187780213980) (UInt256.add (MachineState.readWord memory 882) (UInt256.add (UInt256.xor (UInt256.land (UInt256.xor x.v0 (UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522833630494720) x.v8)) (UInt256.xor (UInt256.lor (UInt256.ofNat 95780971281817308448866066055358605703522833630494720) x.v8) x.v11)) x.v8) x.v10)))) (UInt256.ofNat 475368975196266490007815979009) (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096)) (UInt256.ofNat 20)))),
    (MachineState.readWord memory 604),
    x.v0,
    x.v11,
    (UInt256.ofNat 158456325065422163343096938498),
    (UInt256.ofNat 4294967295),
    (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096),
    (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928),
    (UInt256.ofNat 1109194275457955143345843994625),
    (UInt256.ofNat 475368975196266490007815979009),
    x.v18] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [(UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 158456325065422163343096938498) x.v8) (UInt256.ofNat 23))),
    (UInt256.ofNat 45805601672572416830120737830960963807809187780213980),
    x.v4,
    (UInt256.ofNat 95780971281817308448866066055358605703522837925462015),
    (UInt256.ofNat 95780971281817308448866066055358605703522833630494720),
    x.v7,
    (UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) (UInt256.add x.v7 (UInt256.shiftRight (UInt256.mulMod (UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) (UInt256.add (UInt256.ofNat 45805601672572416830120737830960963807809187780213980) (UInt256.add (MachineState.readWord memory 882) (UInt256.add (UInt256.xor (UInt256.land (UInt256.xor x.v0 (UInt256.land (UInt256.ofNat 95780971281817308448866066055358605703522833630494720) x.v8)) (UInt256.xor (UInt256.lor (UInt256.ofNat 95780971281817308448866066055358605703522833630494720) x.v8) x.v11)) x.v8) x.v10)))) (UInt256.ofNat 475368975196266490007815979009) (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096)) (UInt256.ofNat 20)))),
    (MachineState.readWord memory 604),
    x.v0,
    x.v11,
    (UInt256.ofNat 158456325065422163343096938498),
    (UInt256.ofNat 4294967295),
    (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096),
    (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928),
    (UInt256.ofNat 1109194275457955143345843994625),
    (UInt256.ofNat 475368975196266490007815979009),
    x.v18] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by rfl
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack s.memory x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 32) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.mulMod_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack s.memory x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc x rho hstack hrun hactive
#print axioms run_actual

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawPaired49
