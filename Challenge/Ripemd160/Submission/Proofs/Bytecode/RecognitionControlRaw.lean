import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBodyRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionBodyRaw

private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply PairedLaneUInt256Bridge.bits_injective
  simp only [PairedLaneUInt256Bridge.bits_xor, BitVec.xor_comm]

def initTemplate : List Instr := [
  .op .JUMPDEST,
  .op .POP,
  .push ⟨1, by decide⟩ (UInt256.ofNat 255),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .NOT,
  .op .DIV,
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 7),
  .op .SHL,
  .op (.Dup ⟨0, by decide⟩),
  .op .NOT,
  .op (.Dup ⟨2, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 5),
  .op .SHL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 31),
  .op .NOT,
  .op .CALLDATASIZE,
  .op .AND,
  .push ⟨1, by decide⟩ (UInt256.ofNat 224),
  .push ⟨32, by decide⟩ (UInt256.ofNat 3244493450063667868678674439968361782956185527883176199882357678282131398018),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0)]

def initResult (size : Nat) : RecognitionBodyRaw.Frame :=
  ⟨0, 0, PatternedSwar.P, UInt256.ofNat 224,
    UInt256.land (UInt256.ofNat size) (UInt256.lnot (UInt256.ofNat 31))⟩

theorem run_init (s : State) (pc incoming : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq initTemplate {s with pc := pc, stack := incoming :: rho} =
      some {s with
        pc := pcAfter pc initTemplate
        stack := frame (initResult s.executionEnv.calldata.size) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hU : UInt256.div (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 255) = PatternedSwar.M := by decide
  have hH : UInt256.shiftLeft PatternedSwar.M (UInt256.ofNat 7) = PatternedSwar.m8 := by decide
  have hL : UInt256.lnot PatternedSwar.m8 = PatternedSwar.m7 := by decide
  have hC : UInt256.shiftLeft PatternedSwar.M (UInt256.ofNat 5) = c32 := by decide
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [initTemplate, initResult, frame, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hU, hH, hL, hC,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

def initBodyTemplate : List Instr := initTemplate.drop 2

theorem run_init_body (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq initBodyTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc initBodyTemplate
        stack := frame (initResult s.executionEnv.calldata.size) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hU : UInt256.div (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 255) = PatternedSwar.M := by decide
  have hH : UInt256.shiftLeft PatternedSwar.M (UInt256.ofNat 7) = PatternedSwar.m8 := by decide
  have hL : UInt256.lnot PatternedSwar.m8 = PatternedSwar.m7 := by decide
  have hC : UInt256.shiftLeft PatternedSwar.M (UInt256.ofNat 5) = c32 := by decide
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [initBodyTemplate, initTemplate, initResult, frame, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hU, hH, hL, hC,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

def partialTemplate : List Instr := [
  .op (.Dup ⟨1, by decide⟩),
  .op .CALLDATALOAD,
  .op (.Dup ⟨3, by decide⟩),
  .op .XOR,
  .op (.Dup ⟨2, by decide⟩),
  .op .CALLDATASIZE,
  .op .SUB,
  .push ⟨1, by decide⟩ (UInt256.ofNat 3),
  .op .SHL,
  .push ⟨2, by decide⟩ (UInt256.ofNat 256),
  .op .SUB,
  .op .SHR,
  .op .OR]

def partialResult (s : State) (f : RecognitionBodyRaw.Frame) : RecognitionBodyRaw.Frame :=
  { f with
    acc := UInt256.lor
      (UInt256.shiftRight
        (UInt256.xor f.word (MachineState.readWord s.executionEnv.calldata f.off.toNat))
        (UInt256.ofNat 256 - UInt256.shiftLeft
          (UInt256.ofNat s.executionEnv.calldata.size - f.off) (UInt256.ofNat 3))) f.acc }

theorem run_partial (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq partialTemplate {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc partialTemplate
        stack := frame (partialResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [partialTemplate, partialResult, frame, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

def testTemplate (dest : Nat) : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT,
   .push ⟨1, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_test_continue (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlt : f.off.toNat < f.stop.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (testTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with pc := UInt256.ofNat dest, stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [testTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, hlt, UInt256.isTrue, hvalid,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]

theorem run_test_exit (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hle : f.stop.toNat ≤ f.off.toNat) :
    runInstrSeq (testTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc (testTemplate dest)
        stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hnlt : ¬ f.off.toNat < f.stop.toNat := by omega
  simp (discharger := omega) [testTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, hnlt, UInt256.isTrue,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

#print axioms run_init
#print axioms run_init_body
#print axioms run_partial
#print axioms run_test_continue
#print axioms run_test_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlRaw
