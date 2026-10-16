import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawTransition

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2HoistRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace J2Raw

private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

def prefixTemplate : List Instr := transitionTemplate.take 15

def mid (f : J2Raw.Frame) : J2Raw.Frame := { f with word := tw f.word }

def post (f : J2Raw.Frame) (stop : UInt256) : J2Raw.Frame :=
  { f with off := f.stop, stop := stop, full := UInt256.sub stop (UInt256.ofNat 32) }

def cleanupTemplate : List Instr := [
  .op .MSIZE, .op (.Dup ⟨1, by decide⟩), .op .SUB,
  .op (.Swap ⟨4, by decide⟩), .op .POP, .op (.Swap ⟨6, by decide⟩),
  .op (.Swap ⟨1, by decide⟩), .op .POP ]

def genericTemplate : List Instr := transitionTemplate.drop 15 ++ [.op .POP]

def branchTemplate : List Instr := [ .op .CALLDATASIZE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 16), .op .AND,
  .push ⟨2, by decide⟩ (UInt256.ofNat 5117), .op .JUMPI ]

def specialTemplate : List Instr := [.op .JUMPDEST, .op .CALLDATASIZE] ++
  cleanupTemplate ++ [.push ⟨2, by decide⟩ (UInt256.ofNat (blockPC 4)), .op .JUMP]

 theorem run_prefix (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc prefixTemplate, stack := frame (mid f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [prefixTemplate, transitionTemplate, mid, frame, c114, tw,
      runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
      List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
      signed_sentinel_div9, add_negative_eq_sub, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [signed_sentinel_div9, add_negative_eq_sub, hsub_eq, hadd_eq, hmul_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

 theorem run_generic (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq genericTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc genericTemplate, stack := frame (post f (emin f.stop f.len)) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [genericTemplate, transitionTemplate, post, frame, emin,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    MachineState.msize, hactive, ← hlen, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hadd_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.land_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

 theorem run_special (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (blockPC 4) = true) :
    runInstrSeq specialTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := UInt256.ofNat (blockPC 4), stack := frame (post f f.len) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hmod : blockPC 4 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = blockPC 4 := by decide
  simp (discharger := omega) [specialTemplate, cleanupTemplate, post, frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    MachineState.msize, hactive, ← hlen, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    hmod, hvalid]
  all_goals rfl

 theorem run_branch (s : State) (pc : UInt256) (stack : List UInt256)
    (hs : stack.length ≤ 1018) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5117 = true) :
    runInstrSeq branchTemplate {s with pc := pc, stack := stack} =
      some {s with pc := if UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat 16) = 0
        then pcAfter pc branchTemplate else UInt256.ofNat 5117, stack := stack} := by
  have hbase : stack.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 5) : stack.length + n < 1024 := by omega
  have hz : ∀ x : UInt256, x.toNat = 0 ↔ x = 0 := by
    intro x; constructor
    · intro h; apply Word.word_ext; exact h
    · rintro rfl; rfl
  by_cases hc : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat 16) = UInt256.ofNat 0
  all_goals simp (discharger := omega) [branchTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, Nat.add_assoc, hrun, hbase, hcap,
    hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_comm, hz, UInt256.isTrue, hc]
  all_goals rfl

#print axioms run_prefix
#print axioms run_generic
#print axioms run_special
#print axioms run_branch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2HoistRaw
