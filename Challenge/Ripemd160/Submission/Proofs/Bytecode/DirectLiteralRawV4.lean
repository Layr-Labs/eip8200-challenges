import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralRawV4
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DirectLiteralModel
private theorem hadd_eq (a b : UInt256) : a+b = UInt256.add a b := rfl
private theorem hsub_eq (a b : UInt256) : a-b = UInt256.sub a b := rfl
private theorem hmul_eq (a b : UInt256) : a*b = UInt256.mul a b := rfl

def startTemplate : List Instr := [.push ⟨0, by decide⟩ 0]
def cmpTemplate (k : Nat) : List Instr := [
  .push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt k),
  .push ⟨if k = 0 then 0 else if k < 8 then 1 else 2, by split <;> (try split) <;> decide⟩ (UInt256.ofNat (32*k)),
  .op .CALLDATALOAD, .op .XOR]
def orTemplate : List Instr := [.op .OR]
def branchTemplate (k : Nat) : List Instr := [
  .push ⟨if k < 7 then 1 else 2, by split <;> decide⟩ (UInt256.ofNat (32*k+33)),
  .op .CALLDATASIZE, .op .LT,
  .push ⟨2, by decide⟩ (UInt256.ofNat 6091), .op .JUMPI]
def dropOrTemplate : List Instr := [.op .OR]
def lastTemplate : List Instr := [.push ⟨2, by decide⟩ (UInt256.ofNat 1025)]
def tailTemplate : List Instr := [.op .JUMPDEST, .op .CALLDATASIZE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 248), .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 255), .op .AND, .op .SHR, .op .OR]
def resultTemplate : List Instr := [.push ⟨2, by decide⟩ (UInt256.ofNat 4565), .op .JUMPI]
def shifted (n : UInt256) (_bound : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 255) (UInt256.mul (UInt256.ofNat 248) n)

def firstCmp : List Instr := cmpTemplate 0
def firstBranch : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 33),
  .op .CALLDATASIZE, .op .LT,
  .push ⟨2, by decide⟩ (UInt256.ofNat 6108), .op .JUMPI]
def firstTail : List Instr := tailTemplate.take 7

theorem lor_zero (a : UInt256) : UInt256.lor a 0 = a := by
  apply Word.word_ext
  rw [Word.word_toNat_lor]
  exact Nat.or_zero _

theorem run_firstCmp (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq firstCmp {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc firstCmp, stack := diff s.executionEnv.calldata 0 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [firstCmp, cmpTemplate, diff, runInstrSeq,
    DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
    hcap, UInt256.succ, Instr.size, Nat.add_assoc, Word.word_toNat_ofNat,
    Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

theorem run_firstBranch (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 6108 = true) :
    runInstrSeq firstBranch {s with pc := pc, stack := rho} =
    some {s with pc := if (UInt256.ofNat s.executionEnv.calldata.size).toNat < 33 then UInt256.ofNat 6108 else pcAfter pc firstBranch, stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  by_cases hn : s.executionEnv.calldata.size % 2^256 < 33
  all_goals norm_num only [Nat.reducePow] at hn
  all_goals simp (discharger := omega) [firstBranch, hn, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hv, UInt256.isTrue, UInt256.lt]
  all_goals rfl

theorem run_firstTail (s : State) (pc d : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq firstTail {s with pc := pc, stack := d::rho} =
      some {s with pc := pcAfter pc firstTail, stack := UInt256.shiftRight d (shifted (UInt256.ofNat s.executionEnv.calldata.size) 0) :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [firstTail, tailTemplate, shifted, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  repeat first | apply And.intro | rfl

theorem run_start (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq startTemplate {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc startTemplate, stack := 0::rho} := by
  simp (discharger := omega) [startTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
    UInt256.succ, Instr.size, Word.word_toNat_ofNat, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  exact ⟨rfl,rfl⟩

theorem run_cmp (s : State) (pc : UInt256) (k : Nat) (hk : k < 32) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (cmpTemplate k) {s with pc := pc, stack := a::rho} =
      some {s with pc := pcAfter pc (cmpTemplate k), stack := diff s.executionEnv.calldata k :: a :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hoff : (UInt256.ofNat (32*k)).toNat = 32*k := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hk0 : k=0
  · subst k
    simp (discharger := omega) [cmpTemplate, diff, runInstrSeq, DataStepper.runInstr, pcAfter,
      hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
      hoff, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
    exact ⟨rfl,rfl⟩
  by_cases hk8 : k<8
  all_goals simp (discharger := omega) [cmpTemplate, hk0, hk8, diff, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    hoff, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  all_goals repeat first | apply And.intro | rfl

theorem run_or (s : State) (pc : UInt256) (d a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq orTemplate {s with pc := pc, stack := d::a::rho} =
      some {s with pc := pcAfter pc orTemplate, stack := UInt256.lor d a :: rho} := by
  simp (discharger := omega) [orTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
    UInt256.succ, Instr.size, Nat.add_assoc, show rho.length+2<1024 by omega]
  rfl

theorem run_branch (s : State) (pc : UInt256) (k : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 6091 = true) :
    runInstrSeq (branchTemplate k) {s with pc := pc, stack := rho} =
      some {s with pc := if (UInt256.ofNat s.executionEnv.calldata.size).toNat < (UInt256.ofNat (32*k+33)).toNat
        then UInt256.ofNat 6091 else pcAfter pc (branchTemplate k), stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  by_cases hk8 : k<7
  all_goals by_cases hc : s.executionEnv.calldata.size % 2^256 < (32*k+33) % 2^256
  all_goals norm_num only [Nat.reducePow] at hc
  all_goals simp (discharger := omega) [branchTemplate, hk8, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    UInt256.lt, UInt256.isTrue, hv, Word.word_toNat_ofNat, hc, Word.literal_eq_ofNat,
    List.getElem?_cons_zero, List.exchange]
  all_goals rfl

theorem run_dropOr (s : State) (pc : UInt256) (d a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq dropOrTemplate {s with pc := pc, stack := d::a::rho} =
      some {s with pc := pcAfter pc dropOrTemplate, stack := UInt256.lor d a :: rho} := by
  simp (discharger := omega) [dropOrTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
    UInt256.succ, Instr.size, Nat.add_assoc, show rho.length+2<1024 by omega, show rho.length+3<1024 by omega]
  rfl

theorem run_last (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq lastTemplate {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc lastTemplate, stack := UInt256.ofNat 1025::rho} := by
  simp (discharger := omega) [lastTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
    UInt256.succ, Instr.size, Word.word_toNat_ofNat, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]

theorem run_tail (s : State) (pc : UInt256) (bound d a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq tailTemplate {s with pc := pc, stack := d::a::rho} =
      some {s with pc := pcAfter pc tailTemplate, stack := UInt256.lor (UInt256.shiftRight d (shifted (UInt256.ofNat s.executionEnv.calldata.size) bound)) a :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [tailTemplate, shifted, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

theorem run_result (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4565 = true) :
    runInstrSeq resultTemplate {s with pc := pc, stack := a::rho} =
      some {s with pc := if a.toNat = 0 then pcAfter pc resultTemplate else UInt256.ofNat 4565, stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  by_cases hz : a.toNat=0
  all_goals simp (discharger := omega) [resultTemplate, hz, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
    hcap, UInt256.succ, Instr.size, Nat.add_assoc, hv, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    UInt256.isTrue]
  all_goals rfl
#print axioms run_cmp
#print axioms run_branch
#print axioms run_tail
#print axioms run_result
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralRawV4
