import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralRawV4
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DirectLiteralModel DirectLiteralRawV4

def rev (input : ByteArray) (a : UInt256) : Nat → UInt256
  | 0 => a
  | k+1 => rev input (UInt256.lor (diff input k) a) k

theorem rev_eq (input : ByteArray) (a : UInt256) (k : Nat) :
    rev input a k = UInt256.lor a (full input k) := by
  induction k generalizing a with
  | zero => exact (lor_zero a).symm
  | succ k ih =>
    rw [rev, ih, full]
    apply Word.word_ext
    simp only [Word.word_toNat_lor, diff, Nat.mul_comm]
    ac_rfl

def shift (n : Nat) : Nat := (32*(last n+1)-n)*8

def tailValue (input : ByteArray) (n : Nat) : UInt256 :=
  UInt256.shiftRight (diff input (last n)) (UInt256.ofNat (shift n))

theorem rev_tail (input : ByteArray) (n : Nat) :
    rev input (tailValue input n) (last n) = result input n := rev_eq _ _ _

def shrTemplate (v : Nat) : List Instr :=
  if v = 0 then [] else [.push ⟨1, by decide⟩ (UInt256.ofNat v), .op .SHR]

def jumpTemplate (target : Nat) : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat target), .op .JUMP]

def dispatchTemplate : List Instr := [.op .PC,
  .push ⟨2, by decide⟩ (UInt256.ofNat 2047), .op .CALLDATASIZE,
  .push ⟨9, by decide⟩ (UInt256.ofNat 15965797757087053012), .op .DIV, .op .AND, .op .ADD, .op .JUMP]

private theorem hadd_eq (a b : UInt256) : a+b = UInt256.add a b := rfl
private theorem hdiv_eq (a b : UInt256) : a/b = UInt256.div a b := rfl

theorem run_cmp0 (s : State) (pc : UInt256) (k : Nat) (hk : k < 32) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (cmpTemplate k) {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc (cmpTemplate k), stack := diff s.executionEnv.calldata k :: rho} := by
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

private theorem shr_zero (a : UInt256) : UInt256.shiftRight a (UInt256.ofNat 0) = a := by
  apply Word.word_ext
  rw [Word.shiftRight_toNat a (by decide)]
  exact Nat.shiftRight_zero

theorem run_shr (s : State) (pc a : UInt256) (v : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (shrTemplate v) {s with pc := pc, stack := a::rho} =
      some {s with pc := pcAfter pc (shrTemplate v), stack := UInt256.shiftRight a (UInt256.ofNat v) :: rho} := by
  by_cases hv : v=0
  · subst v
    simp [shrTemplate, runInstrSeq, pcAfter, shr_zero]
  · simp (discharger := omega) [shrTemplate, hv, runInstrSeq, DataStepper.runInstr, pcAfter, hrun,
      UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat, show rho.length+1<1024 by omega, show rho.length+2<1024 by omega]
    repeat first | apply And.intro | rfl

theorem run_jd (s : State) (pc : UInt256) (rho : List UInt256) (hs : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq [.op .JUMPDEST] {s with pc:=pc, stack:=rho} =
      some {s with pc:=pcAfter pc [.op .JUMPDEST], stack:=rho} := by
  simp [runInstrSeq,DataStepper.runInstr,pcAfter,hrun,UInt256.succ,show rho.length<1024 by omega]
  rfl

theorem run_jump (s : State) (pc : UInt256) (target : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat target).toNat = true) :
    runInstrSeq (jumpTemplate target) {s with pc:=pc, stack:=rho} =
      some {s with pc:=UInt256.ofNat target, stack:=rho} := by
  simp only [Word.word_toNat_ofNat] at hv
  norm_num only [Nat.reducePow] at hv
  simp (discharger := omega) [jumpTemplate,runInstrSeq,DataStepper.runInstr,pcAfter,hrun,hv,
    UInt256.succ,Instr.size,Nat.add_assoc,Word.literal_eq_ofNat,show rho.length<1024 by omega,show rho.length+1<1024 by omega]


def target (n : Nat) : UInt256 :=
  UInt256.add (UInt256.land (UInt256.div (UInt256.ofNat 15965797757087053012) (UInt256.ofNat n)) (UInt256.ofNat 2047)) (UInt256.ofNat 4804)

theorem run_dispatch (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code (target s.executionEnv.calldata.size).toNat = true) :
    runInstrSeq dispatchTemplate {s with pc:=UInt256.ofNat 4804, stack:=rho} =
      some {s with pc:=target s.executionEnv.calldata.size, stack:=rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  unfold target at hv
  simp (discharger := omega) [dispatchTemplate,runInstrSeq,DataStepper.runInstr,pcAfter,hrun,
    target,UInt256.succ,Instr.size,Nat.add_assoc,Word.literal_eq_ofNat,
    show rho.length<1024 by omega,hcap, hadd_eq, hdiv_eq, hv]

#print axioms rev_tail
#print axioms run_cmp0
#print axioms run_shr
#print axioms run_jump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
