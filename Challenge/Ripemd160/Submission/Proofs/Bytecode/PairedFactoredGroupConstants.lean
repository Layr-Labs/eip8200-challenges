import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache

set_option warningAsError true

/-! Closed materialization of the two generic RIPEMD group constants.
The execution contracts quantify arbitrary stacks and states; no hash-word
normalization or input-specific hypothesis is used. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedFactoredGroupConstants

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate

theorem upper_value :
    UInt256.shiftLeft (UInt256.ofNat 0x50a28be6) (UInt256.ofNat 128) =
      UInt256.ofNat 460344169260758029377710773882198039553172832256 := by decide

#print axioms upper_value

theorem mixed_value :
    UInt256.lor (UInt256.ofNat 0x5a827999)
      (UInt256.shiftLeft (UInt256.ofNat 0x5c4dd124) (UInt256.ofNat 128)) =
      UInt256.ofNat 526962527014005041256681316140890030896371104153 := by decide

#print axioms mixed_value

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Word.ofNat_add_mod]

private theorem add_eq_hadd (a b : UInt256) : UInt256.add a b = a + b := rfl

def upperTemplate : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0x50a28be6), .push ⟨1, by decide⟩ 128, .op .SHL]

/-- Construct the group-16 constant from two32-bit halves. -/
def replaceTemplate : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .POP,
   .push ⟨20, by decide⟩ (UInt256.ofNat 526962527014005041256681316140890030896371104153)]

theorem run_upperTemplate (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq upperTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc upperTemplate
        stack := UInt256.ofNat 460344169260758029377710773882198039553172832256 :: rho} := by
  have hzero : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 2) : rho.length + n < 1024 := by omega
  simp [upperTemplate, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, hrun, hzero, hcap, List.length_cons, Nat.add_assoc,
    Word.literal_eq_ofNat, upper_value, UInt256.succ, add_eq_hadd, word_add_ofNat_assoc]

#print axioms run_upperTemplate

theorem run_replaceTemplate (s : State) (pc value discarded : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq replaceTemplate {s with pc := pc, stack := value :: discarded :: rho} =
      some {s with
        pc := pcAfter pc replaceTemplate
        stack := UInt256.ofNat 526962527014005041256681316140890030896371104153 :: value :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 3) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [replaceTemplate,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    add_eq_hadd, word_add_ofNat_assoc]

#print axioms run_replaceTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedFactoredGroupConstants
