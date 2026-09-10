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

def upperTemplate : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0x50a28be6),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .SHL]

def replaceTemplate : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .POP,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x5c4dd124),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .SHL,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x5a827999), .op .OR]

theorem run_upperTemplate (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq upperTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc upperTemplate
        stack := UInt256.ofNat 460344169260758029377710773882198039553172832256 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 2) : rho.length + n < 1024 := by omega
  have hzero : rho.length < 1024 := by omega
  simp [upperTemplate, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, Nat.add_assoc, UInt256.succ, hrun, hzero, hcap, upper_value,
    word_add_ofNat_assoc]
  change (pc + UInt256.ofNat 7) + UInt256.ofNat 1 = pc + UInt256.ofNat 8
  exact word_add_ofNat_assoc pc 7 1

#print axioms run_upperTemplate

theorem run_replaceTemplate (s : State) (pc value discarded : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq replaceTemplate {s with pc := pc, stack := value :: discarded :: rho} =
      some {s with
        pc := pcAfter pc replaceTemplate
        stack := UInt256.ofNat 526962527014005041256681316140890030896371104153 :: value :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 3) : rho.length + n < 1024 := by omega
  have hswap (u v : UInt256) (rest : List UInt256) :
      (u :: v :: rest).exchange 0 1 = some (v :: u :: rest) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rest
  simp [replaceTemplate, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, Nat.add_assoc, UInt256.succ, hrun, hcap, hswap, mixed_value,
    word_add_ofNat_assoc]
  change (((((pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 7) +
    UInt256.ofNat 1) + UInt256.ofNat 5) + UInt256.ofNat 1 = pc + UInt256.ofNat 16
  simp only [word_add_ofNat_assoc]

#print axioms run_replaceTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedFactoredGroupConstants
