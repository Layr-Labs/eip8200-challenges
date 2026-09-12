import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-! Materialize the normal 16-bit endian mask directly; retain the 8-bit quotient.
The mask value, schedule memory, and input preconditions are unchanged.
The original rest < 1015 stack-capacity bound remains explicit. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.NormalLiteralMask16

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory PairedMask32Cache

theorem mask8_div :
    UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 257 = mask8 := by decide

#print axioms mask8_div

theorem mask16_div :
    UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 65537 = mask16 := by decide

#print axioms mask16_div

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Word.ofNat_add_mod]

private theorem add_ofNat_assoc (u : UInt256) (a b : Nat) :
    UInt256.add (UInt256.add u (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.add u (UInt256.ofNat (a + b)) := by
  exact word_add_ofNat_assoc u a b

private theorem add_ofNat_assoc_hAdd (u : UInt256) (a b : Nat) :
    (UInt256.add u (UInt256.ofNat a)) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  exact word_add_ofNat_assoc u a b

private theorem add_ofNat_assoc_add (u : UInt256) (a b : Nat) :
    UInt256.add (u + UInt256.ofNat a) (UInt256.ofNat b) =
      u + UInt256.ofNat (a + b) := by
  exact word_add_ofNat_assoc u a b

def cachedInitial : List Instr :=
  [op .JUMPDEST, .push ⟨4, by decide⟩ maskWord,
    push2 (UInt256.ofNat 257), .push 0 0, op .NOT, op .DIV,
    .push ⟨30, by decide⟩ mask16,
    .op (.Swap ⟨2, by decide⟩), dup1, op .MLOAD, swap1,
    push1 (UInt256.ofNat 32), op .ADD, op .MLOAD]

theorem run_cachedInitial (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015) (hrun : s.halt = .Running) :
    runInstrSeq cachedInitial (scheduleEntry s pc messageOffset returnPC rest) =
      some {s with
        pc := pcAfter pc cachedInitial
        stack := inputWord1 s messageOffset :: inputWord0 s messageOffset ::
          mask8 :: maskWord :: mask16 :: returnPC :: rest
        activeWords := loadedActiveWords s messageOffset} := by
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 = some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v,w] rho
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have h32 : UInt256.ofNat 32 + messageOffset = messageOffset + UInt256.ofNat 32 :=
    Word.word_add_comm _ _
  simp [cachedInitial, scheduleEntry, inputWord0, inputWord1,
    loadedActiveWords, activeAfterWord, op, push1, push2, push3, dup1, swap1,
    hzero, mask8_div, mask16_div,
    runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hswap1, hswap3, h32,
    word_add_assoc, Nat.add_assoc, State.activeWordsAfterUInt256,
    Word.word_toNat_ofNat, Word.ofNat_add_mod, UInt256.succ, Instr.size]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [word_add_ofNat_assoc]

#print axioms run_cachedInitial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.NormalLiteralMask16
