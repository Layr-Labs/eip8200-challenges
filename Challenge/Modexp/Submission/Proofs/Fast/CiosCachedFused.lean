import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

/-!
# The fused multiply-accumulate cell

`macFusedProgram` computes the same accumulated word and outgoing carry as
`macProductProgram ++ macFinishProgram` in one instruction fewer (26 bytes either way,
-3 gas per cell).  This file is the execution lemma for it.

**Provenance.** Ported from terrapinelf's promoted MODEXP submission
8c2efe8b-254-4205-a953-9fdcd1730771 (public repo commit c8f510f, co-authors
terrapinelf, ercumentyildirim, Akashneelesh), file
`Challenge/Modexp/Submission/Proofs/Fast/CiosCachedFused.lean`, adapted to this
artifact's cell frame.  The arithmetic identities it uses (`carry_eq`, `sum_eq`,
`partialCarry`, `macSum`, `macCarry`) are this tree's own.
-/

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

private theorem add_comm (a b : UInt256) : a + b = b + a := by
  change UInt256.mk (a.val + b.val) = UInt256.mk (b.val + a.val)
  congr 1
  ac_rfl

private def headProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩), .op .ADD]

private def memoryProgram (tl ts : UInt256) : List Instr :=
  [.push 2 tl, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩), .op .GT]

private def tailProgram : List Instr :=
  [.op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB,
   .op .ADD]

private theorem post_eq (tl ts : UInt256) :
    macFusedPostProgram tl ts = (headProgram ++ memoryProgram tl ts) ++ tailProgram := rfl

private theorem run_head (template : State) (pc mm lo c y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions headProgram (framed template pc ([mm, lo, c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 7)
      ([lo + c, UInt256.lt mm lo - mm, lo, c, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  have hc := add_comm c lo
  simp (disch := omega) [runInstructions, headProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, hc, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_load_word (template : State) (pc sum borrow lo c y tl : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords) :
    runInstructions [.push 2 tl, .op .MLOAD]
      (framed template pc ([sum, borrow, lo, c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 4)
      ([MachineState.readWord template.memory tl.toNat, sum, borrow, lo, c, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hc5, hc6, State.activeWordsAfterUInt256, hload, Nat.add_assoc,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_form_sum (template : State) (pc t sum borrow lo c y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions [.op (.Dup ⟨1, by decide⟩), .op .ADD]
      (framed template pc ([t, sum, borrow, lo, c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 2)
      ([sum + t, sum, borrow, lo, c, y] ++ rest)) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.getElem?_cons_zero, List.getElem?_cons_succ, hc6, hc7, Nat.add_assoc,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_store_word (template : State) (pc value sum borrow lo c y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions [.op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE,
        .op (.Dup ⟨1, by decide⟩), .op .GT]
      (framed template pc ([value, sum, borrow, lo, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded value.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 7)
      ([UInt256.lt value sum, sum, borrow, lo, c, y] ++ rest)) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.getElem?_cons_zero, List.getElem?_cons_succ, hc6, hc7, hrest, Nat.add_assoc,
    State.activeWordsAfterUInt256, hstore, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_memory (template : State) (pc sum borrow lo c y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (memoryProgram tl ts)
      (framed template pc ([sum, borrow, lo, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (sum + MachineState.readWord template.memory tl.toNat).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 13)
      ([UInt256.lt (sum + MachineState.readWord template.memory tl.toNat)
          sum, sum, borrow, lo, c, y] ++ rest)) := by
  have hl := run_load_word template pc sum borrow lo c y tl rest hrest hload
  have hs := run_form_sum template (pc + UInt256.ofNat 4)
    (MachineState.readWord template.memory tl.toNat) sum borrow lo c y rest hrest
  have hw := run_store_word template ((pc + UInt256.ofNat 4) + UInt256.ofNat 2)
    (sum + MachineState.readWord template.memory tl.toNat)
    sum borrow lo c y ts rest hrest hstore
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  have all := runInstructions_append_some _ _ _ _ _ both hw
  simpa only [memoryProgram, List.cons_append, List.nil_append, pc_add_add, Nat.reduceAdd] using all

private theorem run_tail (template : State) (pc extra sum borrow lo c y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions tailProgram
      (framed template pc ([extra, sum, borrow, lo, c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([((UInt256.gt c sum - borrow) - lo) + extra, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, tailProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, List.exchange,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_post (template : State) (pc mm lo c y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macFusedPostProgram tl ts)
      (framed template pc ([mm, lo, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            ((lo + c) + MachineState.readWord template.memory tl.toNat).toNat 32)
          ts.toNat }
      (pc + UInt256.ofNat 25)
      ([((UInt256.gt c (lo + c) - (UInt256.lt mm lo - mm)) - lo) +
          UInt256.lt ((lo + c) + MachineState.readWord template.memory tl.toNat)
            (lo + c), y] ++ rest)) := by
  let t := MachineState.readWord template.memory tl.toNat
  let stored : State :=
    { template with
      memory := MachineState.writeBytes template.memory
        (Data.Bytes.natToBytesPadded ((lo + c) + t).toNat 32) ts.toNat }
  have hh := run_head template pc mm lo c y rest hrest
  have hm := run_memory template (pc + UInt256.ofNat 7)
    (lo + c) (UInt256.lt mm lo - mm) lo c y tl ts rest hrest hload hstore
  have ht := run_tail stored ((pc + UInt256.ofNat 7) + UInt256.ofNat 13)
    (UInt256.lt ((lo + c) + t) (lo + c)) (lo + c) (UInt256.lt mm lo - mm) lo c y rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hh hm
  have all := runInstructions_append_some _ _ _ _ _ both ht
  simpa only [post_eq, stored, t, pc_add_add, Nat.reduceAdd] using all

/-- An arbitrary-word multiply/accumulate, with the load preceding the store. -/
theorem run_fused (template : State) (pc x y c tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macFusedProgram tl ts)
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum x y (MachineState.readWord template.memory tl.toNat) c).toNat 32)
          ts.toNat }
      (pc + UInt256.ofNat 31)
      ([macCarry x y (MachineState.readWord template.memory tl.toNat) c, y] ++ rest)) := by
  have hm := L2.run_multiply template pc x y c rest (by omega)
  have hp := run_post template (advancePC 6 pc)
    (UInt256.mulMod y x maxWord) (x * y) c y tl ts rest hrest hload hstore
  have hc : partialCarry x y c +
      UInt256.lt ((x * y + c) + MachineState.readWord template.memory tl.toNat)
        (x * y + c) =
      macCarry x y (MachineState.readWord template.memory tl.toNat) c := by
    rw [add_comm (partialCarry x y c)]
    simpa only [UInt256.gt, UInt256.lt,
      add_comm (x * y + c) (MachineState.readWord template.memory tl.toNat)] using
      carry_eq x y (MachineState.readWord template.memory tl.toNat) c
  have hs : (x * y + c) + MachineState.readWord template.memory tl.toNat =
      macSum x y (MachineState.readWord template.memory tl.toNat) c := by
    rw [add_comm]
    exact sum_eq x y (MachineState.readWord template.memory tl.toNat) c
  change runInstructions (macFusedPostProgram tl ts)
      (framed template (advancePC 6 pc)
        ([UInt256.mulMod y x maxWord, x * y, c, y] ++ rest)) = _ at hp
  change runInstructions (macFusedPostProgram tl ts) _ =
    some (framed _ _ ([partialCarry x y c + _, y] ++ rest)) at hp
  rw [hc, hs] at hp
  have both := runInstructions_append_some _ _ _ _ _ hm hp
  have hpc : advancePC 6 pc + UInt256.ofNat 25 = pc + UInt256.ofNat 31 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [macFusedProgram, macProductProgram, L2.multiplyProgram, List.take,
    hpc] using both

/-! ## The known-zero incoming carry

`headProgram`'s sixth instruction is the `DUP4` that reproduces the cell's incoming carry `c`.
Where `c` is already zero, `PUSH0` produces the same word for one gas less.  Everything below
is that one substitution: `run_fused_zero` has the *same* conclusion as `run_fused`, only under
the extra hypothesis `c = 0`, and is derived from `run_fused` rather than reproved. -/

/-- `headProgram` with the incoming-carry `DUP4` and its `ADD` both DELETED (two bytes, moved into
the widened load below). -/
private def headZeroProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

/-- `memoryProgram` with the load's `PUSH2` widened to a `PUSH4` of the same value: it pushes the
same word, and a `PUSH4` at `pc` ends where a `PUSH2` at `pc + 2` ends. -/
private def memoryZeroProgram (tl ts : UInt256) : List Instr :=
  [.push 4 tl, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩), .op .GT]

private theorem post_zero_eq (tl ts : UInt256) :
    macFusedPostZeroProgram tl ts = (headZeroProgram ++ memoryZeroProgram tl ts) ++ tailProgram := rfl

/-- `a + 0 = a`, needed once: the deleted `ADD` is the one that added the zero carry. -/
private theorem add_zero' (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val + (UInt256.ofNat 0).val).val = a.toNat
  have h0 : (UInt256.ofNat 0).val = 0 := rfl
  rw [h0, _root_.add_zero]
  rfl

private theorem push0_ofNat : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide

/-- On a zero-carry frame the short head leaves the same word: the general head's `DUP4; ADD`
adds the zero slot to `lo`, which is `lo` again.  It leaves it TWO BYTES EARLIER, and the widened
load in `memoryZeroProgram` makes that up. -/
private theorem run_head_zero (template : State) (pc mm lo y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions headZeroProgram
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([lo + UInt256.ofNat 0, UInt256.lt mm lo - mm, lo, UInt256.ofNat 0, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  rw [add_zero' lo]
  simp (disch := omega) [runInstructions, headZeroProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, push0_ofNat, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The widened load: `memoryZeroProgram` at `pc` and `memoryProgram` at `pc + 2` are the same
run.  Both push `tl` and land at `pc + 5`; the remaining eight instructions are identical. -/
private theorem run_memory_zero_eq (template : State) (pc tl ts : UInt256) (st : List UInt256)
    (hst : st.length + 2 < 1024) :
    runInstructions (memoryZeroProgram tl ts) (framed template pc st) =
    runInstructions (memoryProgram tl ts) (framed template (pc + UInt256.ofNat 2) st) := by
  have h1 : st.length + 1 < 1024 := by omega
  have hlen : st.length < 1024 := by omega
  have hpc : pc + UInt256.ofNat 2 + UInt256.ofNat 3 = pc + UInt256.ofNat 5 := by
    rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have h4 : runInstructions [(.push 4 tl : Instr)] (framed template pc st) =
      some (framed template (pc + UInt256.ofNat 5) (tl :: st)) := by
    simp (disch := omega) [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hst, h1, hlen,
      succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod]
  have h2 : runInstructions [(.push 2 tl : Instr)] (framed template (pc + UInt256.ofNat 2) st) =
      some (framed template (pc + UInt256.ofNat 5) (tl :: st)) := by
    simp (disch := omega) [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hst, h1, hlen,
      succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, hpc]
  have hsplitZ : memoryZeroProgram tl ts = [(.push 4 tl : Instr)] ++ (memoryProgram tl ts).tail :=
    rfl
  have hsplit : memoryProgram tl ts = [(.push 2 tl : Instr)] ++ (memoryProgram tl ts).tail := rfl
  rw [hsplitZ]
  conv_rhs => rw [hsplit]
  simp only [runInstructions_append, h4, h2]

/-- The zero-carry post schedule runs exactly as the general one does. -/
private theorem run_post_zero_eq (template : State) (pc mm lo y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions (macFusedPostZeroProgram tl ts)
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) =
    runInstructions (macFusedPostProgram tl ts)
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) := by
  have hpc : pc + UInt256.ofNat 5 + UInt256.ofNat 2 = pc + UInt256.ofNat 7 := by
    rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  rw [post_eq, post_zero_eq]
  simp only [runInstructions_append]
  rw [run_head_zero template pc mm lo y rest hrest, run_head template pc mm lo (UInt256.ofNat 0) y
    rest hrest]
  simp only [Option.bind_some]
  rw [run_memory_zero_eq template (pc + UInt256.ofNat 5) tl ts
    ([lo + UInt256.ofNat 0, UInt256.lt mm lo - mm, lo, UInt256.ofNat 0, y] ++ rest)
    (by simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil]; omega),
    hpc]

/-- **The rider.**  Identical conclusion to `run_fused`, under `c = 0`. -/
theorem run_fused_zero (template : State) (pc x y c tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords)
    (hc : c = UInt256.ofNat 0) :
    runInstructions (macFusedZeroProgram tl ts)
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum x y (MachineState.readWord template.memory tl.toNat) c).toNat 32)
          ts.toNat }
      (pc + UInt256.ofNat 31)
      ([macCarry x y (MachineState.readWord template.memory tl.toNat) c, y] ++ rest)) := by
  subst hc
  have hm := L2.run_multiply template pc x y (UInt256.ofNat 0) rest (by omega)
  have hsplit (post : UInt256 → UInt256 → List Instr) :
      runInstructions (macProductProgram.take 6 ++ post tl ts)
        (framed template pc ([maxWord, x, UInt256.ofNat 0, y] ++ rest)) =
      runInstructions (post tl ts)
        (framed template (advancePC 6 pc)
          ([UInt256.mulMod y x maxWord, x * y, UInt256.ofNat 0, y] ++ rest)) := by
    rw [show macProductProgram.take 6 = L2.multiplyProgram from rfl,
      runInstructions_append, hm, Option.bind_some]
  have key : runInstructions (macFusedZeroProgram tl ts)
        (framed template pc ([maxWord, x, UInt256.ofNat 0, y] ++ rest)) =
      runInstructions (macFusedProgram tl ts)
        (framed template pc ([maxWord, x, UInt256.ofNat 0, y] ++ rest)) := by
    rw [show macFusedZeroProgram tl ts
          = macProductProgram.take 6 ++ macFusedPostZeroProgram tl ts from rfl,
      show macFusedProgram tl ts
          = macProductProgram.take 6 ++ macFusedPostProgram tl ts from rfl,
      hsplit macFusedPostZeroProgram, hsplit macFusedPostProgram,
      run_post_zero_eq template (advancePC 6 pc) (UInt256.mulMod y x maxWord) (x * y) y tl ts
        rest hrest]
  rw [key]
  exact run_fused template pc x y (UInt256.ofNat 0) tl ts rest hrest hload hstore

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_fused
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_fused_zero
