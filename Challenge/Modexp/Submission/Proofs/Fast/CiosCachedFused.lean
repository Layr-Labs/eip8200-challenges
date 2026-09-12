import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

/-!
# The fused multiply-accumulate cell

`macFusedProgram` computes the same accumulated word and outgoing carry as
`macProductProgram ++ macFinishProgram` in one instruction fewer (26 bytes either way,
-3 gas per cell).  This file is the execution lemma for it.

**Provenance.** Ported from terrapinelf's promoted MODEXP submission
8c2efe8b-0254-3994-a953-9fdcd1730771 (public repo commit c8f510f, co-authors
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
  [.push 3 tl, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
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
    runInstructions [.push 3 tl, .op .MLOAD]
      (framed template pc ([sum, borrow, lo, c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
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
      (pc + UInt256.ofNat 14)
      ([UInt256.lt (sum + MachineState.readWord template.memory tl.toNat)
          sum, sum, borrow, lo, c, y] ++ rest)) := by
  have hl := run_load_word template pc sum borrow lo c y tl rest hrest hload
  have hs := run_form_sum template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory tl.toNat) sum borrow lo c y rest hrest
  have hw := run_store_word template ((pc + UInt256.ofNat 5) + UInt256.ofNat 2)
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
      (pc + UInt256.ofNat 26)
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
  have ht := run_tail stored ((pc + UInt256.ofNat 7) + UInt256.ofNat 14)
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
      (pc + UInt256.ofNat 32)
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
  have hpc : advancePC 6 pc + UInt256.ofNat 26 = pc + UInt256.ofNat 32 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [macFusedProgram, macProductProgram, L2.multiplyProgram, List.take,
    hpc] using both

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_fused
