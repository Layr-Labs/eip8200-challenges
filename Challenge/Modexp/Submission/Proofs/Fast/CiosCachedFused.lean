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

/-- Public: the slot-zero reduction cell composes onto this directly, since the
artifact's narrowed address push makes its tail exactly `macFusedPostProgram`. -/
theorem run_post (template : State) (pc mm lo c y tl ts : UInt256)
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

private def memoryProgramW3 (tl ts : UInt256) : List Instr :=
  [.push 3 tl, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩), .op .GT]

private theorem postW3_eq (tl ts : UInt256) :
    macFusedPostProgramW3 tl ts = (headProgram ++ memoryProgramW3 tl ts) ++ tailProgram := rfl

private theorem run_load_wordW3 (template : State) (pc sum borrow lo c y tl : UInt256)
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

private theorem run_memoryW3 (template : State) (pc sum borrow lo c y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (memoryProgramW3 tl ts)
      (framed template pc ([sum, borrow, lo, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (sum + MachineState.readWord template.memory tl.toNat).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 14)
      ([UInt256.lt (sum + MachineState.readWord template.memory tl.toNat)
          sum, sum, borrow, lo, c, y] ++ rest)) := by
  have hl := run_load_wordW3 template pc sum borrow lo c y tl rest hrest hload
  have hs := run_form_sum template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory tl.toNat) sum borrow lo c y rest hrest
  have hw := run_store_word template ((pc + UInt256.ofNat 5) + UInt256.ofNat 2)
    (sum + MachineState.readWord template.memory tl.toNat)
    sum borrow lo c y ts rest hrest hstore
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  have all := runInstructions_append_some _ _ _ _ _ both hw
  simpa only [memoryProgramW3, List.cons_append, List.nil_append, pc_add_add, Nat.reduceAdd] using all

theorem run_postW3 (template : State) (pc mm lo c y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macFusedPostProgramW3 tl ts)
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
  have hm := run_memoryW3 template (pc + UInt256.ofNat 7)
    (lo + c) (UInt256.lt mm lo - mm) lo c y tl ts rest hrest hload hstore
  have ht := run_tail stored ((pc + UInt256.ofNat 7) + UInt256.ofNat 14)
    (UInt256.lt ((lo + c) + t) (lo + c)) (lo + c) (UInt256.lt mm lo - mm) lo c y rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hh hm
  have all := runInstructions_append_some _ _ _ _ _ both ht
  simpa only [postW3_eq, stored, t, pc_add_add, Nat.reduceAdd] using all

theorem run_fusedW3 (template : State) (pc x y c tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macFusedProgramW3 tl ts)
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
  have hp := run_postW3 template (advancePC 6 pc)
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
  change runInstructions (macFusedPostProgramW3 tl ts)
      (framed template (advancePC 6 pc)
        ([UInt256.mulMod y x maxWord, x * y, c, y] ++ rest)) = _ at hp
  change runInstructions (macFusedPostProgramW3 tl ts) _ =
    some (framed _ _ ([partialCarry x y c + _, y] ++ rest)) at hp
  rw [hc, hs] at hp
  have both := runInstructions_append_some _ _ _ _ _ hm hp
  have hpc : advancePC 6 pc + UInt256.ofNat 26 = pc + UInt256.ofNat 32 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [macFusedProgramW3, macProductProgram, L2.multiplyProgram, List.take,
    hpc] using both

/-! ## The known-zero incoming carry

Where the incoming carry `c` is already zero, `macFusedPostZeroProgram` replaces the
incoming-carry add `DUP4 ADD` by two `JUMPDEST`s (the identity), and the first carry test
`c > lo + c` (constantly zero) with its `DUP2 GT SWAP4` parking by `SWAP1 JUMPDEST JUMPDEST`;
the zero carry slot is consumed by the final `ADD`.  Same bytes and instruction count as
`macFusedPostProgram`, seven gas cheaper.  `run_fused_zero` has the *same* conclusion as
`run_fused`, only under the extra hypothesis `c = 0`, and is derived from `run_fused`. -/

private def headZeroProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩),
   .op .JUMPDEST, .op .JUMPDEST]

private def memoryZeroProgram (tl ts : UInt256) : List Instr :=
  [.push 2 tl, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE]

private def tailZeroProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .JUMPDEST, .op .JUMPDEST, .op .GT,
   .op .SUB, .op .SUB, .op .ADD]

private theorem post_zero_eq (tl ts : UInt256) :
    macFusedPostZeroProgram tl ts =
      (headZeroProgram ++ memoryZeroProgram tl ts) ++ tailZeroProgram := rfl

private theorem run_head_zero (template : State) (pc mm lo y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions headZeroProgram
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 7)
      ([lo, UInt256.lt mm lo - mm, lo, UInt256.ofNat 0, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, headZeroProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_store_only (template : State) (pc value sum borrow lo c y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions [.op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE]
      (framed template pc ([value, sum, borrow, lo, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded value.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 5)
      ([value, sum, borrow, lo, c, y] ++ rest)) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.getElem?_cons_zero, List.getElem?_cons_succ, hc6, hc7, hrest, Nat.add_assoc,
    State.activeWordsAfterUInt256, hstore,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_memory_zero (template : State) (pc sum borrow lo c y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (memoryZeroProgram tl ts)
      (framed template pc ([sum, borrow, lo, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (sum + MachineState.readWord template.memory tl.toNat).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 11)
      ([sum + MachineState.readWord template.memory tl.toNat,
          sum, borrow, lo, c, y] ++ rest)) := by
  have hl := run_load_word template pc sum borrow lo c y tl rest hrest hload
  have hs := run_form_sum template (pc + UInt256.ofNat 4)
    (MachineState.readWord template.memory tl.toNat) sum borrow lo c y rest hrest
  have hw := run_store_only template ((pc + UInt256.ofNat 4) + UInt256.ofNat 2)
    (sum + MachineState.readWord template.memory tl.toNat)
    sum borrow lo c y ts rest hrest hstore
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  have all := runInstructions_append_some _ _ _ _ _ both hw
  simpa only [memoryZeroProgram, List.cons_append, List.nil_append, pc_add_add,
    Nat.reduceAdd] using all

private theorem run_tail_zero (template : State) (pc value sum borrow lo c y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions tailZeroProgram
      (framed template pc ([value, sum, borrow, lo, c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 7)
      ([((UInt256.lt value sum - borrow) - lo) + c, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, tailZeroProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, List.exchange, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_post_zero (template : State) (pc mm lo y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macFusedPostZeroProgram tl ts)
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (lo + MachineState.readWord template.memory tl.toNat).toNat 32)
          ts.toNat }
      (pc + UInt256.ofNat 25)
      ([((UInt256.lt (lo + MachineState.readWord template.memory tl.toNat) lo -
          (UInt256.lt mm lo - mm)) - lo) + UInt256.ofNat 0, y] ++ rest)) := by
  let t := MachineState.readWord template.memory tl.toNat
  let stored : State :=
    { template with
      memory := MachineState.writeBytes template.memory
        (Data.Bytes.natToBytesPadded (lo + t).toNat 32) ts.toNat }
  have hh := run_head_zero template pc mm lo y rest hrest
  have hm := run_memory_zero template (pc + UInt256.ofNat 7)
    lo (UInt256.lt mm lo - mm) lo (UInt256.ofNat 0) y tl ts rest hrest hload hstore
  have ht := run_tail_zero stored ((pc + UInt256.ofNat 7) + UInt256.ofNat 11)
    (lo + t) lo (UInt256.lt mm lo - mm) lo (UInt256.ofNat 0) y rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hh hm
  have all := runInstructions_append_some _ _ _ _ _ both ht
  simpa only [post_zero_eq, stored, t, pc_add_add, Nat.reduceAdd] using all

private theorem word_add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat]
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  omega

private theorem gt_zero_left (a : UInt256) : UInt256.gt (UInt256.ofNat 0) a = UInt256.ofNat 0 := by
  unfold UInt256.gt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  simp

private theorem carry_zero_eq (b lo l : UInt256) :
    ((UInt256.ofNat 0 - b) - lo) + l = ((l - b) - lo) + UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  have hlo : lo.toNat < 2 ^ 256 := lo.val.isLt
  have hl : l.toNat < 2 ^ 256 := l.val.isLt
  omega

/-- The zero-carry post schedule runs exactly as the general one does on a zero-carry frame. -/
private theorem run_post_zero_eq (template : State) (pc mm lo y tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macFusedPostZeroProgram tl ts)
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) =
    runInstructions (macFusedPostProgram tl ts)
      (framed template pc ([mm, lo, UInt256.ofNat 0, y] ++ rest)) := by
  rw [run_post_zero template pc mm lo y tl ts rest hrest hload hstore,
    run_post template pc mm lo (UInt256.ofNat 0) y tl ts rest hrest hload hstore,
    gt_zero_left, carry_zero_eq]
  simp only [word_add_zero]

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
        rest hrest hload hstore]
  rw [key]
  exact run_fused template pc x y (UInt256.ofNat 0) tl ts rest hrest hload hstore

/-! ## The known-zero accumulator word (M9 block 0)

`macTopZeroProgram` (`CiosCachedPrograms`) is the row-head cell on `c = 0` *and* `t = 0`, run on
the frame `[maxWord, x, y]` (the zero carry already popped).  `run_top_zero` states its result in
the `run_fused` form at `c = t = 0`. -/

private theorem zero_add_word (a : UInt256) : UInt256.ofNat 0 + a = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat]
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  omega

private theorem add_zero_word (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat]
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  omega

private theorem gt_self_word (a : UInt256) : UInt256.gt a a = UInt256.ofNat 0 := by
  unfold UInt256.gt
  simp

private theorem gt_zero_left_word (a : UInt256) : UInt256.gt (UInt256.ofNat 0) a = UInt256.ofNat 0 := by
  unfold UInt256.gt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  simp

private theorem top_carry_eq (x y : UInt256) :
    ((UInt256.ofNat 0 - UInt256.lt (UInt256.mulMod y x maxWord) (x * y)) +
        UInt256.mulMod y x maxWord) - x * y =
      macCarry x y (UInt256.ofNat 0) (UInt256.ofNat 0) := by
  rw [← carry_eq x y (UInt256.ofNat 0) (UInt256.ofNat 0)]
  unfold partialCarry
  rw [add_zero_word, zero_add_word, gt_self_word, gt_zero_left_word, zero_add_word]
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have h1 : (UInt256.lt (UInt256.mulMod y x maxWord) (x * y)).toNat < 2 ^ 256 :=
    (UInt256.lt (UInt256.mulMod y x maxWord) (x * y)).val.isLt
  have h2 : (UInt256.mulMod y x maxWord).toNat < 2 ^ 256 := (UInt256.mulMod y x maxWord).val.isLt
  have h3 : (x * y).toNat < 2 ^ 256 := (x * y).val.isLt
  omega

private theorem top_sum_eq (x y : UInt256) :
    x * y = macSum x y (UInt256.ofNat 0) (UInt256.ofNat 0) := by
  unfold macSum
  rw [zero_add_word, zero_add_word]

private theorem run_top_product (template : State) (pc x y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions topProductProgram
      (framed template pc ([maxWord, x, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 6)
      ([UInt256.mulMod y x maxWord, x * y, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, topProductProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, List.exchange,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_top_store (template : State) (pc mm lo y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (topStoreProgram ts)
      (framed template pc ([mm, lo, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded lo.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 5)
      ([mm, lo, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, topStoreProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc,
    State.activeWordsAfterUInt256, hstore,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_top_carry (template : State) (pc mm lo y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions topCarryProgram
      (framed template pc ([mm, lo, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 9)
      ([((UInt256.ofNat 0 - UInt256.lt mm lo) + mm) - lo, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, topCarryProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_top_fill (template : State) (pc : UInt256) (stack : List UInt256)
    (hs : stack.length < 1024) :
    runInstructions topFillProgram (framed template pc stack) =
    some (framed template (pc + UInt256.ofNat 10) stack) := by
  simp [runInstructions, topFillProgram, framed, List.replicate, hs,
    Challenge.EvmProof.Stepper.runInstr,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- **Block-0 top cell.**  With both the incoming carry and the accumulator word known to be
zero, the cell stores `x * y` and leaves `mulHi x y` as the outgoing carry; the conclusion is
stated in the `run_fused` form at `c = t = 0`. -/
theorem run_top_zero (template : State) (pc x y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macTopZeroProgram ts)
      (framed template pc ([maxWord, x, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum x y (UInt256.ofNat 0) (UInt256.ofNat 0)).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 30)
      ([macCarry x y (UInt256.ofNat 0) (UInt256.ofNat 0), y] ++ rest)) := by
  let stored : State :=
    { template with
      memory := MachineState.writeBytes template.memory
        (Data.Bytes.natToBytesPadded (x * y).toNat 32) ts.toNat }
  have hp := run_top_product template pc x y rest hrest
  have hs := run_top_store template (pc + UInt256.ofNat 6)
    (UInt256.mulMod y x maxWord) (x * y) y ts rest hrest hstore
  have hc := run_top_carry stored ((pc + UInt256.ofNat 6) + UInt256.ofNat 5)
    (UInt256.mulMod y x maxWord) (x * y) y rest hrest
  have hf := run_top_fill stored (((pc + UInt256.ofNat 6) + UInt256.ofNat 5) + UInt256.ofNat 9)
    ([((UInt256.ofNat 0 - UInt256.lt (UInt256.mulMod y x maxWord) (x * y)) +
        UInt256.mulMod y x maxWord) - x * y, y] ++ rest) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have a1 := runInstructions_append_some _ _ _ _ _ hp hs
  have a2 := runInstructions_append_some _ _ _ _ _ a1 hc
  have a3 := runInstructions_append_some _ _ _ _ _ a2 hf
  rw [← top_carry_eq, ← top_sum_eq]
  simpa only [macTopZeroProgram, stored, pc_add_add, Nat.reduceAdd] using a3

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_fused
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_fused_zero
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_top_zero
