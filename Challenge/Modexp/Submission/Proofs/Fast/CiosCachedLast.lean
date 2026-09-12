import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

/-!
# The last second-loop cell consumes `mu`

The final reduction cell of a row (pc 4715) is the only one after which `mu` is dead; the row
tail used to drop it with `SWAP1 POP`.  Here the `MULMOD` reads copies of `x` and `mu`
(`DUP2 DUP5 MULMOD`) and `SWAP3 MUL SWAP2` then consumes both originals, so the cell leaves
`[carry, b_i]` and the tail starts directly with its stores.  The program has the same 32 bytes
and the same instruction count as `macFusedProgram`, stores the same word (`macSum`) at the
same address and leaves the same carry (`macCarry`).
-/

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

/-- `DUP2 DUP5 MULMOD SWAP3 MUL SWAP2`: high product from copies, low product from the originals. -/
def multiplyProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

/-- `DUP1 DUP4 GT SUB DUP2 DUP4 ADD`. -/
def headProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩), .op .ADD]

def memoryProgram (tl ts : UInt256) : List Instr :=
  [.push 3 tl, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩), .op .GT]

/-- `SWAP3 GT SUB ADD SUB`: the low product is subtracted last, consuming it. -/
def tailProgram : List Instr :=
  [.op (.Swap ⟨2, by decide⟩), .op .GT, .op .SUB, .op .ADD, .op .SUB]

def macLastProgram (tl ts : UInt256) : List Instr :=
  ((multiplyProgram ++ headProgram) ++ memoryProgram tl ts) ++ tailProgram

def l2LastProgram (w : Fin 33) (x tl ts : UInt256) : List Instr :=
  CiosCachedL2.loadProgram w x ++ macLastProgram tl ts

private theorem mul_comm' (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

private theorem add_sub_comm' (a e p : UInt256) : (a + e) - p = (a - p) + e := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_sub, Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub]
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have he : e.toNat < 2 ^ 256 := e.val.isLt
  have hp : p.toNat < 2 ^ 256 := p.val.isLt
  omega

theorem run_multiply (template : State) (pc x y c : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions multiplyProgram
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([UInt256.mulMod y x maxWord, c, y * x] ++ rest)) := by
  have hc3 : rest.length < 1021 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, multiplyProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc3, hc4, hc5, List.exchange]

theorem run_head (template : State) (pc mm c lo : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions headProgram (framed template pc ([mm, c, lo] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 7)
      ([lo + c, UInt256.lt mm lo - mm, c, lo] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, headProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_load_word (template : State) (pc sum borrow c lo tl : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords) :
    runInstructions [.push 3 tl, .op .MLOAD]
      (framed template pc ([sum, borrow, c, lo] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([MachineState.readWord template.memory tl.toNat, sum, borrow, c, lo] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hc4, hc5, State.activeWordsAfterUInt256, hload, Nat.add_assoc,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_form_sum (template : State) (pc t sum borrow c lo : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions [.op (.Dup ⟨1, by decide⟩), .op .ADD]
      (framed template pc ([t, sum, borrow, c, lo] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 2)
      ([sum + t, sum, borrow, c, lo] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.getElem?_cons_zero, List.getElem?_cons_succ, hc5, hc6, Nat.add_assoc,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_store_word (template : State) (pc value sum borrow c lo ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions [.op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE,
        .op (.Dup ⟨1, by decide⟩), .op .GT]
      (framed template pc ([value, sum, borrow, c, lo] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded value.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 7)
      ([UInt256.lt value sum, sum, borrow, c, lo] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.getElem?_cons_zero, List.getElem?_cons_succ, hc5, hc6, hc7, hrest, Nat.add_assoc,
    State.activeWordsAfterUInt256, hstore, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_memory (template : State) (pc sum borrow c lo tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (memoryProgram tl ts)
      (framed template pc ([sum, borrow, c, lo] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (sum + MachineState.readWord template.memory tl.toNat).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 14)
      ([UInt256.lt (sum + MachineState.readWord template.memory tl.toNat)
          sum, sum, borrow, c, lo] ++ rest)) := by
  have hl := run_load_word template pc sum borrow c lo tl rest hrest hload
  have hs := run_form_sum template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory tl.toNat) sum borrow c lo rest hrest
  have hw := run_store_word template ((pc + UInt256.ofNat 5) + UInt256.ofNat 2)
    (sum + MachineState.readWord template.memory tl.toNat)
    sum borrow c lo ts rest hrest hstore
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  have all := runInstructions_append_some _ _ _ _ _ both hw
  simpa only [memoryProgram, List.cons_append, List.nil_append, pc_add_add, Nat.reduceAdd] using all

theorem run_tail (template : State) (pc extra sum borrow c lo : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions tailProgram
      (framed template pc ([extra, sum, borrow, c, lo] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([((UInt256.gt c sum - borrow) + extra) - lo] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  simp (disch := omega) [runInstructions, tailProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc, List.exchange,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The last cell: same store and carry as `CiosCachedFused.run_fused`, but `y` (= `mu`)
is consumed. -/
theorem run_last (template : State) (pc x y c tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (macLastProgram tl ts)
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum x y (MachineState.readWord template.memory tl.toNat) c).toNat 32)
          ts.toNat }
      (pc + UInt256.ofNat 32)
      ([macCarry x y (MachineState.readWord template.memory tl.toNat) c] ++ rest)) := by
  let t := MachineState.readWord template.memory tl.toNat
  let mm := UInt256.mulMod y x maxWord
  let B := UInt256.lt mm (x * y) - mm
  let stored : State :=
    { template with
      memory := MachineState.writeBytes template.memory
        (Data.Bytes.natToBytesPadded ((x * y + c) + t).toNat 32) ts.toNat }
  have hm := run_multiply template pc x y c rest (by omega)
  rw [mul_comm' y x] at hm
  have hh := run_head template (advancePC 6 pc) mm c (x * y) rest hrest
  have hmem := run_memory template (advancePC 6 pc + UInt256.ofNat 7) (x * y + c) B c (x * y)
    tl ts rest hrest hload hstore
  have ht := run_tail stored ((advancePC 6 pc + UInt256.ofNat 7) + UInt256.ofNat 14)
    (UInt256.lt ((x * y + c) + t) (x * y + c)) (x * y + c) B c (x * y) rest hrest
  have all := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (runInstructions_append_some _ _ _ _ _ hm hh) hmem) ht
  have hc : ((UInt256.gt c (x * y + c) - B) + UInt256.lt ((x * y + c) + t) (x * y + c)) - x * y =
      macCarry x y t c := by
    rw [add_sub_comm']
    change partialCarry x y c + UInt256.lt ((x * y + c) + t) (x * y + c) = macCarry x y t c
    rw [Challenge.EvmProof.Word.word_add_comm (partialCarry x y c)]
    simpa only [UInt256.gt, UInt256.lt,
      Challenge.EvmProof.Word.word_add_comm (x * y + c) t] using carry_eq x y t c
  have hs : (x * y + c) + t = macSum x y t c := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact sum_eq x y t c
  have hpc : ((advancePC 6 pc + UInt256.ofNat 7) + UInt256.ofNat 14) + UInt256.ofNat 5 =
      pc + UInt256.ofNat 32 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  change runInstructions (macLastProgram tl ts) _ =
    some (framed stored _ ([((UInt256.gt c (x * y + c) - B) +
      UInt256.lt ((x * y + c) + t) (x * y + c)) - x * y] ++ rest)) at all
  rw [hc, hpc] at all
  simpa only [stored, t, hs] using all

/-- The frame after the last copy: `mu` is gone. -/
def lastState (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [(l2Step mem mu c0 n k).carry, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n k).memory }

/-- The last second-loop copy (cf. `CiosCachedL2.run_step`). -/
theorem run_stepLast (w : Fin 33) (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (x tl ts : UInt256)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 4160 + 32 * (n - 2 - k))
    (hts : ts.toNat = 4160 + 32 * (n - 1 - k))
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 168 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n)
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    runInstructions (l2LastProgram w x tl ts)
      (CiosCachedL2.state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (lastState template (pc + UInt256.ofNat (w.val + 35)) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (4160 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (4160 + 32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hM : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat x.toNat 32) =
      st.activeWords := by simpa only [st, hx] using hactM
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) =
      st.activeWords := by simpa only [st, htl] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat ts.toNat 32) =
      st.activeWords := by simpa only [st, hts] using hactW
  have hl := CiosCachedL2.run_load w st pc x (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hpush hM
  have hf := run_last st (pc + UInt256.ofNat (w.val + 3))
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry tl ts
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat (w.val + 3)) + UInt256.ofNat 32 =
      pc + UInt256.ofNat (w.val + 35) := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  simpa only [l2LastProgram, st, CiosCachedL2.state, lastState, framed, l2Step, hx, htl, hts, hpc,
    List.cons_append, List.nil_append] using hall

/-- On the row frame: the last copy of row `i` lands on the row tail frame (pc 4750). -/
theorem run_l2Last (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 168 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hn : 2 ≤ n) :
    runInstructions (l2LastProgram 0 0 4160 4192)
      (l2At 4715 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some (tailState s (l2Step mid mu c0 n (n-1)).memory
        (l2Step mid mu c0 n (n-1)).carry mu bi pb n i hd ent pdst ret rest) := by
  have h := run_stepLast 0 s (UInt256.ofNat 4715) mid bi mu c0 n (n-2) 0 4160 4192
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 4715 + UInt256.ofNat ((0 : Fin 33).val + 35) = UInt256.ofNat 4750 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, lastState, l2At,
    tailState] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast.run_l2Last
