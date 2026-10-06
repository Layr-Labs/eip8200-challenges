import Challenge.Modexp.Submission.Proofs.Fast.M9MacPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-!
# M9: execution of one straight MAC block, the exit and the E6 entry on any MAC state

The chain frame is `[carry, q, 2^256-1] ++ rest` (top first) over a `Monpro.MacState` (memory and running
carry), where `rest` carries the loop counter, the seventeen riding slots and the outer frame
throughout (`Shift.slotKState` shape).  A riding block reproduces its `-N` limb from a slot with
`DUP (d+1)`, duplicates the mask, and runs the already-proven fused multiply-accumulate
(`CiosCachedFused.run_fused`) on `t`, so it performs exactly one `SquareModel.l1StepOn` step and
restores the frame.  Block 7 keeps the staged `PUSH2 1280; MLOAD; DUP4` load.  This is the
`StagedOperandL1.run_l1`/`run_step` shape with the two `DUP`s in place of the staged load.

## Assumed from the tree (kernel/model layer; unchanged by the port)
* `Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused.run_fused (template : State) (pc x y c tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) (hload hstore : UInt256.ofNat (MachineState.activeWordsAfter
    template.activeWords.toNat tl.toNat 32) = template.activeWords) :
    runInstructions (macFusedProgram tl ts) (framed template pc ([maxWord, x, c, y] ++ rest)) = some (framed
    { template with memory := writeBytes template.memory (natToBytesPadded (macSum x y (readWord template.memory
    tl.toNat) c).toNat 32) ts.toNat } (pc + UInt256.ofNat 31) ([macCarry x y (readWord template.memory tl.toNat) c, y]
    ++ rest))` (`Proofs/Fast/CiosCachedFused.lean`), and `run_fused_zero` (same, with the incoming-carry
    `DUP4` replaced by `PUSH0`, on `m.carry = 0`).
* `Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore.framed (template : State) (pc : UInt256) (stack : List UInt256) : State`.
* `Challenge.Modexp.Submission.Proofs.Fast.Monpro.MacState` (fields `memory : ByteArray`, `carry : UInt256`),
  `Monpro.maxWord : UInt256` (= `UInt256.ofNat (2^256-1)`), `Monpro.macSum`, `Monpro.macCarry`,
  `Monpro.activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0) (hoff : off + sz ≤ 2816)
    (hact : 88 ≤ s.activeWords.toNat) : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) = s.activeWords`.
* `Challenge.Modexp.Submission.Proofs.Fast.SquareModel.l1StepOn (q : MacState) (bi : UInt256) (pa n j : Nat) : MacState`
  (`Proofs/Fast/SquareModel.lean`; reads `pa + 32(n-1-j)` and `2112 + 32(n-1-j)`, writes the latter).
* `Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel.runInstructions`, `runInstructions_append_some`,
  `succ_eq_add`, `word_add_assoc`; `Challenge.EvmProof.Word.ofNat_add_mod`; `Challenge.EvmProof.Stepper.runInstr`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.M9Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

/-- The chain frame `[carry, q, 2^256-1] ++ rest` over the MAC state `m`. -/
def chainState (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (rest : List UInt256) : State :=
  { template with pc := pc, stack := [m.carry, bi, maxWord] ++ rest, memory := m.memory }

/-- The section entry state: `q` above `rest`, memory `um`. -/
def setupState (template : State) (pc : UInt256) (um : ByteArray) (bi : UInt256)
    (rest : List UInt256) : State :=
  { template with pc := pc, stack := bi :: rest, memory := um }

theorem run_load (template : State) (pc a carry bi : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1014)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat a.toNat 32) = template.activeWords) :
    runInstructions (loadProgram a) (framed template pc ([carry, bi, maxWord] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([maxWord, MachineState.readWord template.memory a.toNat, carry, bi, maxWord] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp (disch := omega) [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.cons_append, List.nil_append,
    hc3, hc4, State.activeWordsAfterUInt256, hactive,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The riding two-`DUP` head: `DUP (d+1)` reproduces the `-N` limb from slot `rest[d-3]`,
`DUP4` lifts the mask. -/
theorem run_dupHead (template : State) (pc : UInt256) (d : Fin 16) (carry bi x : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd3 : 3 ≤ d.val) (_hin : d.val < 3 + rest.length)
    (hx : rest[d.val - 3]? = some x) :
    runInstructions [.op (.Dup { idx := d }), .op (.Dup ⟨3, by decide⟩)]
      (framed template pc ([carry, bi, maxWord] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 2)
      ([maxWord, x, carry, bi, maxWord] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hframe : (carry :: bi :: maxWord :: rest)[d.val]? = some x := by
    rw [show d.val = (d.val - 3) + 3 from by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hx
  simp only [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.cons_append, List.nil_append, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]
  rw [hframe]
  simp (disch := omega) [List.getElem?_cons_zero, List.getElem?_cons_succ,
    hc3, hc4, hc5, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

theorem run_rideHead (template : State) (pc : UInt256) (d : Fin 16) (carry bi x : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd3 : 3 ≤ d.val) (hd13 : d.val ≤ 13) (_hin : d.val < 3 + rest.length)
    (hx : rest[d.val - 3]? = some x) :
    runInstructions (rideHead d)
      (framed template pc ([carry, bi, maxWord] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 7)
      ([UInt256.mulMod bi x maxWord, x * bi, carry, bi, maxWord] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hframe0 : (carry :: bi :: maxWord :: rest)[d.val]? = some x := by
    rw [show d.val = (d.val - 3) + 3 from by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hx
  have hframe1 : ((x * bi) :: carry :: bi :: maxWord :: rest)[d.val + 1]? = some x := by
    rw [List.getElem?_cons_succ]
    exact hframe0
  have hframe2 : (maxWord :: (x * bi) :: carry :: bi :: maxWord :: rest)[d.val + 2]? = some x := by
    rw [show d.val + 2 = (d.val + 1) + 1 from rfl,
      List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hframe0
  unfold rideHead
  rw [dif_pos hd13]
  dsimp only [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.cons_append, List.nil_append]
  simp [List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.exchange, hframe0, hframe1, hframe2, hc3, hc4, hc5, hc6, hc7, hc8, Nat.add_assoc,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem add_comm_word (a b : UInt256) : a + b = b + a := by
  change UInt256.mk (a.val + b.val) = UInt256.mk (b.val + a.val)
  congr 1
  ac_rfl

/-- One straight block (no `JUMPDEST`, 33 bytes) whose `-N` limb rides in slot `rest[d-3]`,
which must agree with the `l1StepOn` read at `1280 + 32(n-1-j)`: limb step `j` of width `n`. -/
theorem run_ride (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (n j : Nat) (t : UInt256) (d : Fin 16)
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (x : UInt256) (hval : x = MachineState.readWord m.memory (1280 + 32 * (n - 1 - j)))
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd3 : 3 ≤ d.val) (hd13 : d.val ≤ 13) (hin : d.val < 3 + rest.length)
    (hx : rest[d.val - 3]? = some x)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n) :
    runInstructions (rideProgram d t) (chainState template pc m bi rest) =
    some (chainState template (pc + UInt256.ofNat 33) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  subst hval
  let x0 := MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := m.memory }
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hm := run_rideHead st pc d m.carry bi x0 rest hrest hd3 hd13 hin hx
  have hp := CiosCachedFused.run_postW3 st (pc + UInt256.ofNat 7)
    (UInt256.mulMod bi x0 maxWord) (x0 * bi) m.carry bi t t (maxWord :: rest)
    (by simp only [List.length_cons]; omega) hT hT
  have hc : partialCarry x0 bi m.carry +
      UInt256.lt ((x0 * bi + m.carry) + MachineState.readWord st.memory t.toNat)
        (x0 * bi + m.carry) =
      macCarry x0 bi (MachineState.readWord st.memory t.toNat) m.carry := by
    rw [add_comm_word (partialCarry x0 bi m.carry)]
    simpa only [UInt256.gt, UInt256.lt,
      add_comm_word (x0 * bi + m.carry) (MachineState.readWord st.memory t.toNat)] using
      carry_eq x0 bi (MachineState.readWord st.memory t.toNat) m.carry
  have hs : (x0 * bi + m.carry) + MachineState.readWord st.memory t.toNat =
      macSum x0 bi (MachineState.readWord st.memory t.toNat) m.carry := by
    rw [add_comm_word]
    exact sum_eq x0 bi (MachineState.readWord st.memory t.toNat) m.carry
  change runInstructions (CiosCached.macFusedPostProgramW3 t t) _ =
    some (framed _ _ ([partialCarry x0 bi m.carry + _, bi] ++ (maxWord :: rest))) at hp
  rw [hc, hs] at hp
  have both := runInstructions_append_some _ _ _ _ _ hm hp
  have hpc : (pc + UInt256.ofNat 7) + UInt256.ofNat 26 = pc + UInt256.ofNat 33 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [rideProgram, st, x0, chainState, framed, SquareModel.l1StepOn, ht, hpc,
    List.cons_append, List.nil_append] using both

/-- A head block with the riding limb (`JUMPDEST` included, 34 bytes). -/
theorem run_ride_head (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (n j : Nat) (t : UInt256) (d : Fin 16)
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (x : UInt256) (hval : x = MachineState.readWord m.memory (1280 + 32 * (n - 1 - j)))
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd3 : 3 ≤ d.val) (hd13 : d.val ≤ 13) (hin : d.val < 3 + rest.length)
    (hx : rest[d.val - 3]? = some x)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n) :
    runInstructions ([.op .JUMPDEST] ++ rideProgram d t) (chainState template pc m bi rest) =
    some (chainState template (pc + UInt256.ofNat 34) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  have hc : rest.length + 3 < 1024 := by omega
  have hin' : (d : Nat) < 3 + rest.length := hin
  have hjd : runInstructions [.op .JUMPDEST] (chainState template pc m bi rest) =
      some (chainState template (pc + UInt256.ofNat 1) m bi rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, chainState, hc, succ_eq_add]
  have hl := run_ride template (pc + UInt256.ofNat 1) m bi n j t d ht x hval rest hrest
    hd3 hd13 hin' hx hactive hn hj
  have h := runInstructions_append_some _ _ _ _ _ hjd hl
  have hpc : pc + UInt256.ofNat 1 + UInt256.ofNat 33 = pc + UInt256.ofNat 34 := by
    rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  rw [hpc] at h
  exact h

/-- Block 0's head on a zero incoming carry (`JUMPDEST` + riding limb + `PUSH0` schedule,
34 bytes). -/
theorem run_ride_zero_head (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (n j : Nat) (t : UInt256) (d : Fin 16)
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (x : UInt256) (hval : x = MachineState.readWord m.memory (1280 + 32 * (n - 1 - j)))
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd3 : 3 ≤ d.val) (hin : d.val < 3 + rest.length)
    (hx : rest[d.val - 3]? = some x)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n)
    (hcarry : m.carry = UInt256.ofNat 0) :
    runInstructions ([.op .JUMPDEST] ++ rideZeroProgram d t) (chainState template pc m bi rest) =
    some (chainState template (pc + UInt256.ofNat 34) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  subst hval
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := m.memory }
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hc : rest.length + 3 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST] (chainState template pc m bi rest) =
      some (chainState template (pc + UInt256.ofNat 1) m bi rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, chainState, hc, succ_eq_add]
  have hl : runInstructions [.op (.Dup { idx := d }), .op (.Dup ⟨3, by decide⟩)]
      (framed st (pc + UInt256.ofNat 1) ([m.carry, bi, maxWord] ++ rest)) =
      some (framed st (pc + UInt256.ofNat 1 + UInt256.ofNat 2)
      ([maxWord, MachineState.readWord m.memory (1280 + 32 * (n - 1 - j)), m.carry, bi, maxWord] ++ rest)) :=
    run_dupHead st (pc + UInt256.ofNat 1) d m.carry bi
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rest hrest hd3 hin hx
  have hf := CiosCachedFused.run_fused_zero st (pc + UInt256.ofNat 1 + UInt256.ofNat 2)
    (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) bi m.carry t t
    (maxWord :: rest) (by simp only [List.length_cons]; omega) hT hT hcarry
  have hall := runInstructions_append_some _ _ _ _ _ hjd
    (runInstructions_append_some _ _ _ _ _ hl hf)
  have hpc : pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 31 = pc + UInt256.ofNat 34 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [rideZeroProgram, st, chainState, framed, SquareModel.l1StepOn, ht, hpc,
    List.cons_append, List.nil_append] using hall

/-- The top-word riding head: `POP` the zero carry, `DUP (d+1)` reproduces the `-N` limb from
slot `rest[d-2]`, `DUP3` lifts the mask. -/
theorem run_popDupHead (template : State) (pc : UInt256) (d : Fin 16) (carry bi x : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd2 : 2 ≤ d.val) (_hin : d.val < 2 + rest.length)
    (hx : rest[d.val - 2]? = some x) :
    runInstructions [.op .POP, .op (.Dup { idx := d }), .op (.Dup ⟨2, by decide⟩)]
      (framed template pc ([carry, bi, maxWord] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 3)
      ([maxWord, x, bi, maxWord] ++ rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hframe : (bi :: maxWord :: rest)[d.val]? = some x := by
    rw [show d.val = (d.val - 2) + 2 from by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hx
  simp only [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.cons_append, List.nil_append, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]
  simp (disch := omega) [List.getElem?_cons_zero, List.getElem?_cons_succ, hframe,
    hc2, hc3, hc4, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_rideTopHead_state (template : State) (pc : UInt256) (d : Fin 16) (carry bi x : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd2 : 2 ≤ d.val) (_hin : d.val < 2 + rest.length)
    (hx : rest[d.val - 2]? = some x) (hd13 : d.val ≤ 13) :
    runInstructions (rideTopHead d)
      (framed template pc ([carry, bi, maxWord] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 8)
      ([UInt256.mulMod bi x maxWord, x * bi, bi, maxWord] ++ rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hframe0 : (bi :: maxWord :: rest)[d.val]? = some x := by
    rw [show d.val = (d.val - 2) + 2 from by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hx
  have hframe2 : (maxWord :: (x * bi) :: bi :: maxWord :: rest)[d.val + 2]? = some x := by
    rw [show d.val + 2 = (d.val + 1) + 1 from rfl,
      List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hframe0
  unfold rideTopHead
  rw [dif_pos hd13]
  dsimp only [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    List.cons_append, List.nil_append]
  simp [List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.exchange, hframe0, hframe2, hc2, hc3, hc4, hc5, hc6, hc7, hc8, Nat.add_assoc,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem sub_lt_eq (mm lo : UInt256) :
    (mm - UInt256.lt mm lo) - lo = ((UInt256.ofNat 0 - UInt256.lt mm lo) + mm) - lo := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have h1 : (UInt256.lt mm lo).toNat < 2 ^ 256 := (UInt256.lt mm lo).val.isLt
  have h2 : mm.toNat < 2 ^ 256 := mm.val.isLt
  have h3 : lo.toNat < 2 ^ 256 := lo.val.isLt
  omega

private theorem run_rideTopStore (template : State) (pc mm lo y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (rideTopStore ts)
      (framed template pc ([mm, lo, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded lo.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 19)
      ([mm, lo, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  dsimp only [runInstructions, rideTopStore, framed,
    Challenge.EvmProof.Stepper.runInstr, List.cons_append, List.nil_append]
  simp (disch := omega) [List.getElem?_cons_zero,
    List.getElem?_cons_succ, hcap, Nat.add_assoc,
    State.activeWordsAfterUInt256, hstore,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_rideTopCarry (template : State) (pc mm lo y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions rideTopCarry
      (framed template pc ([mm, lo, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 6)
      ([((UInt256.ofNat 0 - UInt256.lt mm lo) + mm) - lo, y] ++ rest)) := by
  have hcap (n : Nat) (hn : n ≤ 8) : rest.length + n < 1024 := by omega
  rw [← sub_lt_eq mm lo]
  dsimp only [runInstructions, rideTopCarry, framed,
    Challenge.EvmProof.Stepper.runInstr, List.cons_append, List.nil_append]
  simp (disch := omega) [List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.exchange, hcap, Nat.add_assoc, UInt256.gt, UInt256.lt,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_rideTopFill (template : State) (pc : UInt256) (stack : List UInt256)
    (_hs : stack.length < 1024) :
    runInstructions rideTopFill (framed template pc stack) =
    some (framed template pc stack) := by
  rfl

private theorem run_rideTopPost (template : State) (pc mm lo y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions ((rideTopStore ts ++ rideTopCarry) ++ rideTopFill)
      (framed template pc ([mm, lo, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded lo.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 25)
      ([((UInt256.ofNat 0 - UInt256.lt mm lo) + mm) - lo, y] ++ rest)) := by
  let stored : State :=
    { template with
      memory := MachineState.writeBytes template.memory
        (Data.Bytes.natToBytesPadded lo.toNat 32) ts.toNat }
  have hs := run_rideTopStore template pc mm lo y ts rest hrest hstore
  have hc := run_rideTopCarry stored (pc + UInt256.ofNat 19) mm lo y rest hrest
  have hf := run_rideTopFill stored ((pc + UInt256.ofNat 19) + UInt256.ofNat 6)
    ([((UInt256.ofNat 0 - UInt256.lt mm lo) + mm) - lo, y] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have a1 := runInstructions_append_some _ _ _ _ _ hs hc
  have a2 := runInstructions_append_some _ _ _ _ _ a1 hf
  have hpc : (pc + UInt256.ofNat 19) + UInt256.ofNat 6 = pc + UInt256.ofNat 25 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [stored, hpc] using a2

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
  rw [← CiosCachedMacCore.carry_eq x y (UInt256.ofNat 0) (UInt256.ofNat 0)]
  unfold CiosCachedMacCore.partialCarry
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

/-- Block 0's head on a zero incoming carry *and* a zero accumulator word (`JUMPDEST` +
`POP` + riding limb + `macTopZeroProgram`, 34 bytes). -/
theorem run_ride_top_head (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (n j : Nat) (t : UInt256) (d : Fin 16)
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (x : UInt256) (hval : x = MachineState.readWord m.memory (1280 + 32 * (n - 1 - j)))
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hd2 : 2 ≤ d.val) (hin : d.val < 2 + rest.length)
    (hx : rest[d.val - 2]? = some x) (hd13 : d.val ≤ 13)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n)
    (hcarry : m.carry = UInt256.ofNat 0)
    (htop : MachineState.readWord m.memory (2112 + 32 * (n - 1 - j)) = UInt256.ofNat 0) :
    runInstructions ([.op .JUMPDEST] ++ rideTopProgram d t) (chainState template pc m bi rest) =
    some (chainState template (pc + UInt256.ofNat 34) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  subst hval
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := m.memory }
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hc : rest.length + 3 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST] (chainState template pc m bi rest) =
      some (chainState template (pc + UInt256.ofNat 1) m bi rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, chainState, hc, succ_eq_add]
  have hth := run_rideTopHead_state st (pc + UInt256.ofNat 1) d m.carry bi
    (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rest hrest hd2 hin hx hd13
  have htp := run_rideTopPost st (pc + UInt256.ofNat 1 + UInt256.ofNat 8)
    (UInt256.mulMod bi (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) maxWord)
    (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j)) * bi) bi t
    (maxWord :: rest) (by simp only [List.length_cons]; omega) hT
  have hall := runInstructions_append_some _ _ _ _ _ hjd
    (runInstructions_append_some _ _ _ _ _ hth htp)
  rw [top_carry_eq, top_sum_eq] at hall
  have hpc : pc + UInt256.ofNat 1 + UInt256.ofNat 8 + UInt256.ofNat 25 = pc + UInt256.ofNat 34 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have hstep : SquareModel.l1StepOn m bi 1280 n j =
      { memory := MachineState.writeBytes m.memory
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) bi
              (UInt256.ofNat 0) (UInt256.ofNat 0)).toNat 32) (2112 + 32 * (n - 1 - j))
        carry := macCarry (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) bi
          (UInt256.ofNat 0) (UInt256.ofNat 0) } := by
    simp only [SquareModel.l1StepOn, htop, hcarry]
  rw [hstep]
  simpa only [rideTopProgram, st, chainState, framed, ht, hpc,
    List.cons_append, List.nil_append] using hall

/-- One straight block (no `JUMPDEST`) with the staged `MLOAD` load — block 7 only: the
immediates must be the `-N` limb `pa + 32(n-1-j)` and the `t` limb `2112 + 32(n-1-j)`. -/
theorem run_block (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (pa n j : Nat) (a t : UInt256)
    (ha : a.toNat = pa + 32 * (n - 1 - j)) (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (rest : List UInt256) (hrest : rest.length ≤ 1014)
    (hactive : 88 ≤ template.activeWords.toNat) (hpa : pa + 32 * n ≤ 2784)
    (hn : n ≤ 8) (hj : j < n) :
    runInstructions (blockProgram a t) (chainState template pc m bi rest) =
    some (chainState template (pc + UInt256.ofNat 36) (SquareModel.l1StepOn m bi pa n j) bi rest) := by
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := m.memory }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat a.toNat 32) =
      st.activeWords := by simpa only [st, ha] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hl := run_load st pc a m.carry bi rest hrest hA
  have hread : MachineState.readWord st.memory a.toNat =
      MachineState.readWord m.memory (pa + 32 * (n - 1 - j)) := by simp only [st, ha]
  rw [hread] at hl
  have hf := CiosCachedFused.run_fused st (pc + UInt256.ofNat 5)
    (MachineState.readWord m.memory (pa + 32 * (n - 1 - j))) bi m.carry t t
    (maxWord :: rest) (by simp only [List.length_cons]; omega) hT hT
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat 5) + UInt256.ofNat 31 = pc + UInt256.ofNat 36 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [blockProgram, st, chainState, framed, SquareModel.l1StepOn, ht, hpc,
    List.cons_append, List.nil_append] using hall

/-- An `l1StepOn` write (the `t` limb at `2112 + 32(n-1-j)`) is invisible below `0x840`. -/
theorem l1StepOn_readWord_below (q : Monpro.MacState) (bi : UInt256) (pa n j addr : Nat)
    (h : addr + 32 ≤ 2112) :
    MachineState.readWord (SquareModel.l1StepOn q bi pa n j).memory addr =
      MachineState.readWord q.memory addr := by
  simp only [SquareModel.l1StepOn]
  exact Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega))

theorem run_exit (template : State) (pc : UInt256) (m : MacState) (bi : UInt256)
    (rest : List UInt256) (_hrest : rest.length ≤ 1014) :
    runInstructions exitProgram (chainState template pc m bi rest) =
    some (chainState template pc m bi rest) := by
  rfl

private theorem notZero_maxWord : UInt256.lnot (⟨0⟩ : UInt256) = maxWord := by decide

private theorem notZeroOfNat_maxWord : UInt256.lnot (UInt256.ofNat 0) = maxWord := by decide

private theorem push0_ofNat : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide

/-- E6: from `[q] ++ rest` over `um` to the chain frame `[0, q, mask] ++ rest` at the entry
parked in the scratch slot, `rest[1]` (`rest` = counter :: slots ++ frame). -/
theorem run_entry (template : State) (pc : UInt256) (um : ByteArray) (bi : UInt256)
    (rest : List UInt256) (ent : Nat) (hrest : rest.length ≤ 1014)
    (hlen : 2 ≤ rest.length)
    (hslot : rest[1]? = some (UInt256.ofNat ent))
    (hent : ent < 2 ^ 256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code ent = true) :
    runInstructions entryProgram (setupState template pc um bi rest) =
    some (chainState template (UInt256.ofNat ent) ⟨um, UInt256.ofNat 0⟩ bi rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have htoNat : (UInt256.ofNat ent).toNat = ent := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hent]
  let st : State := { template with memory := um }
  have hs1 : runInstructions
      [.push 0 0, .op .NOT, .op (.Swap ⟨0, by decide⟩), .push 0 0]
      (setupState template pc um bi rest) =
      some (framed st (pc + UInt256.ofNat 4)
        (UInt256.ofNat 0 :: bi :: maxWord :: rest)) := by
    simp (disch := omega) [runInstructions, setupState, framed, st,
      Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4,
      List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.cons_append, List.nil_append, succ_eq_add, word_add_assoc,
      Challenge.EvmProof.Word.ofNat_add_mod, notZero_maxWord,
      notZeroOfNat_maxWord, push0_ofNat]
  have hs2 : runInstructions [.op (.Dup ⟨4, by decide⟩)]
      (framed st (pc + UInt256.ofNat 4) (UInt256.ofNat 0 :: bi :: maxWord :: rest)) =
      some (framed st (pc + UInt256.ofNat 5)
        (UInt256.ofNat ent :: UInt256.ofNat 0 :: bi :: maxWord :: rest)) := by
    have hc6 : rest.length + 6 < 1024 := by omega
    simp only [runInstructions, framed, st,
      Challenge.EvmProof.Stepper.runInstr, List.getElem?_cons_zero,
      List.getElem?_cons_succ, hc4, hc5, hc6, succ_eq_add,
      word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
    rw [hslot]
    simp (disch := omega)
    all_goals omega
  have hs3 : runInstructions [.op .JUMP]
      (framed st (pc + UInt256.ofNat 5)
        (UInt256.ofNat ent :: UInt256.ofNat 0 :: bi :: maxWord :: rest)) =
      some (framed st (UInt256.ofNat ent)
        (UInt256.ofNat 0 :: bi :: maxWord :: rest)) := by
    simp (disch := omega) [runInstructions, framed, st,
      Challenge.EvmProof.Stepper.runInstr, htoNat, hjump, hc3, succ_eq_add,
      word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
    all_goals omega
  have hall := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hs1 hs2) hs3
  simpa only [entryProgram, setupState, chainState, framed, st, List.cons_append,
    List.nil_append] using hall

end Challenge.Modexp.Submission.Proofs.Fast.M9Mac

#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_dupHead
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_ride
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_ride_head
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_ride_zero_head
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_block
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.l1StepOn_readWord_below
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_exit
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.run_entry
