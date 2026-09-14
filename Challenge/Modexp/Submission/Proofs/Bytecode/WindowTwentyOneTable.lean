import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneStage
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

def framed (template : State) (pc base modulus : UInt256)
    (count : Nat) (stack : List UInt256) : State :=
  { template with
    pc := pc
    stack := stack
    memory := WindowTableMemory.tableMemoryThrough base modulus count
    activeWords := UInt256.ofNat count }

def storeProgram (width : Fin 33) (count : Nat) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push width (UInt256.ofNat (32 * count)), .op .MSTORE]

def storePC (width : Fin 33) (pc : UInt256) : UInt256 :=
  (pc.succ + UInt256.ofNat (width.val + 1)).succ

theorem run_store (template : State) (pc base modulus : UInt256)
    (count : Nat) (hcount : count < 16) (width : Fin 33) (hwidth : 0 < width.val)
    (tail : List UInt256) (hcap : tail.length + 3 < 1024) :
    runInstructions (storeProgram width count)
      (framed template pc base modulus count
        (WindowMath.tableWord base modulus count :: tail)) =
    some (framed template (storePC width pc) base modulus (count + 1)
      (WindowMath.tableWord base modulus count :: tail)) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoffsetWord : (UInt256.ofNat (32 * count)).toNat = 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hactive : MachineState.activeWordsAfter count (32 * count) 32 = count + 1 := by
    cases count with
    | zero => decide
    | succ count => exact WindowTableMemory.activeWordsAfter_table count
  simp [runInstructions, storeProgram, storePC, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap, hcap1, hcap2, show width.val ≠ 0 by omega,
    hcountWord, hoffsetWord, hactive, State.activeWordsAfterUInt256,
    WindowTableMemory.tableMemoryThrough_succ, WindowTableMemory.storeWord]

def state (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (rest : List UInt256) : State :=
  framed template pc base modulus (power + 1)
    (WindowMath.tableWord base modulus power ::
      List.replicate (14 - power) modulus ++ ([base, exponent] ++ rest))

/-- Only the final table store consumes the word that it writes. -/
def lastStoreProgram (width : Fin 33) (count : Nat) : List Instr :=
  [.push width (UInt256.ofNat (32 * count)), .op .MSTORE]

def lastStorePC (width : Fin 33) (pc : UInt256) : UInt256 :=
  (pc + UInt256.ofNat (width.val + 1)).succ

theorem run_store_last (template : State) (pc base modulus : UInt256)
    (count : Nat) (hcount : count < 16) (width : Fin 33) (hwidth : 0 < width.val)
    (tail : List UInt256) (hcap : tail.length + 2 < 1024) :
    runInstructions (lastStoreProgram width count)
      (framed template pc base modulus count
        (WindowMath.tableWord base modulus count :: tail)) =
    some (framed template (lastStorePC width pc) base modulus (count + 1) tail) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoffsetWord : (UInt256.ofNat (32 * count)).toNat = 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hactive : MachineState.activeWordsAfter count (32 * count) 32 = count + 1 := by
    cases count with
    | zero => decide
    | succ count => exact WindowTableMemory.activeWordsAfter_table count
  simp [runInstructions, lastStoreProgram, lastStorePC, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap, hcap1, show width.val ≠ 0 by omega,
    hcountWord, hoffsetWord, hactive, State.activeWordsAfterUInt256,
    WindowTableMemory.tableMemoryThrough_succ, WindowTableMemory.storeWord]

def multiplyProgram (power : Nat) (hpower : 2 ≤ power) : List Instr :=
  [.op (.Dup ⟨15 - power, by omega⟩), .op .MULMOD]

theorem run_multiply (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (hpower : 2 ≤ power) (hmax : power < 14)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (multiplyProgram power hpower)
      (state template pc base modulus exponent power rest) =
    some (framed template (advancePC 2 pc) base modulus (power + 1)
      (WindowMath.tableWord base modulus (power + 1) ::
        List.replicate (13 - power) modulus ++ ([base, exponent] ++ rest))) := by
  have hcopies : 14 - power = (13 - power) + 1 := by omega
  have hslot : 15 - power = (14 - power) + 1 := by omega
  have hbase :
      (WindowMath.tableWord base modulus power ::
        List.replicate (14 - power) modulus ++ ([base, exponent] ++ rest))[15 - power]? =
      some base := by
    simp only [List.cons_append]
    rw [hslot, List.getElem?_cons_succ,
      List.getElem?_append_right (by simp)]
    simp
  have hbase' :
      (WindowMath.tableWord base modulus power :: modulus ::
        (List.replicate (13 - power) modulus ++ base :: exponent :: rest))[15 - power]? =
      some base := by
    simpa only [hcopies, List.replicate_succ, List.cons_append, List.nil_append] using hbase
  have hnext : WindowMath.tableWord base modulus (power + 1) =
      UInt256.mulMod base (WindowMath.tableWord base modulus power) modulus := by
    rw [WindowMath.tableWord, if_neg (by omega), mulMod_comm]
  have hcap0 : 13 - power + (rest.length + 4) < 1024 := by omega
  have hcap1 : 13 - power + (rest.length + 5) < 1024 := by omega
  simp (disch := omega)
    [runInstructions, multiplyProgram, state, framed, Challenge.EvmProof.Stepper.runInstr,
    hbase', hcopies, List.replicate_succ, List.cons_append, List.nil_append,
    List.length_append, List.length_replicate, Nat.add_assoc,
    hcap0, hcap1, hnext, advancePC]

def updateProgram (power : Nat) (hpower : 2 ≤ power) (width : Fin 33) : List Instr :=
  multiplyProgram power hpower ++ storeProgram width (power + 1)

theorem run_update (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (hpower : 2 ≤ power) (hmax : power < 14)
    (width : Fin 33) (hwidth : 0 < width.val)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (updateProgram power hpower width)
      (state template pc base modulus exponent power rest) =
    some (state template (storePC width (advancePC 2 pc)) base modulus exponent
      (power + 1) rest) := by
  have hm := run_multiply template pc base modulus exponent power hpower hmax rest hrest
  have hs := run_store template (advancePC 2 pc) base modulus (power + 1) (by omega)
    width hwidth (List.replicate (13 - power) modulus ++ ([base, exponent] ++ rest))
    (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
  have both := runInstructions_append_some _ _ _ _ _ hm hs
  simpa only [updateProgram, state, List.cons_append,
    show 14 - (power + 1) = 13 - power by omega] using both

/-! ## `MSIZE`-addressed table stores

Every table store extends the active memory by exactly one word, so the store
address equals `MSIZE` at the store.  These programs replace the pushed address
constants; the symbolic runs use the `MSIZE`-extended evaluator. -/

def storeProgramM : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MSIZE, .op .MSTORE]

def storePCM (pc : UInt256) : UInt256 := pc.succ.succ.succ

theorem run_storeM (template : State) (pc base modulus : UInt256)
    (count : Nat) (hcount : count < 16)
    (tail : List UInt256) (hcap : tail.length + 3 < 1024) :
    runInstructionsX storeProgramM
      (framed template pc base modulus count
        (WindowMath.tableWord base modulus count :: tail)) =
    some (framed template (storePCM pc) base modulus (count + 1)
      (WindowMath.tableWord base modulus count :: tail)) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoffsetWord : (UInt256.ofNat (32 * count)).toNat = 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hactive : MachineState.activeWordsAfter count (32 * count) 32 = count + 1 := by
    cases count with
    | zero => decide
    | succ count => exact WindowTableMemory.activeWordsAfter_table count
  simp [runInstructionsX, runInstrX_msize, storeProgramM, storePCM, framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, hcap1, hcap2,
    hcountWord, hoffsetWord, hactive, State.activeWordsAfterUInt256,
    WindowTableMemory.tableMemoryThrough_succ, WindowTableMemory.storeWord]

def lastStoreProgramM : List Instr := [.op .MSIZE, .op .MSTORE]

def lastStorePCM (pc : UInt256) : UInt256 := pc.succ.succ

theorem run_store_lastM (template : State) (pc base modulus : UInt256)
    (count : Nat) (hcount : count < 16)
    (tail : List UInt256) (hcap : tail.length + 2 < 1024) :
    runInstructionsX lastStoreProgramM
      (framed template pc base modulus count
        (WindowMath.tableWord base modulus count :: tail)) =
    some (framed template (lastStorePCM pc) base modulus (count + 1) tail) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoffsetWord : (UInt256.ofNat (32 * count)).toNat = 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hactive : MachineState.activeWordsAfter count (32 * count) 32 = count + 1 := by
    cases count with
    | zero => decide
    | succ count => exact WindowTableMemory.activeWordsAfter_table count
  simp [runInstructionsX, runInstrX_msize, lastStoreProgramM, lastStorePCM, framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, hcap1,
    hcountWord, hoffsetWord, hactive, State.activeWordsAfterUInt256,
    WindowTableMemory.tableMemoryThrough_succ, WindowTableMemory.storeWord]

theorem hasMsize_multiply (power : Nat) (hpower : 2 ≤ power) :
    hasMsize (multiplyProgram power hpower) = false := by
  simp [multiplyProgram, hasMsize]

theorem run_multiplyX (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (hpower : 2 ≤ power) (hmax : power < 14)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX (multiplyProgram power hpower)
      (state template pc base modulus exponent power rest) =
    some (framed template (advancePC 2 pc) base modulus (power + 1)
      (WindowMath.tableWord base modulus (power + 1) ::
        List.replicate (13 - power) modulus ++ ([base, exponent] ++ rest))) := by
  rw [runInstructionsX_eq _ (hasMsize_multiply power hpower)]
  exact run_multiply template pc base modulus exponent power hpower hmax rest hrest

def updateProgramM (power : Nat) (hpower : 2 ≤ power) : List Instr :=
  multiplyProgram power hpower ++ storeProgramM

theorem run_updateM (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (hpower : 2 ≤ power) (hmax : power < 14)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX (updateProgramM power hpower)
      (state template pc base modulus exponent power rest) =
    some (state template (storePCM (advancePC 2 pc)) base modulus exponent
      (power + 1) rest) := by
  have hm := run_multiplyX template pc base modulus exponent power hpower hmax rest hrest
  have hs := run_storeM template (advancePC 2 pc) base modulus (power + 1) (by omega)
    (List.replicate (13 - power) modulus ++ ([base, exponent] ++ rest))
    (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
  have both := runInstructionsX_append_some _ _ _ _ _ hm hs
  simpa only [updateProgramM, state, List.cons_append,
    show 14 - (power + 1) = 13 - power by omega] using both

/-! ## The final table slot

At `power = 14` the staged modulus copies are exhausted, so the last update
carries no `DUP`: the bare `MULMOD` consumes the word it just built together
with the `base` and the `modulus` sitting directly beneath it.  That is exactly
why the prelude leaves `modulus` — not the exponent — in the frame's third
slot. -/

def lastUpdateProgramM : List Instr := [.op .MULMOD] ++ lastStoreProgramM

private theorem run_mulmod_last (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op .MULMOD]
      (state template pc base modulus modulus 14 rest) =
    some (framed template pc.succ base modulus 15
      (WindowMath.tableWord base modulus 15 :: rest)) := by
  have hnext : WindowMath.tableWord base modulus 15 =
      UInt256.mulMod (WindowMath.tableWord base modulus 14) base modulus := by
    rw [WindowMath.tableWord, if_neg (by decide)]
  simp [runInstructions, state, framed, Challenge.EvmProof.Stepper.runInstr,
    List.replicate_zero, List.nil_append, List.cons_append, hnext]
  omega

theorem run_last_updateM (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX lastUpdateProgramM
      (state template pc base modulus modulus 14 rest) =
    some (framed template (lastStorePCM pc.succ) base modulus 16 rest) := by
  have hm : runInstructionsX [.op .MULMOD]
      (state template pc base modulus modulus 14 rest) =
      some (framed template pc.succ base modulus 15
        (WindowMath.tableWord base modulus 15 :: rest)) := by
    rw [runInstructionsX_eq _ (by decide)]
    exact run_mulmod_last template pc base modulus rest hrest
  have hs := run_store_lastM template pc.succ base modulus 15 (by decide) rest (by omega)
  exact runInstructionsX_append_some _ _ _ _ _ hm hs

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable
