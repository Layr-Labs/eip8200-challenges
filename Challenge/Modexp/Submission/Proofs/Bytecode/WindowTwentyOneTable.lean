import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneStage

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

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
      List.replicate (15 - power) modulus ++ ([base, exponent] ++ rest))

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
  [.op (.Dup ⟨16 - power, by omega⟩), .op .MULMOD]

theorem run_multiply (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (hpower : 2 ≤ power) (hmax : power < 15)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (multiplyProgram power hpower)
      (state template pc base modulus exponent power rest) =
    some (framed template (advancePC 2 pc) base modulus (power + 1)
      (WindowMath.tableWord base modulus (power + 1) ::
        List.replicate (14 - power) modulus ++ ([base, exponent] ++ rest))) := by
  have hcopies : 15 - power = (14 - power) + 1 := by omega
  have hslot : 16 - power = (15 - power) + 1 := by omega
  have hbase :
      (WindowMath.tableWord base modulus power ::
        List.replicate (15 - power) modulus ++ ([base, exponent] ++ rest))[16 - power]? =
      some base := by
    simp only [List.cons_append]
    rw [hslot, List.getElem?_cons_succ,
      List.getElem?_append_right (by simp)]
    simp
  have hbase' :
      (WindowMath.tableWord base modulus power :: modulus ::
        (List.replicate (14 - power) modulus ++ base :: exponent :: rest))[16 - power]? =
      some base := by
    simpa only [hcopies, List.replicate_succ, List.cons_append, List.nil_append] using hbase
  have hnext : WindowMath.tableWord base modulus (power + 1) =
      UInt256.mulMod base (WindowMath.tableWord base modulus power) modulus := by
    rw [WindowMath.tableWord, if_neg (by omega), mulMod_comm]
  have hcap0 : 14 - power + (rest.length + 4) < 1024 := by omega
  have hcap1 : 14 - power + (rest.length + 5) < 1024 := by omega
  simp (disch := omega)
    [runInstructions, multiplyProgram, state, framed, Challenge.EvmProof.Stepper.runInstr,
    hbase', hcopies, List.replicate_succ, List.cons_append, List.nil_append,
    List.length_append, List.length_replicate, Nat.add_assoc,
    hcap0, hcap1, hnext, advancePC]

def updateProgram (power : Nat) (hpower : 2 ≤ power) (width : Fin 33) : List Instr :=
  multiplyProgram power hpower ++ storeProgram width (power + 1)

theorem run_update (template : State) (pc base modulus exponent : UInt256)
    (power : Nat) (hpower : 2 ≤ power) (hmax : power < 15)
    (width : Fin 33) (hwidth : 0 < width.val)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (updateProgram power hpower width)
      (state template pc base modulus exponent power rest) =
    some (state template (storePC width (advancePC 2 pc)) base modulus exponent
      (power + 1) rest) := by
  have hm := run_multiply template pc base modulus exponent power hpower hmax rest hrest
  have hs := run_store template (advancePC 2 pc) base modulus (power + 1) (by omega)
    width hwidth (List.replicate (14 - power) modulus ++ ([base, exponent] ++ rest))
    (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
  have both := runInstructions_append_some _ _ _ _ _ hm hs
  simpa only [updateProgram, state, List.cons_append,
    show 15 - (power + 1) = 14 - power by omega] using both

def lastUpdateProgram : List Instr :=
  multiplyProgram 14 (by decide) ++ lastStoreProgram 2 15

theorem run_last_update (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions lastUpdateProgram
      (state template pc base modulus exponent 14 rest) =
    some (framed template (lastStorePC 2 (advancePC 2 pc)) base modulus 16
      ([base, exponent] ++ rest)) := by
  have hm := run_multiply template pc base modulus exponent 14 (by decide) (by decide) rest hrest
  have hs := run_store_last template (advancePC 2 pc) base modulus 15 (by decide)
    2 (by decide) ([base, exponent] ++ rest) (by simp; omega)
  simp only [show 14 - 14 = 0 by decide, List.replicate_zero] at hm
  exact runInstructions_append_some _ _ _ _ _ hm hs

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable
