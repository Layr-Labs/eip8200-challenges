import Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopy
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

/-!
# Paired-exponent precopy window route

Store `e >>> 3` at 512 and `e >>> 7` at 544. Their unaligned loads expose
all exponent nibbles except the final two; those come from the original exponent
retained below the modulus pool. Every memory lookup, including the first, has
one mask and no additional shift. The arithmetic window is unchanged.

The first row supplies digits 1,3,...,61; the second supplies 0,2,...,60.
Digits 62 and 63 use shifts 1 and 5 of the original exponent on the stack.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopyRoute

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneMsize

/-! ## Memory: two right-shifted rows above the table -/

def precopyMem (mem : ByteArray) (e : UInt256) : ByteArray :=
  WindowTableMemory.storeWord
    (WindowTableMemory.storeWord mem 512 (UInt256.shiftRight e (UInt256.ofNat 3)))
    544 (UInt256.shiftRight e (UInt256.ofNat 7))

theorem readWord_precopyMem_low (mem : ByteArray) (e : UInt256) (a : Nat) (ha : a + 32 ≤ 512) :
    MachineState.readWord (precopyMem mem e) a = MachineState.readWord mem a := by
  unfold precopyMem WindowTableMemory.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega)),
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega))]

private theorem land480_mod (x : Nat) : 480 &&& x = 480 &&& (x % 65536) := by
  rw [show (65536 : Nat) = 2 ^ 16 by decide, ← Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_comm x, ← Nat.and_assoc, show (480 &&& (2 ^ 16 - 1) : Nat) = 480 by decide]

private theorem window_low (bs : ByteArray) (off k : Nat) (v : UInt256) (hk : k ≤ 30)
    (hb30 : ((bs[off + k]?.getD 0).toNat) = v.toNat / 256 ^ (31 - k) % 256)
    (hb31 : ((bs[off + k + 1]?.getD 0).toNat) = v.toNat / 256 ^ (30 - k) % 256)
    (hoff : 30 ≤ off) :
    (MachineState.readWord bs (off - 30 + k)).toNat % 65536 = v.toNat / 256 ^ (30 - k) % 65536 := by
  rw [WindowCopyMemory.readWord_mod65536, show off - 30 + k + 30 = off + k by omega,
    show off - 30 + k + 31 = off + k + 1 by omega, hb30, hb31]
  have hp : 256 ^ (31 - k) = 256 ^ (30 - k) * 256 := by
    rw [show 31 - k = (30 - k) + 1 by omega, Nat.pow_succ]
  rw [hp, ← Nat.div_div_eq_div_mul]
  omega

/-- Row A (`e >>> 3` at 512), read at `482 + k`. -/
theorem land480_rowA (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 30) :
    UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) (482 + k)) =
      UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight e (UInt256.ofNat (243 - 8 * k))) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
    show (UInt256.ofNat 480).toNat = 480 from rfl,
    land480_mod (MachineState.readWord _ _).toNat, land480_mod (e.toNat >>> _)]
  congr 1
  have hw := window_low (precopyMem mem e) 512 k (UInt256.shiftRight e (UInt256.ofNat 3)) (by omega)
    (by
      unfold precopyMem
      rw [WindowCopyMemory.storeWord_getD_other _ _ _ _ (Or.inl (by omega)),
        WindowCopyMemory.storeWord_getD _ _ _ _ (by omega)])
    (by
      unfold precopyMem
      rw [WindowCopyMemory.storeWord_getD_other _ _ _ _ (Or.inl (by omega)), Nat.add_assoc,
        WindowCopyMemory.storeWord_getD _ _ _ _ (by omega), show 31 - (k + 1) = 30 - k by omega])
    (by omega)
  rw [show 512 - 30 + k = 482 + k by omega] at hw
  have hp : (2 : Nat) ^ 3 * 256 ^ (30 - k) = 2 ^ (243 - 8 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  rw [hw, Challenge.EvmProof.Word.shiftRight_toNat _ (by omega), Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, hp]

/-- Row B (`e >>> 7` at 544), read at `514 + k`. -/
theorem land480_rowB (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 30) :
    UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) (514 + k)) =
      UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight e (UInt256.ofNat (247 - 8 * k))) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
    show (UInt256.ofNat 480).toNat = 480 from rfl,
    land480_mod (MachineState.readWord _ _).toNat, land480_mod (e.toNat >>> _)]
  congr 1
  have hw := window_low (precopyMem mem e) 544 k (UInt256.shiftRight e (UInt256.ofNat 7)) (by omega)
    (by
      unfold precopyMem
      rw [WindowCopyMemory.storeWord_getD _ _ _ _ (by omega)])
    (by
      unfold precopyMem
      rw [Nat.add_assoc,
        WindowCopyMemory.storeWord_getD _ _ _ _ (by omega), show 31 - (k + 1) = 30 - k by omega])
    (by omega)
  rw [show 544 - 30 + k = 514 + k by omega] at hw
  have hp : (2 : Nat) ^ 7 * 256 ^ (30 - k) = 2 ^ (247 - 8 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  rw [hw, Challenge.EvmProof.Word.shiftRight_toNat _ (by omega), Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, hp]


private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

theorem odd_address (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 30) :
    (UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) (482+k))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat (1+2*k) := by
  rw [land480_rowA mem e k hk, land_comm]
  have h := WindowTwentyOneBits.lookupAddress_toNat e (243-8*k) (by omega)
  unfold WindowTwentyOneBits.lookupAddress at h
  rw [h]
  unfold WindowTwentyOneMath.nibble
  rw [Nat.shiftRight_eq_div_pow, show 243-8*k+5 = 4*(63-(1+2*k)) by omega, Nat.pow_mul]

theorem even_address (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 30) :
    (UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) (514+k))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat (2*k) := by
  rw [land480_rowB mem e k hk, land_comm]
  have h := WindowTwentyOneBits.lookupAddress_toNat e (247-8*k) (by omega)
  unfold WindowTwentyOneBits.lookupAddress at h
  rw [h]
  unfold WindowTwentyOneMath.nibble
  rw [Nat.shiftRight_eq_div_pow, show 247-8*k+5 = 4*(63-2*k) by omega, Nat.pow_mul]

theorem low_address (e : UInt256) (shift : Nat) (hshift : shift ≤ 5) :
    (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft e (UInt256.ofNat shift))).toNat =
      32 * ((e.toNat >>> (5-shift)) % 16) := by
  rw [Challenge.EvmProof.Word.word_toNat_land, show (UInt256.ofNat 480).toNat = 480 from rfl,
    WindowTwentyOneBits.shiftLeft_toNat_mod _ shift (by omega), Nat.and_comm,
    WindowTwentyOneBits.mask480_nat,
    WindowTwentyOneBits.shifted_nibble_nat e.toNat shift 5 hshift (by omega), Nat.shiftLeft_eq]
  norm_num only [Nat.reducePow]
  exact Nat.mul_comm _ 32


def laddr (i : Nat) : Nat := if i % 2 = 0 then 482 + i / 2 else 515 + i / 2

theorem laddr_bound (i : Nat) (hi : i < 61) : laddr i + 32 ≤ 576 := by
  unfold laddr
  split <;> omega

theorem precopy_address (mem : ByteArray) (e : UInt256) (i : Nat) (hi : i < 61) :
    (UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) (laddr i))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat (1+i) := by
  unfold laddr
  split
  next h =>
    have z := odd_address mem e (i/2) (by omega)
    simpa only [show 1+2*(i/2) = 1+i by omega] using z
  next h =>
    have z := even_address mem e (i/2+1) (by omega)
    simpa only [show 514+(i/2+1) = 515+i/2 by omega, show 2*(i/2+1) = 1+i by omega] using z

theorem first_address (mem : ByteArray) (e : UInt256) :
    (UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) 514)).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat 0 := by
  simpa using even_address mem e 0 (by omega)

theorem last_address (e : UInt256) :
    (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft e (UInt256.ofNat 5))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat 63 := by
  simpa [WindowTwentyOneMath.nibble] using low_address e 5 (by omega)

theorem advancePC_ofNat (count pc : Nat) :
    advancePC count (UInt256.ofNat pc) = UInt256.ofNat (pc + count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [advancePC, ih, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- 968..972: prepare the first row with `DUP2 PUSH1 3 SHR`. -/
def setupProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 1 3, .op .SHR]

theorem run_setup (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions setupProgram
      (WindowTwentyOneTable.framed template pc base modulus 16 (modulus :: exponent :: rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 4 pc) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3) :: modulus :: exponent :: rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, setupProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, word_add_assoc]

/-- 972..980: store the first row, derive `e >>> 7`, and store the second row. -/
def copyProgram : List Instr :=
  [.op .MSIZE, .op .MSTORE, .op (.Dup ⟨1, by decide⟩), .push 1 7, .op .SHR,
   .op .MSIZE, .op .MSTORE]

theorem run_copy (template : State) (pc base modulus exponent low : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 1000) :
    runInstructionsX copyProgram
      (WindowTwentyOneTable.framed template pc base modulus 16 (low :: modulus :: exponent :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 8 pc)
      (WindowTableMemory.storeWord
        (WindowTableMemory.storeWord (WindowTableMemory.tableMemory base modulus) 512 low)
        544 (UInt256.shiftRight exponent (UInt256.ofNat 7))) 18 (modulus :: exponent :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hcap4 : tail.length + 4 < 1024 := by omega
  have ha : (UInt256.ofNat 16).toNat = 16 := rfl
  have h1 : MachineState.activeWordsAfter 16 512 32 = 17 := by simp [MachineState.activeWordsAfter]
  have h1' : (UInt256.ofNat 17).toNat = 17 := rfl
  have h2 : MachineState.activeWordsAfter 17 544 32 = 18 := by simp [MachineState.activeWordsAfter]
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructionsX, runInstrX_msize, copyProgram,
    WindowTwentyOneTable.framed, WindowTwentyOneLookup.framed,
    WindowTableMemory.tableMemory, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    advancePC, succ_eq_add, word_add_assoc, hp2, Challenge.EvmProof.Word.literal_eq_ofNat]

/-- 980..1295: 315 `DUP1` instructions copy the top modulus. -/
def poolProgram : List Instr := WindowPrecopy.dupOnes 315

set_option maxRecDepth 4000 in
theorem run_pool (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (modulus : UInt256) (tail : List UInt256) (hcap : tail.length + 320 < 1024) :
    runInstructions poolProgram
      (WindowTwentyOneLookup.framed template pc mem active (modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 315 pc) mem active
      (List.replicate 315 modulus ++ modulus :: tail)) := by
  exact WindowPrecopy.run_dupOnes template mem active modulus 315 pc tail (by omega)

/-- 1295..1304: nibble 0 from the second exponent row. -/
def firstProgram : List Instr :=
  [.push 2 (UInt256.ofNat 514), .op .MLOAD,
   .push 2 (UInt256.ofNat 480), .op .AND, .op .MLOAD]

theorem run_first (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus : UInt256) (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : (UInt256.land (UInt256.ofNat 480)
      (MachineState.readWord mem 514)).toNat = 32 * index)
    (stack : List UInt256) (hcap : stack.length + 3 < 1024) :
    runInstructions firstProgram (WindowTwentyOneLookup.framed template pc mem 18 stack) =
    some (WindowTwentyOneLookup.framed template (advancePC 9 pc) mem 18
      (WindowMath.tableWord base modulus index :: stack)) := by
  have hcap0 : stack.length < 1024 := by omega
  have hcap1 : stack.length + 1 < 1024 := by omega
  have hcap2 : stack.length + 2 < 1024 := by omega
  have hl : (UInt256.ofNat 514).toNat = 514 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table index hindex
  have hactive' := WindowCopyMemory.activeWordsAfter_eighteen 514 (by omega)
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, firstProgram, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap0, hcap1, hcap2,
      hl, h18, haddress, hread, hactive, hactive',
      State.activeWordsAfterUInt256, advancePC, succ_eq_add, hp3, word_add_assoc]

/-- Windows for nibbles `1 + start`, ..., `start + count`, loads at `laddr start`, .... -/
def routeWindows (start : Nat) : Nat → List Instr
  | 0 => []
  | count + 1 =>
      WindowPrecopy.windowProgram (laddr start) ++ routeWindows (start + 1) count

theorem advance_succ_front (base modulus : UInt256) (exponent start count : Nat) (acc : UInt256) :
    WindowTwentyOneMath.advance base modulus exponent start (count + 1) acc =
      WindowTwentyOneMath.advance base modulus exponent (start + 1) count
        (WindowMath.nibbleWordStep modulus base acc (WindowTwentyOneMath.nibble exponent start)) := by
  rw [Nat.add_comm count 1, WindowTwentyOneMath.advance_add]
  rfl

theorem run_routeWindows (template : State) (mem : ByteArray) (base modulus exponent : UInt256)
    (below : List UInt256)
    (hread : ∀ index, index < 16 →
      MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : ∀ i, i < 61 →
      (UInt256.land (UInt256.ofNat 480)
        (MachineState.readWord mem (laddr i))).toNat =
        32 * WindowTwentyOneMath.nibble exponent.toNat (1 + i)) :
    ∀ (count start : Nat), start + count ≤ 61 →
    ∀ (pc accumulator : UInt256) (extra : Nat),
    5 * count + extra + below.length + 4 < 1024 →
    runInstructions (routeWindows start count)
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate (5 * count + extra) modulus ++ below)) =
    some (WindowTwentyOneLookup.framed template (advancePC (18 * count) pc) mem 18
      (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + start) count accumulator ::
        List.replicate extra modulus ++ below))
  | 0, start, _, pc, accumulator, extra, _ => by
      simp [routeWindows, runInstructions, advancePC, WindowTwentyOneMath.advance]
  | count + 1, start, hbound, pc, accumulator, extra, hcap => by
      have hd := WindowTwentyOneMath.nibble_lt exponent.toNat (1 + start)
      have hs := WindowPrecopy.run_window template pc mem base modulus accumulator below
        (5 * (count + 1) + extra) (by omega) (laddr start)
        (laddr_bound start (by omega))
        (WindowTwentyOneMath.nibble exponent.toNat (1 + start)) hd
        (hread _ hd) (haddress start (by omega)) (by omega)
      have hsub : 5 * (count + 1) + extra - 5 = 5 * count + extra := by omega
      rw [hsub] at hs
      have hi := run_routeWindows template mem base modulus exponent below hread haddress count
        (start + 1) (by omega) (advancePC 18 pc)
        (WindowMath.nibbleWordStep modulus base accumulator
          (WindowTwentyOneMath.nibble exponent.toNat (1 + start))) extra (by omega)
      have hall := runInstructions_append_some _ _ _ _ _ hs hi
      have hpc : advancePC (18 * count) (advancePC 18 pc) = advancePC (18 * (count + 1)) pc := by
        rw [← advancePC_add]
        congr 1
        omega
      rw [advance_succ_front, show 1 + start + 1 = 1 + (start + 1) by omega]
      simpa only [routeWindows, hpc] using hall

/-- Nibble 63 from the original exponent (fourth on the stack), then multiply. -/
def finalProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .push 1 (UInt256.ofNat 5), .op .SHL,
   .push 2 (UInt256.ofNat 480), .op .AND, .op .MLOAD, .op .MULMOD]

theorem run_final (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent : UInt256) (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft exponent (UInt256.ofNat 5))).toNat = 32 * index)
    (tail : List UInt256) (hcap : tail.length + 7 < 1024) :
    runInstructions finalProgram
      (WindowTwentyOneLookup.framed template pc mem 18 (accumulator :: modulus :: modulus :: exponent :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 10 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index) accumulator modulus ::
        modulus :: exponent :: tail)) := by
  have hcap3 : tail.length + 4 < 1024 := by omega
  have hcap4 : tail.length + 5 < 1024 := by omega
  have hcap5 : tail.length + 6 < 1024 := by omega
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table index hindex
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, finalProgram, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, hcap5,
      List.getElem?_cons_succ, List.getElem?_cons_zero,
      h18, haddress, hread, hactive,
      State.activeWordsAfterUInt256, advancePC, succ_eq_add, hp2, hp3, word_add_assoc]

/-- 2410..2420: nibble 62 from the original exponent, ninth on the stack.
The right-shifted memory rows intentionally do not represent this low digit. -/
def stackLookupProgram : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .push 1 (UInt256.ofNat 1), .op .SHL,
   .push 2 (UInt256.ofNat 480), .op .AND, .op .MLOAD, .op .MULMOD]

theorem run_stackLookup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent : UInt256) (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft exponent (UInt256.ofNat 1))).toNat = 32 * index)
    (tail : List UInt256) (hcap : tail.length + 13 < 1024) :
    runInstructions stackLookupProgram
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate 6 modulus ++ modulus :: exponent :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 10 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index) accumulator modulus ::
        List.replicate 5 modulus ++ modulus :: exponent :: tail)) := by
  have hcap8 : tail.length + 9 < 1024 := by omega
  have hcap9 : tail.length + 10 < 1024 := by omega
  have hcap10 : tail.length + 11 < 1024 := by omega
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table index hindex
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, stackLookupProgram, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap8, hcap9, hcap10,
      List.replicate_succ, List.getElem?_cons_succ, List.getElem?_cons_zero,
      h18, haddress, hread, hactive,
      State.activeWordsAfterUInt256, advancePC, succ_eq_add, hp2, hp3, word_add_assoc]

/-- Shifting the original exponent left once selects nibble 62 under the mask. -/
theorem stack62_address (e : UInt256) :
    (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft e (UInt256.ofNat 1))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat 62 := by
  have hshift := WindowTwentyOneBits.shifted_lookupAddress e 1 61 (by omega) (by omega) (by omega)
  have hz : UInt256.shiftRight (UInt256.shiftLeft e (UInt256.ofNat 1)) (UInt256.ofNat 0) =
      UInt256.shiftLeft e (UInt256.ofNat 1) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega)]
    simp
  have hc : UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft e (UInt256.ofNat 1)) =
      UInt256.land (UInt256.shiftRight (UInt256.shiftLeft e (UInt256.ofNat 1)) (UInt256.ofNat 0))
        (UInt256.ofNat 480) := by
    rw [hz, land_comm]
  rw [hc]
  simpa [WindowTwentyOneBits.lookupAddress, WindowTwentyOneMath.nibble] using hshift

/-- 2384..2444: nibbles 61 and 62, final squares, nibble 63, return.
An unreachable PUSH0 at 2444 compensates for the removed instruction; existing
padding at 2445..2447 then preserves every later byte PC and instruction index. -/
def tailProgram : List Instr :=
  routeWindows 60 1 ++ WindowSixteenBlock.Block.squares 4 ++ stackLookupProgram ++
    WindowSixteenBlock.Block.squares 4 ++ finalProgram ++ WindowTwentyOneReturn.program

/-! ## The route, state by state -/

def routeMem (base modulus exponent : UInt256) : ByteArray :=
  precopyMem (WindowTableMemory.tableMemory base modulus) exponent

/-- Below the pool: the original modulus, exponent, and caller rest. -/
def frame (modulus exponent : UInt256) (rest : List UInt256) : List UInt256 :=
  modulus :: exponent :: rest

def routeState (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (stack : List UInt256) : State :=
  WindowTwentyOneLookup.framed template (UInt256.ofNat pc) (routeMem base modulus exponent) 18 stack

theorem routeMem_table (base modulus exponent : UInt256) :
    ∀ index, index < 16 → MachineState.readWord (routeMem base modulus exponent) (32 * index) =
      WindowMath.tableWord base modulus index := by
  intro index hindex
  rw [routeMem, readWord_precopyMem_low _ _ _ (by omega)]
  exact WindowTableMemory.readWord_tableMemory base modulus index hindex

/-- The returned state: the result word is stored at 0 and returned from pc 2443. -/
def returnedState (template : State) (base modulus exponent : UInt256) (rest : List UInt256) :
    State :=
  WindowTwentyOneReturn.returned
    (routeState template 2307 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 :: frame modulus exponent rest))
    (UInt256.ofNat 2312) (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 18
    (frame modulus exponent rest)

theorem run_setupAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions setupProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 837) base modulus 16
        (modulus :: exponent :: rest)) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 841) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3) :: frame modulus exponent rest)) := by
  have h := run_setup template (UInt256.ofNat 837) base modulus exponent rest (by omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_copyAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructionsX copyProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 841) base modulus 16
        (UInt256.shiftRight exponent (UInt256.ofNat 3) :: frame modulus exponent rest)) =
    some (routeState template 849 base modulus exponent (frame modulus exponent rest)) := by
  have h := run_copy template (UInt256.ofNat 841) base modulus exponent
    (UInt256.shiftRight exponent (UInt256.ofNat 3)) rest (by omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_poolAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions poolProgram (routeState template 849 base modulus exponent
      (frame modulus exponent rest)) =
    some (routeState template 1164 base modulus exponent
      (List.replicate 315 modulus ++ frame modulus exponent rest)) := by
  have h := run_pool template (UInt256.ofNat 849) (routeMem base modulus exponent) 18
    modulus (exponent :: rest)
    (by simp only [List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_firstAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions firstProgram (routeState template 1164 base modulus exponent
      (List.replicate 315 modulus ++ frame modulus exponent rest)) =
    some (routeState template 1173 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 315 modulus ++ frame modulus exponent rest)) := by
  have hd := WindowTwentyOneMath.nibble_lt exponent.toNat 0
  have h := run_first template (UInt256.ofNat 1164) (routeMem base modulus exponent) base modulus
    (WindowTwentyOneMath.nibble exponent.toNat 0) hd (routeMem_table base modulus exponent _ hd)
    (first_address _ exponent) (List.replicate 315 modulus ++ frame modulus exponent rest)
    (by simp only [frame, List.length_append, List.length_replicate, List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_headAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions (routeWindows 0 60) (routeState template 1173 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 315 modulus ++ frame modulus exponent rest)) =
    some (routeState template 2253 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ frame modulus exponent rest)) := by
  have h := run_routeWindows template (routeMem base modulus exponent) base modulus exponent
    (frame modulus exponent rest) (routeMem_table base modulus exponent)
    (fun i hi => precopy_address _ exponent i hi) 60 0 (by omega) (UInt256.ofNat 1173)
    (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat) 15
    (by simp only [frame, List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_tailAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions tailProgram (routeState template 2253 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ frame modulus exponent rest)) =
    some (returnedState template base modulus exponent rest) := by
  have h1 : runInstructions (routeWindows 60 1) (routeState template 2253 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ frame modulus exponent rest)) =
      some (routeState template 2271 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 10 modulus ++ frame modulus exponent rest)) := by
    have h := run_routeWindows template (routeMem base modulus exponent) base modulus exponent
      (frame modulus exponent rest) (routeMem_table base modulus exponent)
      (fun i hi => precopy_address _ exponent i hi) 1 60 (by omega) (UInt256.ofNat 2253)
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60) 10
      (by simp only [frame, List.length_cons]; omega)
    have h61 : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 60) 1
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60) =
        WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 :=
      (WindowTwentyOneMath.advance_add base modulus exponent.toNat 1 60 1 _).symm
    rw [advancePC_ofNat, h61] at h
    exact h
  have h2a : runInstructions (WindowSixteenBlock.Block.squares 4)
      (routeState template 2271 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 10 modulus ++ frame modulus exponent rest)) =
      some (routeState template 2279 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61) ::
          List.replicate 6 modulus ++ frame modulus exponent rest)) := by
    have h := WindowSixteenBlock.Block.run_squares template (UInt256.ofNat 2271)
      (routeMem base modulus exponent) 18 modulus
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61)
      (List.replicate 6 modulus ++ frame modulus exponent rest) 4 (by decide)
      (by simp only [frame, List.length_append, List.length_replicate, List.length_cons]; omega)
    have hstack : WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 10 modulus ++ frame modulus exponent rest =
        WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 4 modulus ++ (List.replicate 6 modulus ++ frame modulus exponent rest) := by
      simp only [List.cons_append, ← List.append_assoc, ← List.replicate_add]
    rw [advancePC_ofNat] at h
    rw [hstack]
    exact h
  have hd62 := WindowTwentyOneMath.nibble_lt exponent.toNat 62
  have h2b : runInstructions stackLookupProgram
      (routeState template 2279 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61) ::
          List.replicate 6 modulus ++ frame modulus exponent rest)) =
      some (routeState template 2289 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 5 modulus ++ frame modulus exponent rest)) := by
    have h := run_stackLookup template (UInt256.ofNat 2279) (routeMem base modulus exponent)
      base modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61))
      exponent (WindowTwentyOneMath.nibble exponent.toNat 62)
      hd62 (routeMem_table base modulus exponent _ hd62) (stack62_address exponent)
      rest (by omega)
    have h62 : WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 =
        UInt256.mulMod
          (WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 62))
          (WindowMath.squareWordAfter modulus 4
            (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61)) modulus := by
      rw [mulMod_comm]
      rfl
    rw [advancePC_ofNat] at h
    rw [h62]
    exact h
  have h3 : runInstructions (WindowSixteenBlock.Block.squares 4)
      (routeState template 2289 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 5 modulus ++ frame modulus exponent rest)) =
      some (routeState template 2297 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62) ::
          modulus :: frame modulus exponent rest)) := by
    have h := WindowSixteenBlock.Block.run_squares template (UInt256.ofNat 2289)
      (routeMem base modulus exponent) 18 modulus
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62)
      (modulus :: frame modulus exponent rest) 4 (by decide)
      (by simp only [frame, List.length_cons]; omega)
    have hstack : WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 5 modulus ++ frame modulus exponent rest =
        WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 4 modulus ++ modulus :: frame modulus exponent rest := by
      simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    rw [advancePC_ofNat] at h
    rw [hstack]
    exact h
  have hd := WindowTwentyOneMath.nibble_lt exponent.toNat 63
  have h4 : runInstructions finalProgram
      (routeState template 2297 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62) ::
          modulus :: frame modulus exponent rest)) =
      some (WindowTwentyOneReturn.framed
        (routeState template 2307 base modulus exponent
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 ::
            frame modulus exponent rest))
        (UInt256.ofNat 2307)
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 ::
          frame modulus exponent rest)) := by
    have h := run_final template (UInt256.ofNat 2297) (routeMem base modulus exponent) base modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62))
      exponent (WindowTwentyOneMath.nibble exponent.toNat 63)
      hd (routeMem_table base modulus exponent _ hd) (last_address exponent)
      rest (by omega)
    rw [advancePC_ofNat,
      mulMod_comm (WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 63))
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62)) modulus] at h
    exact h
  have h5 := WindowTwentyOneReturn.run_return
    (routeState template 2307 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 :: frame modulus exponent rest))
    (UInt256.ofNat 2307) (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 18
    (by decide) rfl (frame modulus exponent rest) (by simp only [frame, List.length_cons]; omega)
  rw [advancePC_ofNat] at h5
  have h012 := runInstructions_append_some _ _ _ _ _ h1 h2a
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h2b
  have h01234 := runInstructions_append_some _ _ _ _ _ h0123 h3
  have h012345 := runInstructions_append_some _ _ _ _ _ h01234 h4
  have hall := runInstructions_append_some _ _ _ _ _ h012345 h5
  exact hall

/-! ## Result -/

theorem core_result (template : State) (base modulus exponent : UInt256)
    (hmodulus : 0 < modulus.toNat) (rest : List UInt256) :
    (returnedState template base modulus exponent rest).toResult =
      .returned (Precompile.natToBytes (base.toNat ^ exponent.toNat % modulus.toNat) 32) := by
  unfold returnedState
  rw [WindowTwentyOneReturn.returned_result]
  have he : exponent.toNat < 16 ^ 64 := by
    change exponent.toNat < 2 ^ 256
    exact exponent.val.isLt
  have h := WindowTwentyOneMath.three_bodies_toNat base modulus exponent.toNat hmodulus he
  rw [h]

/-- With a zero modulus the last `MULMOD` yields zero. -/
theorem core_result_zero (template : State) (base modulus exponent : UInt256)
    (hmodulus : modulus.toNat = 0) (rest : List UInt256) :
    (returnedState template base modulus exponent rest).toResult =
      .returned (Precompile.natToBytes 0 32) := by
  unfold returnedState
  rw [WindowTwentyOneReturn.returned_result]
  have h := WindowTwentyOneMath.accumulator_zero base modulus exponent.toNat hmodulus
  rw [h]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopyRoute
