import Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopy
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

/-!
# Precopy window route (lane precopy256)

Every modulus copy the ladder consumes is pushed once, before the accumulator exists.
Pcs outside the route are unchanged; instruction indices after pc 2397 move by -80.
The tail follows the head windows directly at 2388 (no jump, no `JUMPDEST`).

* 968..976 `setupProgram`: `e <<< 1` and `e >>> 3` from the exponent word under the modulus;
* 976..981 `copyProgram`: the two `MSIZE` stores, `e >>> 3` at 512 and `e <<< 1` at 544;
* 981..1296 `poolProgram`: `DUP2` and 314 `DUP1`, the 315 modulus copies;
* 1296..1308 `firstProgram`: nibble 0 from byte 512 (`e >>> 251`);
* 1308..2388 `routeWindows 0 60`: nibbles 1..60;
* 2388..2448 `tailProgram`: nibbles 61 and 62, the last four squarings, nibble 63 from
  `e <<< 1` on the stack, and the return, straight after the head windows.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopyRoute

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneMsize

/-! ## Memory: `e >>> 3` at 512 and `e <<< 1` at 544 above the table -/

def precopyMem (mem : ByteArray) (e : UInt256) : ByteArray :=
  WindowTableMemory.storeWord
    (WindowTableMemory.storeWord mem 512 (UInt256.shiftRight e (UInt256.ofNat 3)))
    544 (UInt256.shiftLeft e (UInt256.ofNat 1))

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

/-- Row B (`e <<< 1` at 544), read at `514 + k`. -/
theorem land480_rowB (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 30) :
    UInt256.land (UInt256.ofNat 480) (MachineState.readWord (precopyMem mem e) (514 + k)) =
      UInt256.land (UInt256.ofNat 480)
        (UInt256.shiftRight (UInt256.shiftLeft e (UInt256.ofNat 1)) (UInt256.ofNat (240 - 8 * k))) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
    show (UInt256.ofNat 480).toNat = 480 from rfl,
    land480_mod (MachineState.readWord _ _).toNat, land480_mod (_ >>> _)]
  congr 1
  have hw := window_low (precopyMem mem e) 544 k (UInt256.shiftLeft e (UInt256.ofNat 1)) (by omega)
    (by
      unfold precopyMem
      rw [WindowCopyMemory.storeWord_getD _ _ _ _ (by omega)])
    (by
      unfold precopyMem
      rw [Nat.add_assoc, WindowCopyMemory.storeWord_getD _ _ _ _ (by omega),
        show 31 - (k + 1) = 30 - k by omega])
    (by omega)
  rw [show 544 - 30 + k = 514 + k by omega] at hw
  have hp : 256 ^ (30 - k) = (2 : Nat) ^ (240 - 8 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    congr 1
    omega
  rw [hw, Nat.shiftRight_eq_div_pow, hp]

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

/-- The 62 window loads: load `i` addresses nibble `1 + i`. -/
theorem precopy_address (mem : ByteArray) (e : UInt256) (i : Nat) (hi : i < 62) :
    (UInt256.land (UInt256.ofNat 480)
      (MachineState.readWord (precopyMem mem e) (WindowCopyMemory.laddr i))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat (1 + i) := by
  unfold WindowCopyMemory.laddr
  by_cases h : i % 2 = 0
  · rw [if_pos h, land480_rowA mem e (i / 2) (by omega), land_comm]
    have hl := WindowTwentyOneBits.lookupAddress_toNat e (243 - 8 * (i / 2)) (by omega)
    unfold WindowTwentyOneBits.lookupAddress at hl
    rw [hl]
    unfold WindowTwentyOneMath.nibble
    rw [Nat.shiftRight_eq_div_pow, show 243 - 8 * (i / 2) + 5 = 4 * (63 - (1 + i)) by omega,
      Nat.pow_mul]
  · rw [if_neg h, land480_rowB mem e (i / 2) (by omega), land_comm,
      show 240 - 8 * (i / 2) = 244 - 4 * i by omega]
    have hshift := WindowTwentyOneBits.shifted_lookupAddress e 1 i (by omega) hi (by omega)
    simpa [WindowTwentyOneBits.lookupAddress, WindowTwentyOneMath.nibble] using hshift

private theorem first_digit_nat (x hi lo E : Nat) (hE : E < 2 ^ 256)
    (hx : x % 65536 = hi * 256 + lo)
    (hlo : lo = E / 8 / 256 ^ 31 % 256) :
    ((x >>> 1) % 16) <<< 5 = 32 * (E / 16 ^ (63 - 0) % 16) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num at hlo hE ⊢
  omega

/-- The first load reads byte 512, the top byte of `e >>> 3`; `SHL 4` and the mask
leave nibble 0. -/
theorem first_address (mem : ByteArray) (e : UInt256) :
    (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft (MachineState.readWord (precopyMem mem e) 481) (UInt256.ofNat 4))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat 0 := by
  have hlow := WindowCopyMemory.readWord_mod65536 (precopyMem mem e) 481
  have hb := WindowCopyMemory.storeWord_getD mem 512 (UInt256.shiftRight e (UInt256.ofNat 3)) 0
    (by omega)
  have hb' : (((precopyMem mem e)[481 + 31]?.getD 0).toNat) =
      e.toNat / 8 / 256 ^ 31 % 256 := by
    unfold precopyMem
    rw [WindowCopyMemory.storeWord_getD_other _ _ _ _ (Or.inl (by omega))]
    rw [show 481 + 31 = 512 + 0 by rfl, hb, Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
      Nat.shiftRight_eq_div_pow]
  rw [Challenge.EvmProof.Word.word_toNat_land, show (UInt256.ofNat 480).toNat = 480 from rfl,
    WindowTwentyOneBits.shiftLeft_toNat_mod _ 4 (by omega), Nat.and_comm,
    WindowTwentyOneBits.mask480_nat,
    WindowTwentyOneBits.shifted_nibble_nat _ 4 5 (by omega) (by omega)]
  unfold WindowTwentyOneMath.nibble
  exact first_digit_nat _ _ _ e.toNat e.val.isLt hlow hb'

/-- The last digit: `(e <<< 1) <<< 4` puts nibble 63 under the mask. -/
theorem last_address (e : UInt256) :
    (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft (UInt256.shiftLeft e (UInt256.ofNat 1)) (UInt256.ofNat 4))).toNat =
      32 * WindowTwentyOneMath.nibble e.toNat 63 := by
  have h := WindowTwentyOneBits.shifted_lookupAddressLast e
  have h4 : (4 : UInt256) = UInt256.ofNat 4 := rfl
  rw [h4] at h
  rw [h]
  unfold WindowTwentyOneMath.nibble
  simp

/-! ## Straight-line pieces -/

theorem advancePC_ofNat (count pc : Nat) :
    advancePC count (UInt256.ofNat pc) = UInt256.ofNat (pc + count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [advancePC, ih, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- 968..976: `DUP2 PUSH1 1 SHL DUP3 PUSH1 3 SHR`. -/
def setupProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 1 1, .op .SHL,
   .op (.Dup ⟨2, by decide⟩), .push 1 3, .op .SHR]

theorem run_setup (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions setupProgram
      (WindowTwentyOneTable.framed template pc base modulus 16 (modulus :: exponent :: rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 8 pc) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3) ::
        UInt256.shiftLeft exponent (UInt256.ofNat 1) :: modulus :: exponent :: rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, setupProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, hcap5, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, word_add_assoc]

/-- 976..981: `MSIZE MSTORE DUP1 MSIZE MSTORE`, the two row stores above the table. -/
def copyProgram : List Instr :=
  [.op .MSIZE, .op .MSTORE, .op (.Dup ⟨0, by decide⟩), .op .MSIZE, .op .MSTORE]

theorem run_copy (template : State) (pc base modulus low high : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 1000) :
    runInstructionsX copyProgram
      (WindowTwentyOneTable.framed template pc base modulus 16 (low :: high :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 5 pc)
      (WindowTableMemory.storeWord
        (WindowTableMemory.storeWord (WindowTableMemory.tableMemory base modulus) 512 low)
        544 high) 18 (high :: tail)) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcap3 : tail.length + 3 < 1024 := by omega
  have ha : (UInt256.ofNat 16).toNat = 16 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : MachineState.activeWordsAfter 16 512 32 = 17 := by
    simp [MachineState.activeWordsAfter]
  have h1' : (UInt256.ofNat 17).toNat = 17 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : MachineState.activeWordsAfter 17 544 32 = 18 := by
    simp [MachineState.activeWordsAfter]
  simp [runInstructionsX, runInstrX_msize, copyProgram,
    WindowTwentyOneTable.framed, WindowTwentyOneLookup.framed,
    WindowTableMemory.tableMemory, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap1, hcap2, hcap3, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    advancePC, succ_eq_add, word_add_assoc]

/-- 981..1296: `DUP2` then 314 `DUP1`: the 315 modulus copies. -/
def poolProgram : List Instr := .op (.Dup ⟨1, by decide⟩) :: WindowPrecopy.dupOnes 314

private theorem run_dupTwo (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (x modulus : UInt256) (tail : List UInt256) (hcap : tail.length + 3 < 1024) :
    runInstructions [.op (.Dup ⟨1, by decide⟩)]
      (WindowTwentyOneLookup.framed template pc mem active (x :: modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 1 pc) mem active
      (modulus :: x :: modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  simp (disch := omega)
    [runInstructions, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap2,
      List.getElem?_cons_succ, List.getElem?_cons_zero, advancePC]

theorem run_pool (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (x modulus : UInt256) (tail : List UInt256) (hcap : tail.length + 320 < 1024) :
    runInstructions poolProgram
      (WindowTwentyOneLookup.framed template pc mem active (x :: modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 315 pc) mem active
      (List.replicate 315 modulus ++ x :: modulus :: tail)) := by
  have h0 := run_dupTwo template pc mem active x modulus tail (by omega)
  have h1 := WindowPrecopy.run_dupOnes template mem active modulus 314 (advancePC 1 pc)
    (x :: modulus :: tail) (by simp only [List.length_cons]; omega)
  have hall := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : advancePC 314 (advancePC 1 pc) = advancePC 315 pc := by
    rw [← advancePC_add]
  simpa only [poolProgram, List.singleton_append, hpc] using hall

/-- 1296..1308: nibble 0 from byte 512. -/
def firstProgram : List Instr :=
  [.push 2 (UInt256.ofNat 481), .op .MLOAD, .push 1 (UInt256.ofNat 4), .op .SHL,
   .push 2 (UInt256.ofNat 480), .op .AND, .op .MLOAD]

theorem run_first (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus : UInt256) (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft (MachineState.readWord mem 481) (UInt256.ofNat 4))).toNat = 32 * index)
    (stack : List UInt256) (hcap : stack.length + 3 < 1024) :
    runInstructions firstProgram (WindowTwentyOneLookup.framed template pc mem 18 stack) =
    some (WindowTwentyOneLookup.framed template (advancePC 12 pc) mem 18
      (WindowMath.tableWord base modulus index :: stack)) := by
  have hcap0 : stack.length < 1024 := by omega
  have hcap1 : stack.length + 1 < 1024 := by omega
  have hcap2 : stack.length + 2 < 1024 := by omega
  have hl : (UInt256.ofNat 481).toNat = 481 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table index hindex
  have hactive' := WindowCopyMemory.activeWordsAfter_eighteen 481 (by omega)
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, firstProgram, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap0, hcap1, hcap2,
      hl, h18, haddress, hread, hactive, hactive',
      State.activeWordsAfterUInt256, advancePC, succ_eq_add, hp2, hp3, word_add_assoc]

/-- Windows for nibbles `1 + start`, ..., `start + count`, loads at `laddr start`, .... -/
def routeWindows (start : Nat) : Nat → List Instr
  | 0 => []
  | count + 1 =>
      WindowPrecopy.windowProgram (WindowCopyMemory.laddr start) ++ routeWindows (start + 1) count

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
    (haddress : ∀ i, i < 62 →
      (UInt256.land (UInt256.ofNat 480)
        (MachineState.readWord mem (WindowCopyMemory.laddr i))).toNat =
        32 * WindowTwentyOneMath.nibble exponent.toNat (1 + i)) :
    ∀ (count start : Nat), start + count ≤ 62 →
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
        (5 * (count + 1) + extra) (by omega) (WindowCopyMemory.laddr start)
        (WindowSixteenBlock.Block.laddr_bound start (by omega))
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

/-- 5528..5538: nibble 63 from `e <<< 1` (third on the stack) and the last multiply. -/
def finalProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 1 (UInt256.ofNat 4), .op .SHL,
   .push 2 (UInt256.ofNat 480), .op .AND, .op .MLOAD, .op .MULMOD]

theorem run_final (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator doubledE : UInt256) (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftLeft doubledE (UInt256.ofNat 4))).toNat = 32 * index)
    (tail : List UInt256) (hcap : tail.length + 6 < 1024) :
    runInstructions finalProgram
      (WindowTwentyOneLookup.framed template pc mem 18 (accumulator :: modulus :: doubledE :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 10 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index) accumulator modulus ::
        doubledE :: tail)) := by
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hcap4 : tail.length + 4 < 1024 := by omega
  have hcap5 : tail.length + 5 < 1024 := by omega
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

/-- 2388..2448: nibbles 61 and 62, the last four squarings, nibble 63, return. -/
def tailProgram : List Instr :=
  routeWindows 60 2 ++ WindowSixteenBlock.Block.squares 4 ++ finalProgram ++
    WindowTwentyOneReturn.program

/-! ## The route, state by state -/

def routeMem (base modulus exponent : UInt256) : ByteArray :=
  precopyMem (WindowTableMemory.tableMemory base modulus) exponent

/-- Below the pool: `e <<< 1`, the modulus and exponent words, the caller's rest. -/
def frame (modulus exponent : UInt256) (rest : List UInt256) : List UInt256 :=
  UInt256.shiftLeft exponent (UInt256.ofNat 1) :: modulus :: exponent :: rest

def routeState (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (stack : List UInt256) : State :=
  WindowTwentyOneLookup.framed template (UInt256.ofNat pc) (routeMem base modulus exponent) 18 stack

theorem routeMem_table (base modulus exponent : UInt256) :
    ∀ index, index < 16 → MachineState.readWord (routeMem base modulus exponent) (32 * index) =
      WindowMath.tableWord base modulus index := by
  intro index hindex
  rw [routeMem, readWord_precopyMem_low _ _ _ (by omega)]
  exact WindowTableMemory.readWord_tableMemory base modulus index hindex

/-- The returned state: the result word is stored at 0 and returned from pc 5543. -/
def returnedState (template : State) (base modulus exponent : UInt256) (rest : List UInt256) :
    State :=
  WindowTwentyOneReturn.returned
    (routeState template 2311 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 :: frame modulus exponent rest))
    (UInt256.ofNat 2316) (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 18
    (frame modulus exponent rest)

theorem run_setupAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions setupProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 837) base modulus 16
        (modulus :: exponent :: rest)) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 845) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3) :: frame modulus exponent rest)) := by
  have h := run_setup template (UInt256.ofNat 837) base modulus exponent rest (by omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_copyAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructionsX copyProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 845) base modulus 16
        (UInt256.shiftRight exponent (UInt256.ofNat 3) :: frame modulus exponent rest)) =
    some (routeState template 850 base modulus exponent (frame modulus exponent rest)) := by
  have h := run_copy template (UInt256.ofNat 845) base modulus
    (UInt256.shiftRight exponent (UInt256.ofNat 3)) (UInt256.shiftLeft exponent (UInt256.ofNat 1))
    (modulus :: exponent :: rest) (by simp only [List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_poolAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions poolProgram (routeState template 850 base modulus exponent
      (frame modulus exponent rest)) =
    some (routeState template 1165 base modulus exponent
      (List.replicate 315 modulus ++ frame modulus exponent rest)) := by
  have h := run_pool template (UInt256.ofNat 850) (routeMem base modulus exponent) 18
    (UInt256.shiftLeft exponent (UInt256.ofNat 1)) modulus (exponent :: rest)
    (by simp only [List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_firstAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions firstProgram (routeState template 1165 base modulus exponent
      (List.replicate 315 modulus ++ frame modulus exponent rest)) =
    some (routeState template 1177 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 315 modulus ++ frame modulus exponent rest)) := by
  have hd := WindowTwentyOneMath.nibble_lt exponent.toNat 0
  have h := run_first template (UInt256.ofNat 1165) (routeMem base modulus exponent) base modulus
    (WindowTwentyOneMath.nibble exponent.toNat 0) hd (routeMem_table base modulus exponent _ hd)
    (first_address _ exponent) (List.replicate 315 modulus ++ frame modulus exponent rest)
    (by simp only [frame, List.length_append, List.length_replicate, List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_headAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions (routeWindows 0 60) (routeState template 1177 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 315 modulus ++ frame modulus exponent rest)) =
    some (routeState template 2257 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ frame modulus exponent rest)) := by
  have h := run_routeWindows template (routeMem base modulus exponent) base modulus exponent
    (frame modulus exponent rest) (routeMem_table base modulus exponent)
    (fun i hi => precopy_address _ exponent i hi) 60 0 (by omega) (UInt256.ofNat 1177)
    (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat) 15
    (by simp only [frame, List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h

theorem run_tailAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions tailProgram (routeState template 2257 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ frame modulus exponent rest)) =
    some (returnedState template base modulus exponent rest) := by
  have h1 : runInstructions (routeWindows 60 2) (routeState template 2257 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ frame modulus exponent rest)) =
      some (routeState template 2293 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 4 modulus ++ modulus :: frame modulus exponent rest)) := by
    have h := run_routeWindows template (routeMem base modulus exponent) base modulus exponent
      (frame modulus exponent rest) (routeMem_table base modulus exponent)
      (fun i hi => precopy_address _ exponent i hi) 2 60 (by omega) (UInt256.ofNat 2257)
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60) 5
      (by simp only [frame, List.length_cons]; omega)
    have h62 : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 60) 2
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60) =
        WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 :=
      (WindowTwentyOneMath.advance_add base modulus exponent.toNat 1 60 2 _).symm
    rw [advancePC_ofNat, h62] at h
    exact h
  have h2 : runInstructions (WindowSixteenBlock.Block.squares 4)
      (routeState template 2293 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 4 modulus ++ modulus :: frame modulus exponent rest)) =
      some (routeState template 2301 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62) ::
          modulus :: frame modulus exponent rest)) := by
    have h := WindowSixteenBlock.Block.run_squares template (UInt256.ofNat 2293)
      (routeMem base modulus exponent) 18 modulus
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62)
      (modulus :: frame modulus exponent rest) 4 (by decide)
      (by simp only [frame, List.length_cons]; omega)
    rw [advancePC_ofNat] at h
    exact h
  have hd := WindowTwentyOneMath.nibble_lt exponent.toNat 63
  have h3 : runInstructions finalProgram
      (routeState template 2301 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62) ::
          modulus :: frame modulus exponent rest)) =
      some (WindowTwentyOneReturn.framed
        (routeState template 2311 base modulus exponent
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 ::
            frame modulus exponent rest))
        (UInt256.ofNat 2311)
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 ::
          frame modulus exponent rest)) := by
    have h := run_final template (UInt256.ofNat 2301) (routeMem base modulus exponent) base modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62))
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) (WindowTwentyOneMath.nibble exponent.toNat 63)
      hd (routeMem_table base modulus exponent _ hd) (last_address exponent)
      (modulus :: exponent :: rest) (by simp only [List.length_cons]; omega)
    rw [advancePC_ofNat,
      mulMod_comm (WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 63))
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62)) modulus] at h
    exact h
  have h4 := WindowTwentyOneReturn.run_return
    (routeState template 2311 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 :: frame modulus exponent rest))
    (UInt256.ofNat 2311) (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 18
    (by decide) rfl (frame modulus exponent rest) (by simp only [frame, List.length_cons]; omega)
  rw [advancePC_ofNat] at h4
  have h012 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  have hall := runInstructions_append_some _ _ _ _ _ h0123 h4
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
