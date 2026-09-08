import Challenge.Modexp.Submission.Proofs.Fast.FullBaseGuardCore
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

def fallbackProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 31), .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 5), .op .SHR,
   .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 5), .op .SHL, .op .SUB,
   .push ⟨1, by decide⟩ (UInt256.ofNat 3), .op .SHL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 96), .op .CALLDATALOAD,
   .op (.Swap ⟨0, by decide⟩), .op .SHR,
   .op (.Dup ⟨2, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 992), .op .ADD, .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1668), .op .JUMP]

def pbOf (bsize : Nat) : Nat := (31 + bsize) / 32
def topWidth (bsize : Nat) : Nat := bsize - 32 * (pbOf bsize - 1)
def topLimbOf (input : ByteArray) (bsize : Nat) : Nat :=
  Precompile.bytesToNatPadded input 96 (topWidth bsize)
def storeWord (memory : ByteArray) (addr : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded w.toNat 32) addr

def legacyLoopState (s : State) (memory : ByteArray)
    (n bsize esize msize pb j : Nat) : State :=
  { s with pc := UInt256.ofNat 1668
           stack := UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize
           memory := memory }

theorem runInstructions_append (left right : List Instr) (s : State) :
    runInstructions (left ++ right) s =
      (runInstructions left s).bind (runInstructions right) := by
  induction left generalizing s with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, runInstructions]
      cases Challenge.EvmProof.Stepper.runInstr instruction s <;> simp [ih]

theorem runInstructions_append_of (left right : List Instr) (s mid final : State)
    (hleft : runInstructions left s = some mid)
    (hright : runInstructions right mid = some final) :
    runInstructions (left ++ right) s = some final := by
  rw [runInstructions_append, hleft]
  exact hright

def fallbackCountProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 31), .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 5), .op .SHR]

def fallbackWordProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 5), .op .SHL, .op .SUB,
   .push ⟨1, by decide⟩ (UInt256.ofNat 3), .op .SHL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 96), .op .CALLDATALOAD,
   .op (.Swap ⟨0, by decide⟩), .op .SHR]

def fallbackStoreProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 992), .op .ADD, .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1668), .op .JUMP]

def fallbackCountState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3669
           stack := UInt256.ofNat (pbOf bsize) :: outer n bsize esize msize
           memory := memory }

def fallbackWordState (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3683
           stack := UInt256.ofNat (topLimbOf input bsize) ::
             UInt256.ofNat (pbOf bsize) :: outer n bsize esize msize
           memory := memory }

private theorem shr_ofNat (value shift : Nat) (hv : value < 2 ^ 256)
    (hs : shift < 256) :
    UInt256.shiftRight (UInt256.ofNat value) (UInt256.ofNat shift) =
      UInt256.ofNat (value / 2 ^ shift) := by
  simpa only [Nat.shiftRight_eq_div_pow] using
    Challenge.EvmProof.Word.shiftRight_ofNat hv hs

private theorem mod_word_self {a : Nat} (ha : a < 2 ^ 256) :
    a % 2 ^ 256 = a := Nat.mod_eq_of_lt ha

private theorem activeWords_fix (s : State) (offset size : Nat) (hsz : size ≠ 0)
    (hend : offset + size ≤ 9536) (hactive : 298 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat offset size) =
      s.activeWords := by
  have hnat : MachineState.activeWordsAfter s.activeWords.toNat offset size =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, hsz, if_false]
    apply Nat.max_eq_left
    omega
  rw [hnat]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

set_option linter.unusedSimpArgs false in
/-- The miss branch executes the relocated general Horner initialization and
jumps to the unchanged loop. No guard-match assumption is needed here. -/
theorem run_fallback (s : State) (mem input : ByteArray)
    (n bsize esize msize : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 1668 = true) :
    runInstructions fallbackProgram (fallbackState s mem n bsize esize msize) =
      some (legacyLoopState s (storeWord mem (992 + 32 * n)
        (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize
        (pbOf bsize) 1) := by
  have hpb1 : 1 ≤ pbOf bsize := by unfold pbOf; omega
  have hpbLe : pbOf bsize ≤ 32 := by unfold pbOf; omega
  have hpbBig : bsize ≤ 32 * pbOf bsize := by unfold pbOf; omega
  have hpbLow : 32 * (pbOf bsize - 1) < bsize := by unfold pbOf; omega
  have htw1 : 0 < topWidth bsize := by unfold topWidth; omega
  have htw32 : topWidth bsize ≤ 32 := by unfold topWidth; omega
  have hshiftEq : 32 * pbOf bsize - bsize = 32 - topWidth bsize := by
    unfold topWidth; omega
  have hshr : UInt256.shiftRight (UInt256.ofNat (31 + bsize)) (UInt256.ofNat 5) =
      UInt256.ofNat ((31 + bsize) / 2 ^ 5) :=
    shr_ofNat _ 5 (Nat.lt_of_le_of_lt (show 31 + bsize ≤ 1055 by omega) (by norm_num))
      (by omega)
  have hpb : (31 + bsize) / 32 = pbOf bsize := rfl
  have hshl : UInt256.shiftLeft (UInt256.ofNat (pbOf bsize)) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * pbOf bsize) := by
    have he : pbOf bsize * 2 ^ 5 = 32 * pbOf bsize := by ring
    have h1 : pbOf bsize < 2 ^ 256 := Nat.lt_of_le_of_lt hpbLe (by norm_num)
    have h2 : (5 : Nat) < 256 := by omega
    have h3 : pbOf bsize * 2 ^ 5 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show 32 * pbOf bsize ≤ 1024 by omega) (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsub : UInt256.ofNat (32 * pbOf bsize) - UInt256.ofNat bsize =
      UInt256.ofNat (32 * pbOf bsize - bsize) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hpbBig
      (Nat.lt_of_le_of_lt (show 32 * pbOf bsize ≤ 1024 by omega) (by norm_num))
  have hshl2 : UInt256.shiftLeft (UInt256.ofNat (32 * pbOf bsize - bsize))
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - topWidth bsize) * 8) := by
    have he : (32 * pbOf bsize - bsize) * 2 ^ 3 = (32 - topWidth bsize) * 8 := by
      rw [← hshiftEq]; ring
    have h1 : 32 * pbOf bsize - bsize < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (show 32 * pbOf bsize - bsize ≤ 1024 by omega) (by norm_num)
    have h2 : (3 : Nat) < 256 := by omega
    have h3 : (32 * pbOf bsize - bsize) * 2 ^ 3 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show (32 - topWidth bsize) * 8 ≤ 256 by omega)
        (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsr : UInt256.shiftRight (MachineState.readWord input 96)
      (UInt256.ofNat ((32 - topWidth bsize) * 8)) =
      UInt256.ofNat (topLimbOf input bsize) :=
    Challenge.EvmProof.Bytes.shiftRight_readWord input 96 (topWidth bsize) htw1 htw32
  have hmod : (992 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 992 + 32 * n := mod_word_self (by
        exact Nat.lt_of_le_of_lt (show 992 + 32 * n ≤ 2016 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (992 + 32 * n) 32) = s.activeWords :=
    activeWords_fix s (992 + 32 * n) 32 (by omega) (by omega) hact
  have hcount : runInstructions fallbackCountProgram
      (fallbackState s mem n bsize esize msize) =
      some (fallbackCountState s mem n bsize esize msize) := by
    simp [fallbackCountProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      fallbackState, fallbackCountState, outer, hshr, hpb,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hword : runInstructions fallbackWordProgram
      (fallbackCountState s mem n bsize esize msize) =
      some (fallbackWordState s mem input n bsize esize msize) := by
    simp [fallbackWordProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      fallbackCountState, fallbackWordState, outer, hdata, hshl, hsub, hshl2, hsr,
      List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hstore : runInstructions fallbackStoreProgram
      (fallbackWordState s mem input n bsize esize msize) =
      some (legacyLoopState s (storeWord mem (992 + 32 * n)
        (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize
        (pbOf bsize) 1) := by
    simp [fallbackStoreProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      fallbackWordState, legacyLoopState, storeWord, outer, hmod, hfix, hjump,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hrest := runInstructions_append_of fallbackWordProgram fallbackStoreProgram
    (fallbackCountState s mem n bsize esize msize)
    (fallbackWordState s mem input n bsize esize msize)
    (legacyLoopState s (storeWord mem (992 + 32 * n)
      (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize (pbOf bsize) 1)
    hword hstore
  have hall := runInstructions_append_of fallbackCountProgram
    (fallbackWordProgram ++ fallbackStoreProgram)
    (fallbackState s mem n bsize esize msize)
    (fallbackCountState s mem n bsize esize msize)
    (legacyLoopState s (storeWord mem (992 + 32 * n)
      (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize (pbOf bsize) 1)
    hcount hrest
  have hprogram : fallbackProgram =
      fallbackCountProgram ++ (fallbackWordProgram ++ fallbackStoreProgram) := rfl
  exact (congrArg
    (fun program => runInstructions program (fallbackState s mem n bsize esize msize))
    hprogram).trans hall

end Challenge.Modexp.Submission.Proofs.Fast.FullBase
