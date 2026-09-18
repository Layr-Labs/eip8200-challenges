import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace RootE3Guard
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

/-- Exact new v4 bytecode at PCs 3013 through 3038. -/
def program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .push 1 1, .op .EQ, .push 2 2816, .op .MLOAD, .op .CALLDATALOAD,
   .push 0 0, .op .BYTE, .push 1 3, .op .EQ, .op .AND, .op (.Dup ⟨1, by decide⟩), .push 1 3,
   .op .AND, .op .ISZERO, .op .AND, .op (.Dup ⟨0, by decide⟩), .push 2 1760, .op .MSTORE,
   .op .SHR]

def exponentByte (mem input : ByteArray) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat 0)
    (MachineState.readWord input (MachineState.readWord mem 2816).toNat)

def guardWord (mem input : ByteArray) (n esize : Nat) : UInt256 :=
  UInt256.land (UInt256.isZero (UInt256.land (UInt256.ofNat 3) (UInt256.ofNat n)))
    (UInt256.land (UInt256.eq (UInt256.ofNat 3) (exponentByte mem input))
      (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat esize)))

def entry (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with
    pc := UInt256.ofNat 2664
    stack := UInt256.ofNat n :: Exp.outer n bsize esize msize
    memory := mem }

def result (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with
    pc := UInt256.ofNat 2691
    stack := UInt256.shiftRight (UInt256.ofNat n)
      (guardWord mem s.executionEnv.calldata n esize) :: Exp.outer n bsize esize msize
    memory := Exp.storeWord mem 1760 (guardWord mem s.executionEnv.calldata n esize)}

theorem run_guard (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 89 ≤ s.activeWords.toNat) :
    runInstructions program (entry s mem n bsize esize msize) =
      some (result s mem n bsize esize msize) := by
  have haw1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2816 32) =
      s.activeWords := Exp.activeWords_fix s 2816 32 (by decide) (by omega) (by omega)
  have haw2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Monpro.activeWords_fix s 1760 32 (by decide) (by omega) (by omega)
  simp (config := {maxSteps := 300000})
    [program, runInstructions, Challenge.EvmProof.Stepper.runInstr, entry, result,
     Exp.outer, Exp.storeWord, guardWord, exponentByte,
     State.activeWordsAfterUInt256, haw1, haw2, Exp.push0_word,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_guard
end RootE3Guard

namespace RootE3Guard
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem exponentByte_spec (mem input : ByteArray) (bsize : Nat) (hb : bsize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize)) :
    exponentByte mem input = UInt256.ofNat (FixedExponentRoute.exponentValue input bsize 1) := by
  have hoff : 96 + bsize < 2 ^ 256 := by omega
  rw [exponentByte, heoff, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from Exp.push0_word.symm,
    Challenge.EvmProof.Bytes.byteAt_zero_readWord]
  congr 1
  symm
  simpa [FixedExponentRoute.exponentValue] using
    Challenge.EvmProof.Bytes.bytesToNatPadded_succ input (96 + bsize) 0

theorem exponentValue_one_lt (input : ByteArray) (bsize : Nat) :
    FixedExponentRoute.exponentValue input bsize 1 < 256 := by
  simpa [FixedExponentRoute.exponentValue] using
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (96 + bsize) 1

private theorem eq_ofNat_small (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b) =
      if b = a then UInt256.ofNat 1 else UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a = b
  · subst b; rfl
  · have hs : b ≠ a := Ne.symm h
    simp [h, hs]

theorem guardWord_spec (mem input : ByteArray) (n bsize esize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize)) :
    guardWord mem input n esize =
      if esize = 1 ∧ FixedExponentRoute.exponentValue input bsize 1 = 3 ∧ (n = 4 ∨ n = 8)
        then UInt256.ofNat 1 else UInt256.ofNat 0 := by
  have hwidth : UInt256.isZero (UInt256.land (UInt256.ofNat 3) (UInt256.ofNat n)) =
      if n = 4 ∨ n = 8 then UInt256.ofNat 1 else UInt256.ofNat 0 := by
    interval_cases n <;> decide
  have hv : FixedExponentRoute.exponentValue input bsize 1 < 2 ^ 256 :=
    (exponentValue_one_lt input bsize).trans (by decide)
  rw [guardWord, exponentByte_spec mem input bsize hb heoff, hwidth,
    eq_ofNat_small 3 _ (by decide) hv, eq_ofNat_small 1 esize (by decide) (by omega)]
  by_cases he1 : esize = 1 <;>
    by_cases hx : FixedExponentRoute.exponentValue input bsize 1 = 3 <;>
    by_cases hw : n = 4 ∨ n = 8 <;>
    simp [he1, hx, hw] <;> rfl

theorem shiftedCount_spec (mem input : ByteArray) (n bsize esize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize)) :
    UInt256.shiftRight (UInt256.ofNat n) (guardWord mem input n esize) =
      UInt256.ofNat (if esize = 1 ∧ FixedExponentRoute.exponentValue input bsize 1 = 3 ∧
        (n = 4 ∨ n = 8) then n / 2 else n) := by
  have hs1 : UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 1) =
      UInt256.ofNat (n / 2) := by interval_cases n <;> decide
  have hs0 : UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 0) =
      UInt256.ofNat n := by interval_cases n <;> decide
  rw [guardWord_spec mem input n bsize esize hn hn8 hb he heoff]
  split_ifs <;> assumption

#print axioms exponentByte_spec
#print axioms guardWord_spec
#print axioms shiftedCount_spec


theorem guardWord_zero_of_not_e3 (mem input : ByteArray) (n bsize esize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize))
    (hmiss : ¬ (esize = 1 ∧ FixedExponentRoute.exponentValue input bsize 1 = 3 ∧
      (n = 4 ∨ n = 8))) :
    guardWord mem input n esize = UInt256.ofNat 0 := by
  rw [guardWord_spec mem input n bsize esize hn hn8 hb he heoff, if_neg hmiss]

theorem result_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize))
    (hhit : esize = 1 ∧
      FixedExponentRoute.exponentValue s.executionEnv.calldata bsize 1 = 3 ∧ (n = 4 ∨ n = 8)) :
    result s mem n bsize esize msize =
      { s with
        pc := UInt256.ofNat 2691
        stack := UInt256.ofNat (n / 2) :: Exp.outer n bsize esize msize
        memory := Exp.storeWord mem 1760 (UInt256.ofNat 1) } := by
  unfold result
  rw [shiftedCount_spec mem s.executionEnv.calldata n bsize esize hn hn8 hb he heoff,
    guardWord_spec mem s.executionEnv.calldata n bsize esize hn hn8 hb he heoff,
    if_pos hhit]
  simp only [if_pos hhit]

theorem result_ordinary (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize))
    (hmiss : ¬ (esize = 1 ∧
      FixedExponentRoute.exponentValue s.executionEnv.calldata bsize 1 = 3 ∧ (n = 4 ∨ n = 8))) :
    result s mem n bsize esize msize =
      { s with
        pc := UInt256.ofNat 2691
        stack := UInt256.ofNat n :: Exp.outer n bsize esize msize
        memory := Exp.storeWord mem 1760 (UInt256.ofNat 0) } := by
  unfold result
  rw [shiftedCount_spec mem s.executionEnv.calldata n bsize esize hn hn8 hb he heoff,
    guardWord_spec mem s.executionEnv.calldata n bsize esize hn hn8 hb he heoff,
    if_neg hmiss]
  simp only [if_neg hmiss]

theorem quarter_counts (n : Nat) (hn : n = 4 ∨ n = 8) :
    n = 4 * (n / 4) ∧ n / 2 = 2 * (n / 4) ∧ 1 ≤ n / 4 ∧ n / 4 ≤ 2 := by
  rcases hn with rfl | rfl <;> decide

#print axioms guardWord_zero_of_not_e3
#print axioms result_e3
#print axioms result_ordinary
#print axioms quarter_counts
end RootE3Guard
