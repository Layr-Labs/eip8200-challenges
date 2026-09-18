import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

theorem isTrue_isZero (value : UInt256) :
    UInt256.isTrue (UInt256.isZero value) ↔ value.toNat = 0 := by
  unfold UInt256.isTrue
  rw [Challenge.EvmProof.Word.word_toNat_isZero]
  by_cases h : value.toNat = 0 <;> simp [h]

def testProgram (target : UInt256) : List Instr :=
  [.op .ISZERO, .push 2 target, .op .JUMPI]

theorem run_test (template : State) (pc target value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (testProgram target) (framed template pc (value :: rest)) =
    some (framed template (if value.toNat = 0 then target else advancePC 5 pc) rest) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hpush : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  by_cases hv : value.toNat = 0 <;>
    simp [runInstructions, testProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap1, hcap2, htarget, isTrue_isZero, hv, advancePC, succ_eq_add,
      hpush, word_add_assoc]

def widthDiff (baseSize exponentSize modulusSize : UInt256) : UInt256 :=
  UInt256.lor (UInt256.xor modulusSize (UInt256.ofNat 32))
    (UInt256.lor (UInt256.xor exponentSize (UInt256.ofNat 32))
      (UInt256.gt baseSize (UInt256.ofNat 32)))

private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  rw [Fin.xor_val, Fin.xor_val, Nat.xor_comm]

def widthValueProgram : List Instr :=
  [.op .JUMPDEST, .push 1 32, .op (.Dup ⟨1, by decide⟩), .op .GT,
   .op (.Dup ⟨2, by decide⟩), .push 1 32, .op .XOR, .op .OR,
   .op (.Dup ⟨3, by decide⟩), .push 1 32, .op .XOR, .op .OR]

theorem run_width_value (template : State) (baseSize exponentSize modulusSize : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 997) :
    runInstructions widthValueProgram
      (framed template (UInt256.ofNat 804) ([baseSize, exponentSize, modulusSize] ++ tail)) =
    some (framed template (UInt256.ofNat 819)
      (widthDiff baseSize exponentSize modulusSize :: [baseSize, exponentSize, modulusSize] ++ tail)) := by
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hcap4 : tail.length + 4 < 1024 := by omega
  have hcap5 : tail.length + 5 < 1024 := by omega
  have hcap6 : tail.length + 6 < 1024 := by omega
  simp [runInstructions, widthValueProgram, framed, widthDiff,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, hcap5, hcap6, Nat.add_assoc, xor_comm,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

def shortTestProgram (target : UInt256) : List Instr :=
  [.op .ISZERO, .push 1 target, .op .JUMPI]

theorem run_short_test (template : State) (pc target value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (shortTestProgram target) (framed template pc (value :: rest)) =
    some (framed template (if value.toNat = 0 then target else advancePC 4 pc) rest) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  by_cases hv : value.toNat = 0 <;>
    simp [runInstructions, shortTestProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap1, hcap2, htarget, isTrue_isZero, hv, advancePC, succ_eq_add,
      hpush, word_add_assoc]



def shortBranchProgram (target : UInt256) : List Instr :=
  [.push 1 target, .op .JUMPI]

theorem run_short_branch (template : State) (pc target value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (shortBranchProgram target) (framed template pc (value :: rest)) =
    some (framed template (if value.toNat = 0 then advancePC 3 pc else target) rest) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  by_cases hv : value.toNat = 0 <;>
    simp [runInstructions, shortBranchProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap1, hcap2, htarget, UInt256.isTrue, hv, advancePC, succ_eq_add,
      hpush, word_add_assoc]

/-- The width test at 1752 branches straight to the legacy word entry 144 on a
miss and falls through to the hit tail on a match. -/
def widthProgram : List Instr := widthValueProgram ++ shortBranchProgram (UInt256.ofNat 135)

theorem run_width (template : State) (baseSize exponentSize modulusSize : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 997)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 135 = true) :
    runInstructions widthProgram
      (framed template (UInt256.ofNat 804) ([baseSize, exponentSize, modulusSize] ++ tail)) =
    some (framed template
      (if (widthDiff baseSize exponentSize modulusSize).toNat = 0
        then UInt256.ofNat 822 else UInt256.ofNat 135)
      ([baseSize, exponentSize, modulusSize] ++ tail)) := by
  have hv := run_width_value template baseSize exponentSize modulusSize tail htail
  have ht := run_short_branch template (UInt256.ofNat 819) (UInt256.ofNat 135)
    (widthDiff baseSize exponentSize modulusSize) ([baseSize, exponentSize, modulusSize] ++ tail)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 3 (UInt256.ofNat 819) = UInt256.ofNat 822 := by decide
  simpa only [widthProgram, framed, hpc] using both

/-- Hit tail at 1770: drop the two copies on top of the route frame and hand the
remaining ten words to the adapter at 115. -/
def hitTailProgram : List Instr := [.op .POP, .op .POP, .push 1 116, .op .JUMP]

theorem run_hit_tail (template : State) (x y : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 116 = true) :
    runInstructions hitTailProgram (framed template (UInt256.ofNat 822) (x :: y :: rest)) =
    some (framed template (UInt256.ofNat 116) rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  simp [runInstructions, hitTailProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, hcap2, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, htarget,
    Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Adapter at 115: discard the seven route words above the three header sizes
and re-enter the early one-word entry at 25 with exactly the header stack. -/
def adapterProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push 1 25, .op .JUMP]

theorem run_adapter (template : State) (a b c d e f g : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 25 = true) :
    runInstructions adapterProgram
      (framed template (UInt256.ofNat 116) (a :: b :: c :: d :: e :: f :: g :: rest)) =
    some (framed template (UInt256.ofNat 25) rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, adapterProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, htarget,
    Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Entry of the one-word core at pc 2240 (0x8c0). Both special-modulus misses
jump here with the loaded modulus word on top of the route frame and `POP`
discards it. There is no base-width branch: a zero-width base runs the core
with the base word `CALLDATALOAD 96 >> 256 = 0`. -/
def baseProgram : List Instr :=
  [.op .JUMPDEST]

theorem run_base (template : State) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions baseProgram (framed template (UInt256.ofNat 827) (value :: rest)) =
    some (framed template (UInt256.ofNat 828) (value :: rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [runInstructions, baseProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap1, Challenge.EvmProof.Word.succ_ofNat_mod]


/-- 1776: keep a spare copy of the modulus word under the working copy and
preload calldata offset 96; four inert jump destinations preserve the byte PCs. -/
def modulusProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 96]

theorem run_modulus (template : State)
    (value : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 999) :
    runInstructions modulusProgram (framed template (UInt256.ofNat 828) (value :: rest)) =
    some (framed template (UInt256.ofNat 831)
      (UInt256.ofNat 96 :: value :: value :: rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  simp [runInstructions, modulusProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap1, hcap2, h96Word, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

/-- 1783: load the base word at the preloaded calldata offset 96 and normalize it by the declared base
width, which now sits at depth five under the two modulus copies. -/
def normalizeProgram : List Instr :=
  [.op .CALLDATALOAD, .op (.Dup ⟨7, by decide⟩), .push 1 32, .op .SUB, .push 1 3, .op .SHL,
   .op .SHR]

theorem run_normalize (template : State) (modulus : UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hbase : rest[5]? = some (UInt256.ofNat baseSize)) :
    runInstructions normalizeProgram
      (framed template (UInt256.ofNat 831) (UInt256.ofNat 96 :: modulus :: rest)) =
    some (framed template (UInt256.ofNat 840)
      (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata 96)
        (UInt256.ofNat ((32 - baseSize) * 8)) :: modulus :: rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hwidth (by decide : 32 < 2 ^ 256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat baseSize) (UInt256.ofNat 3) =
      UInt256.ofNat ((32 - baseSize) * 8) := by
    rw [hsub, Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
    congr 1
  have h96 : (UInt256.ofNat 96).toNat = 96 := by decide
  simp [runInstructions, normalizeProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap2, hcap3, hcap4, List.getElem?_cons_succ, hbase, h96,
    Challenge.EvmProof.Word.literal_eq_ofNat, hshift,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]


end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
