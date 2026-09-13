import Challenge.Modexp.Submission.Proofs.Fast.R4Value
import Mathlib.Algebra.Group.Fin.Basic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Diagonal
open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro R4Math

def diagSum (a tb t : UInt256) : UInt256 := t + a * (a + tb)

def diagCarry (a tb t k : UInt256) : UInt256 :=
  let f := a + tb
  let lo := a * f
  let z := UInt256.mulMod a f k - UInt256.lt f a
  (UInt256.lt (t + lo) t - (UInt256.lt z lo - z)) - lo

private theorem subFold (o b z l : UInt256) :
    o - (b - z) - l = (z - b - l) + o := by
  change UInt256.mk (o.val - (b.val - z.val) - l.val) =
    UInt256.mk ((z.val - b.val - l.val) + o.val)
  congr 1
  simp [sub_eq_add_neg, add_assoc, add_comm]

theorem diagCarry_add (a tb t : UInt256) :
    diagCarry a tb t maxWord =
      SquareDiag.diagHi a (a + tb) + UInt256.lt (diagSum a tb t) t := by
  unfold diagCarry diagSum SquareDiag.diagHi
  exact subFold _ _ _ _

private theorem high_bound (B H L X t : Nat) (hB : 0 < B)
    (ht : t < B) (hX : X ≤ (B - 1) * B) (heq : H * B + L = X + t) : H < B := by
  have hr : (B - 1) * B + B = B * B := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  have hlt : H * B < B * B := calc
    H * B ≤ H * B + L := Nat.le_add_right _ _
    _ = X + t := heq
    _ < (B - 1) * B + B := Nat.add_lt_add_of_le_of_lt hX ht
    _ = B * B := hr
  exact Nat.lt_of_mul_lt_mul_right hlt

theorem diagCell_spec (a tb t : UInt256) (htb : tb.toNat ≤ 1) :
    (diagCarry a tb t maxWord).toNat * 2 ^ 256 + (diagSum a tb t).toNat =
      a.toNat * (a.toNat + tb.toNat) + t.toNat := by
  have hd := SquareDiag.diag_spec a tb htb
  have ha := R4Math.add_spec t (a * (a + tb))
  have hx := R4Math.toNat_lt a
  have ht := R4Math.toNat_lt t
  have hprod : a.toNat * (a.toNat + tb.toNat) ≤ (2 ^ 256 - 1) * 2 ^ 256 :=
    Nat.mul_le_mul (by omega) (by omega)
  have htotal :
      ((SquareDiag.diagHi a (a + tb)).toNat + (UInt256.lt (diagSum a tb t) t).toNat) *
          2 ^ 256 + (diagSum a tb t).toNat =
        a.toNat * (a.toNat + tb.toNat) + t.toNat := by
    dsimp only [diagSum]
    nlinarith only [hd, ha]
  have hsum : (SquareDiag.diagHi a (a + tb)).toNat +
      (UInt256.lt (diagSum a tb t) t).toNat < 2 ^ 256 := by
    exact high_bound _ _ _ _ _ (by norm_num) ht hprod htotal
  rw [diagCarry_add, word_toNat_add, Nat.mod_eq_of_lt hsum]
  exact htotal

theorem diagonal_eq (a tb t : UInt256) (htb : tb.toNat ≤ 1) :
    diagCarry a tb t maxWord = mCarry a a (a * tb) t maxWord ∧
      diagSum a tb t = mSum a a (a * tb) t := by
  apply R4Math.pair_unique
  have hm := R4Math.mCell_spec a a (a * tb) t
  have hd := diagCell_spec a tb t htb
  have hb := R4Value.mul_bit a tb htb
  rw [hb] at hm
  rw [hd, hm]
  ring

#print axioms diagonal_eq

set_option linter.unusedSimpArgs false
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open R4Math

def diagProgram1 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def diag1Part0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩)]

theorem diag1Part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions diag1Part0 { s with pc := UInt256.ofNat 4917, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } =
    some { s with pc := UInt256.ofNat 4923, stack := [x1, (x1 + x0), ((x1 + x0) + x1), x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [diag1Part0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

def diag1Part1 : List Instr := [.op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩)]

theorem diag1Part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions diag1Part1 { s with pc := UInt256.ofNat 4923, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } =
    some { s with pc := UInt256.ofNat 4929, stack := [x0, x1, x0, (UInt256.mulMod x0 x1 x8), x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  simp [diag1Part1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

def diag1Part2 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB]

theorem diag1Part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions diag1Part2 { s with pc := UInt256.ofNat 4929, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } =
    some { s with pc := UInt256.ofNat 4935, stack := [(x3 - (UInt256.lt x1 x0)), (x2 * x1), x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  simp [diag1Part2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

def diag1Part3 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩)]

theorem diag1Part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions diag1Part3 { s with pc := UInt256.ofNat 4935, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } =
    some { s with pc := UInt256.ofNat 4941, stack := [x5, x1, ((UInt256.lt x0 x1) - x0), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [diag1Part3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def diag1Part4 : List Instr := [.op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

theorem diag1Part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions diag1Part4 { s with pc := UInt256.ofNat 4941, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } =
    some { s with pc := UInt256.ofNat 4947, stack := [(((UInt256.lt (x0 + x1) x7) - x2) - x3), x4, x5, x6, (x0 + x1), x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [diag1Part4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def diag1Part5 : List Instr := []

theorem diag1Part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010) :
    runInstructions diag1Part5 { s with pc := UInt256.ofNat 4947, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } =
    some { s with pc := UInt256.ofNat 4947, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [diag1Part5, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

theorem diagRun1 (s : State) (tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions diagProgram1
      { s with pc := UInt256.ofNat 4917, stack := [tb,a,p3,p2,p1,p0,p4,maxWord,n0,n1,n2,n3,np] ++ rest } =
    some { s with pc := UInt256.ofNat 4947, stack := [(diagCarry a tb p1 maxWord), ((a + tb) + a), p3, p2, (diagSum a tb p1), p0, p4, maxWord, n0, n1, n2, n3, np] ++ rest } := by
  have hsplit : diagProgram1 = diag1Part0 ++ (diag1Part1 ++ (diag1Part2 ++ (diag1Part3 ++ (diag1Part4 ++ (diag1Part5))))) := rfl
  rw [hsplit]
  have g0 := diag1Part0_run s tb a p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g1 := diag1Part1_run s a (a + tb) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g2 := diag1Part2_run s a (a + tb) a (UInt256.mulMod a (a + tb) maxWord) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g3 := diag1Part3_run s ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb)) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g4 := diag1Part4_run s p1 (a * (a + tb)) ((UInt256.lt ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb))) - ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a))) (a * (a + tb)) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g5 := diag1Part5_run s (((UInt256.lt (p1 + (a * (a + tb))) p1) - ((UInt256.lt ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb))) - ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)))) - (a * (a + tb))) ((a + tb) + a) p3 p2 (p1 + (a * (a + tb))) p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  simpa only [diagSum, diagCarry, List.cons_append, List.nil_append] using (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 (runInstructions_append_some _ _ _ _ _ g4 (g5))))))

#print axioms diagRun1

def diagProgram2 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def diag2Part0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩)]

theorem diag2Part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions diag2Part0 { s with pc := UInt256.ofNat 5030, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } =
    some { s with pc := UInt256.ofNat 5036, stack := [x1, (x1 + x0), ((x1 + x0) + x1), x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [diag2Part0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

def diag2Part1 : List Instr := [.op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩)]

theorem diag2Part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions diag2Part1 { s with pc := UInt256.ofNat 5036, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } =
    some { s with pc := UInt256.ofNat 5042, stack := [x0, x1, x0, (UInt256.mulMod x0 x1 x8), x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  simp [diag2Part1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

def diag2Part2 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB]

theorem diag2Part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions diag2Part2 { s with pc := UInt256.ofNat 5042, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } =
    some { s with pc := UInt256.ofNat 5048, stack := [(x3 - (UInt256.lt x1 x0)), (x2 * x1), x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  simp [diag2Part2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

def diag2Part3 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩)]

theorem diag2Part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions diag2Part3 { s with pc := UInt256.ofNat 5048, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } =
    some { s with pc := UInt256.ofNat 5054, stack := [x4, x1, ((UInt256.lt x0 x1) - x0), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [diag2Part3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def diag2Part4 : List Instr := [.op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

theorem diag2Part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions diag2Part4 { s with pc := UInt256.ofNat 5054, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } =
    some { s with pc := UInt256.ofNat 5060, stack := [(((UInt256.lt (x0 + x1) x6) - x2) - x3), x4, x5, (x0 + x1), x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [diag2Part4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def diag2Part5 : List Instr := []

theorem diag2Part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010) :
    runInstructions diag2Part5 { s with pc := UInt256.ofNat 5060, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } =
    some { s with pc := UInt256.ofNat 5060, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [diag2Part5, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

theorem diagRun2 (s : State) (tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions diagProgram2
      { s with pc := UInt256.ofNat 5030, stack := [tb,a,p3,p2,p1,p0,p4,maxWord,n0,n1,n2,n3,np] ++ rest } =
    some { s with pc := UInt256.ofNat 5060, stack := [(diagCarry a tb p2 maxWord), ((a + tb) + a), p3, (diagSum a tb p2), p1, p0, p4, maxWord, n0, n1, n2, n3, np] ++ rest } := by
  have hsplit : diagProgram2 = diag2Part0 ++ (diag2Part1 ++ (diag2Part2 ++ (diag2Part3 ++ (diag2Part4 ++ (diag2Part5))))) := rfl
  rw [hsplit]
  have g0 := diag2Part0_run s tb a p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g1 := diag2Part1_run s a (a + tb) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g2 := diag2Part2_run s a (a + tb) a (UInt256.mulMod a (a + tb) maxWord) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g3 := diag2Part3_run s ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb)) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g4 := diag2Part4_run s p2 (a * (a + tb)) ((UInt256.lt ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb))) - ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a))) (a * (a + tb)) ((a + tb) + a) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g5 := diag2Part5_run s (((UInt256.lt (p2 + (a * (a + tb))) p2) - ((UInt256.lt ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb))) - ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)))) - (a * (a + tb))) ((a + tb) + a) p3 (p2 + (a * (a + tb))) p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  simpa only [diagSum, diagCarry, List.cons_append, List.nil_append] using (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 (runInstructions_append_some _ _ _ _ _ g4 (g5))))))

#print axioms diagRun2

def diagProgram3 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def diag3Part0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩)]

theorem diag3Part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions diag3Part0 { s with pc := UInt256.ofNat 5114, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } =
    some { s with pc := UInt256.ofNat 5120, stack := [x1, (x1 + x0), x7, x1, (x1 + x0), x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [diag3Part0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def diag3Part1 : List Instr := [.op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩)]

theorem diag3Part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions diag3Part1 { s with pc := UInt256.ofNat 5120, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } =
    some { s with pc := UInt256.ofNat 5126, stack := [x3, x4, (UInt256.lt x4 x3), (UInt256.mulMod x0 x1 x2), x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [diag3Part1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def diag3Part2 : List Instr := [.op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT]

theorem diag3Part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions diag3Part2 { s with pc := UInt256.ofNat 5126, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14] ++ rest } =
    some { s with pc := UInt256.ofNat 5132, stack := [(UInt256.lt (x3 - x2) (x0 * x1)), (x3 - x2), (x0 * x1), x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [diag3Part2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

def diag3Part3 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩)]

theorem diag3Part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions diag3Part3 { s with pc := UInt256.ofNat 5132, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } =
    some { s with pc := UInt256.ofNat 5138, stack := [(x3 + x2), x3, (x0 - x1), x2, (x3 + x2), x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [diag3Part3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

def diag3Part4 : List Instr := [.op .LT, .op .SUB, .op .SUB]

theorem diag3Part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions diag3Part4 { s with pc := UInt256.ofNat 5138, stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14] ++ rest } =
    some { s with pc := UInt256.ofNat 5141, stack := [(((UInt256.lt x0 x1) - x2) - x3), x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14] ++ rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [diag3Part4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

theorem diagRun3 (s : State) (tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions diagProgram3
      { s with pc := UInt256.ofNat 5114, stack := [tb,a,p3,p2,p1,p0,p4,maxWord,n0,n1,n2,n3,np] ++ rest } =
    some { s with pc := UInt256.ofNat 5141, stack := [(diagCarry a tb p3 maxWord), (diagSum a tb p3), p2, p1, p0, p4, maxWord, n0, n1, n2, n3, np] ++ rest } := by
  have hsplit : diagProgram3 = diag3Part0 ++ (diag3Part1 ++ (diag3Part2 ++ (diag3Part3 ++ (diag3Part4)))) := rfl
  rw [hsplit]
  have g0 := diag3Part0_run s tb a p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g1 := diag3Part1_run s a (a + tb) maxWord a (a + tb) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g2 := diag3Part2_run s a (a + tb) (UInt256.lt (a + tb) a) (UInt256.mulMod a (a + tb) maxWord) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g3 := diag3Part3_run s (UInt256.lt ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb))) ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb)) p3 p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  have g4 := diag3Part4_run s (p3 + (a * (a + tb))) p3 ((UInt256.lt ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a)) (a * (a + tb))) - ((UInt256.mulMod a (a + tb) maxWord) - (UInt256.lt (a + tb) a))) (a * (a + tb)) (p3 + (a * (a + tb))) p2 p1 p0 p4 maxWord n0 n1 n2 n3 np rest (by omega)
  simpa only [diagSum, diagCarry, List.cons_append, List.nil_append] using (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 (g4)))))

#print axioms diagRun3

end Challenge.Modexp.Submission.Proofs.Fast.R4Diagonal
