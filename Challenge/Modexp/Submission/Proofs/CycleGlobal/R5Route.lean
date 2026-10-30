import Challenge.Modexp.Submission.Proofs.CycleGlobal.R5Head
import Challenge.Modexp.Submission.Proofs.Cycle.Finish
import Challenge.Modexp.Submission.Proofs.R5.Route
import Challenge.Modexp.Submission.Proofs.R5.PrologueMeaning

noncomputable section
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 4096

/-!
# The r5 route from the prologue at 5334

From the width-4 entry state the route either returns the 128-byte Montgomery result or, when
the prologue test fires (the top 40 bits of the staged operand are all ones), jumps to the
general MODEXP route at 219 with a short stack.

The width test jumps to the prologue (5334), which unpacks N, B and `A * 2^176` into 240-bit
digits (`PrologueMeaning`, `Digits`) and stores the scratch words; `Route.from_head` runs the
`k` squares, the product with B, the normalization and the pack.
-/

namespace CycleSubmission.Global.R5Route
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open CycleSubmission.R5.ExecPrologue CycleSubmission.R5.PrologueRun CycleSubmission.R5.PrologueMeaning
open CycleSubmission.R5.LoopRun CycleSubmission.R5.LoopMeaning

def result (N A B k : Nat) : Nat :=
  Model.montMul N (Limbs.radix^4) ((fun a => Model.montMul N (Limbs.radix^4) a a)^[k] A) B

theorem represents_congr {m1 m2 : ByteArray} {ptr X : Nat}
    (h : ∀ k < 4, MachineState.readWord m2 (ptr + 32 * (4 - 1 - k)) =
      MachineState.readWord m1 (ptr + 32 * (4 - 1 - k)))
    (hr : Model.FastRepresents m1 ptr 4 X) : Model.FastRepresents m2 ptr 4 X := by
  refine ⟨hr.1, ?_⟩
  rw [← hr.2]
  unfold Model.fastLimbs
  apply List.map_congr_left
  intro k hk
  rw [h k (List.mem_range.mp hk)]

theorem entry_represents {mem : ByteArray} {ptr X : Nat} (hp : ptr + 128 ≤ 2048)
    (hr : Model.FastRepresents mem ptr 4 X) : Model.FastRepresents (R5Head.entryMemory mem) ptr 4 X :=
  represents_congr (fun k hk => R5Head.entryMemory_read mem _ (Or.inl (by omega))) hr

theorem eq_toNat (a b : UInt256) : (UInt256.eq a b).toNat = if a.toNat = b.toNat then 1 else 0 := by
  simp only [UInt256.eq]
  split <;> norm_num [UInt256.ofNat, UInt256.toNat, UInt256.size]

/-- The state at the r5 prologue 5334 with a sixteen-word frame `f0 .. f15` above `rest`. -/
def entry (s : State) (em : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5334, memory := em, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest}

theorem prologue_route (s : State) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (em : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 100) (k N A B : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hf14 : f14 = UInt256.ofNat (k - 1))
    (hmod : Model.FastRepresents em 0 4 N) (ha : Model.FastRepresents em 2112 4 A)
    (hb : Model.FastRepresents em 256 4 B)
    (hinv : (N % Limbs.radix * f11.toNat + 1) % 2^256 = 0)
    (hodd : N % 2 = 1) (hA : A < N) (hB : B < N) :
    Nonempty (CycleSubmission.Finish.Outcome (entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest)
        (Precompile.natToBytes (result N A B k) 128)) ∨
    ∃ (stk : List UInt256) (m' : ByteArray),
      Nonempty (GasSteps (entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest)
        {s with pc := UInt256.ofNat 219, stack := stk, memory := m'}) ∧ stk.length < 900 := by
  have N_lt : N < 2^1024 := by simpa [Limbs.radix, ← pow_mul] using hmod.1
  have A_lt : A < 2^1024 := by omega
  have hNpos : 0 < N := by omega
  -- the execution up to the test at 5464
  have g1 : GasSteps (entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with pc := UInt256.ofNat 5334} :=
    GasSteps.refl _
  have g2 := CycleSubmission.R5.Blocks.proSegBlock.steps
    (s := {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with pc := UInt256.ofNat 5334, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest}) (env.transfer rfl rfl) rfl
    (proSeg_run (entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest (by omega) hact)
  have g3 := CycleSubmission.R5.Blocks.ctl5464_steps {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with memory := proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15}
    (proSegV8_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) ((proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest) (env.transfer rfl rfl) (by simp only [List.length_cons]; omega)
  by_cases hcond : (proSegV8_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = 0
  swap
  · right
    refine ⟨(proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest, proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, ⟨(g1.trans g2).trans (g3.cast rfl (by rw [if_neg hcond]; rfl))⟩, ?_⟩
    simp only [List.length_cons]; omega
  left
  -- digit values
  have dn0 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 160).toNat = N % 2^240 := by
    rw [m7_n0]; simpa using CycleSubmission.R5.Digits.window hmod 96 0 (by norm_num)
  have dn1 : (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = N / 2^240 % 2^240 := by
    rw [v_n1]; simpa using CycleSubmission.R5.Digits.window hmod 66 30 (by norm_num)
  have dn2 : (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = N / 2^480 % 2^240 := by
    rw [v_n2]; simpa using CycleSubmission.R5.Digits.window hmod 36 60 (by norm_num)
  have dn3 : (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = N / 2^720 % 2^240 := by
    rw [v_n3]; simpa using CycleSubmission.R5.Digits.window hmod 6 90 (by norm_num)
  have dn4 : (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = N / 2^960 := by
    rw [v_n4]; simpa using CycleSubmission.R5.Digits.top hmod 192 (by norm_num)
  have db0 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 0).toNat = B % 2^240 := by
    rw [m7_b0]; simpa using CycleSubmission.R5.Digits.window hb 96 0 (by norm_num)
  have db1 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 32).toNat = B / 2^240 % 2^240 := by
    rw [m7_b1]; simpa using CycleSubmission.R5.Digits.window hb 66 30 (by norm_num)
  have db2 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 64).toNat = B / 2^480 % 2^240 := by
    rw [m7_b2]; simpa using CycleSubmission.R5.Digits.window hb 36 60 (by norm_num)
  have db3 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 96).toNat = B / 2^720 % 2^240 := by
    rw [m7_b3]; simpa using CycleSubmission.R5.Digits.window hb 6 90 (by norm_num)
  have db4 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 128).toNat = B / 2^960 := by
    rw [m7_b4]; simpa using CycleSubmission.R5.Digits.top hb 192 (by norm_num)
  have dx0 : (blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = A % 2^64 * 2^176 := by
    simp only [blk5467_o0]; rw [m7_mask', m7_high em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 2208 (by norm_num)]
    simpa using CycleSubmission.R5.Digits.low_shifted ha
  have dx1 : (blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = A / 2^64 % 2^240 := by
    simp only [blk5467_o1]; rw [m7_mask', m7_high em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 2200 (by norm_num)]
    simpa using CycleSubmission.R5.Digits.window ha 88 8 (by norm_num)
  have dx2 : (blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = A / 2^304 % 2^240 := by
    simp only [blk5467_o2]; rw [m7_mask', m7_high em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 2170 (by norm_num)]
    simpa using CycleSubmission.R5.Digits.window ha 58 38 (by norm_num)
  have dx3 : (blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = A / 2^544 % 2^240 := by
    simp only [blk5467_o3]; rw [m7_mask', m7_high em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 2140 (by norm_num)]
    simpa using CycleSubmission.R5.Digits.window ha 28 68 (by norm_num)
  have t16 : (UInt256.shiftRight (MachineState.readWord em 2112) (UInt256.ofNat 16)).toNat = A / 2^784 := by
    simpa using CycleSubmission.R5.Digits.top ha 16 (by norm_num)
  have dx4 : (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat = A / 2^784 := by rw [v_x4]; exact t16
  -- digit bounds
  have hr : (0:Nat) < 2^240 := by norm_num
  have top_lt : ∀ X : Nat, X < 2^1024 → X / 2^960 < 2^240 := fun X hX => by omega
  have hn1 : (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dn1]; exact Nat.mod_lt _ hr
  have hn2 : (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dn2]; exact Nat.mod_lt _ hr
  have hn3 : (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dn3]; exact Nat.mod_lt _ hr
  have hn4 : (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dn4]; exact top_lt N N_lt
  have B_lt : B < 2^1024 := by omega
  have hb0 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 0).toNat < CycleSubmission.WordArithmetic.radix := by rw [db0]; exact Nat.mod_lt _ hr
  have hb1 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 32).toNat < CycleSubmission.WordArithmetic.radix := by rw [db1]; exact Nat.mod_lt _ hr
  have hb2 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 64).toNat < CycleSubmission.WordArithmetic.radix := by rw [db2]; exact Nat.mod_lt _ hr
  have hb3 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 96).toNat < CycleSubmission.WordArithmetic.radix := by rw [db3]; exact Nat.mod_lt _ hr
  have hb4 : (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 128).toNat < CycleSubmission.WordArithmetic.radix := by rw [db4]; exact top_lt B B_lt
  have hx0 : (blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dx0]; show _ < 2^240; omega
  have hx1 : (blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dx1]; exact Nat.mod_lt _ hr
  have hx2 : (blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dx2]; exact Nat.mod_lt _ hr
  have hx3 : (blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dx3]; exact Nat.mod_lt _ hr
  have hx4 : (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15).toNat < CycleSubmission.WordArithmetic.radix := by rw [dx4]; show _ < 2^240; omega
  -- values
  have hNval : N = val ⟨MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 160, proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15⟩ := by
    unfold val; dsimp only; rw [dn0, dn1, dn2, dn3, dn4]; exact (CycleSubmission.R5.Digits.value0 N).symm
  have hBval : val ⟨MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 0, MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 32,
      MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 64, MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 96, MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 128⟩ = B := by
    unfold val; dsimp only; rw [db0, db1, db2, db3, db4]; exact CycleSubmission.R5.Digits.value0 B
  have hxval : val ⟨blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15⟩ = A * 2^176 := by
    unfold val; dsimp only; rw [dx0, dx1, dx2, dx3, dx4]; exact CycleSubmission.R5.Digits.value176 A
  -- the test: the top 40 bits of A are not all ones, so `A * 2^176 + 2N ≤ R`
  have hxb : val ⟨blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15⟩ + 2 * N ≤ CycleSubmission.R5.RouteMath.R := by
    rw [v_cond, eq_toNat] at hcond
    split_ifs at hcond with hh
    rw [Word.shiftRight_toNat _ (by norm_num : 200 < 256), Nat.shiftRight_eq_div_pow, t16,
      Nat.div_div_eq_div_mul, ← pow_add, Word.word_toNat_ofNat] at hh
    norm_num at hh
    have hq : A / 2^984 < 2^40 := by omega
    have hA1 : A < A / 2^984 * 2^984 + 2^984 := Nat.lt_div_mul_add (by positivity)
    rw [hxval]; unfold CycleSubmission.R5.RouteMath.R; omega
  have hw : ((val ⟨blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15⟩ : Nat) : ZMod N) =
      ((A : ZMod N) * (CycleSubmission.R5.RouteMath.R4 : ZMod N)⁻¹) * CycleSubmission.R5.RouteMath.R := by
    rw [hxval]; exact CycleSubmission.R5.RouteMath.start_zmod hodd A
  have hN : (N * f11.toNat + 1) % 2^256 = 0 := by
    have h := Nat.ModEq.add_right 1 (Nat.ModEq.mul_right f11.toNat (Nat.mod_modEq N (2^256)))
    unfold Nat.ModEq at h
    rw [← h]; simpa [Limbs.radix] using hinv
  have hc : f14.toNat = k - 1 := by
    rw [hf14, Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  -- the rest of the prologue and the route from the loop head
  have g3' := g3.cast rfl (by rw [if_pos hcond])
  have g4 := CycleSubmission.R5.Blocks.blk5467Block.steps
    (s := {{entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with memory := proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15} with pc := UInt256.ofNat 5467, stack := (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest})
    (env.transfer rfl rfl) rfl
    ((blk5467_run {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with memory := proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15} (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest (by omega) hact).trans
      (congrArg some (blk5467_eq {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with memory := proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15} (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest)))
  have g5 := CycleSubmission.R5.Blocks.ctl5502_steps {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with memory := proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15}
    ((blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest) (env.transfer rfl rfl)
    (by simp only [List.length_cons]; omega)
  obtain ⟨t, ⟨gt⟩, hh, hret, hcs⟩ := CycleSubmission.R5.Route.from_head
    {entry s em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest with memory := proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15} (env.transfer rfl rfl) hact (f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest)
    (by simp only [List.length_cons]; omega)
    ⟨blk5467_o0 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o1 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o2 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, blk5467_o3 (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, proSegV8_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15⟩
    (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 160) (proSegV2_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_1 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_2 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV2_3 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)
    (proSegV2_4 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (proSegV0_0 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) f11
    (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 0) (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 32) (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 64)
    (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 96) (MachineState.readWord (proSegM7 em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 128) f14 N B k
    ((A : ZMod N) * (CycleSubmission.R5.RouteMath.R4 : ZMod N)⁻¹)
    (v_inv em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (v_P em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) hn1 hn2 hn3 hn4 dn0 hN hNval hodd N_lt rfl rfl rfl rfl rfl rfl
    (m7_inv' em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) (m7_mask' em f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) ⟨hb0, hb1, hb2, hb3, hb4⟩ hBval hB hk hc
    ⟨hx0, hx1, hx2, hx3, hx4⟩ hxb hw
  refine ⟨⟨t, (((g1.trans g2).trans g3').trans g4).trans (g5.trans gt), hh, ?_, hcs⟩⟩
  rw [hret, show result N A B k = CycleSubmission.R5.RouteMath.result N A B k from rfl,
    CycleSubmission.R5.RouteMath.result_zmod hNpos hodd]

theorem route (s : State) (mem : ByteArray) (bsize esize k N A B : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat)
    (hmod : Model.FastRepresents mem 0 4 N)
    (ha : Model.FastRepresents mem 2112 4 A)
    (hb : Model.FastRepresents mem 256 4 B)
    (hinv : (N % Limbs.radix * (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0)
    (hodd : N % 2 = 1) (hA : A < N) (hB : B < N) :
    Nonempty (CycleSubmission.Finish.Outcome (R5Head.entryState s mem bsize esize k)
        (Precompile.natToBytes (result N A B k) 128)) ∨
    ∃ (stk : List UInt256) (m' : ByteArray),
      Nonempty (GasSteps (R5Head.entryState s mem bsize esize k)
        {s with pc := UInt256.ofNat 219, stack := stk, memory := m'}) ∧ stk.length < 900 :=
  prologue_route s env hact (R5Head.entryMemory mem) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (UInt256.ofNat k :: Exp.outer 4 bsize esize 128) (by simp [Exp.outer]) k N A B hk hk16 rfl
    (entry_represents (by norm_num) hmod) (R5Head.entryMemory_represents mem A ha)
    (entry_represents (by norm_num) hb) hinv hodd hA hB

end CycleSubmission.Global.R5Route
