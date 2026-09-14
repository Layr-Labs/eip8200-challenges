import Challenge.Modexp.Submission.Proofs.Fast.R4Diagonal
import Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
import Mathlib.Algebra.Group.Fin.Basic
import Challenge.Modexp.Submission.Proofs.Fast.N0Carry

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4：各切片的符号执行（机器生成，勿手改；gen/emit2.py）

每段切成小块；小块在新鲜变量上符号执行，段定理把小块拼起来。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Runs

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.R4Blocks Challenge.Modexp.Submission.Proofs.Fast.R4Math

def prog_pd0 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨7, by decide⟩), .push 0 0, .op .MLOAD, .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨12, by decide⟩)]

theorem run_pd0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 n3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (hn3 : MachineState.readWord s.memory 0 = n3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_pd0
      { s with pc := UInt256.ofNat 4798, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4805, stack := x8 :: x11 :: x12 :: n3 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
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
  have hc18 : rest.length + 18 < 1024 := by omega
  have hl0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [prog_pd0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hl0, hn3, Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]


def prog_pd1 : List Instr :=
  [.push 2 2464, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩)]

theorem run_pd1 (s : State) (a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1019)
    (ha0 : MachineState.readWord s.memory 2464 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_pd1
      { s with pc := UInt256.ofNat 4805, stack := rest } =
    some { s with pc := UInt256.ofNat 4814, stack := a0 :: a0 :: (a0 + a0) :: a0 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hl2464 : (2464 : UInt256).toNat = 2464 := rfl
  simp [prog_pd1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hl2464, ha0, Monpro.activeWords_fix s 2464 32 (by decide) (by norm_num) hact, hc0, hc1, hc2, hc3, hc4]


def prog_pd2 : List Instr :=
  [.op .MUL, .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩)]

theorem run_pd2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions prog_pd2
      { s with pc := UInt256.ofNat 4814, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4821, stack := (UInt256.mulMod x3 x3 x14) :: (UInt256.mulMod x3 x3 x14) :: (x0 * x1) :: x2 :: x14 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
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
  simp [prog_pd2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]


def prog_pd3 : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op .GT, .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

theorem run_pd3 (s : State) (x0 x1 x2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1019) :
    runInstructions prog_pd3
      { s with pc := UInt256.ofNat 4821, stack := x0 :: x1 :: x2 :: rest } =
    some { s with pc := UInt256.ofNat 4827, stack := ((x1 - (UInt256.gt x2 x0)) - x2) :: x2 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [prog_pd3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4]


private theorem fusedBorrow_neg (a b c : UInt256) :
    b - a - c = (⟨0⟩ : UInt256) - (c + (a - b)) := by
  change UInt256.mk (b.val - a.val - c.val) = UInt256.mk (0 - (c.val + (a.val - b.val)))
  congr 1
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Universal symbolic execution of the merged entry and first diagonal. -/
theorem run_prodiag (s : State) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 n3 a0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hn3 : MachineState.readWord s.memory 0 = n3)
    (ha0 : MachineState.readWord s.memory 2464 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_prodiag
      { s with pc := UInt256.ofNat 4798,
               stack := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest } =
    some { s with pc := UInt256.ofNat 4827,
                  stack := dHi a0 e5 :: (a0 * a0) :: (a0 + a0) :: e5 :: e8 :: e11 :: e12 :: n3 :: e7 ::
                    e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest } := by
  have hs : prog_prodiag = prog_pd0 ++ (prog_pd1 ++ (prog_pd2 ++ prog_pd3)) := rfl
  rw [hs]
  have g0 := run_pd0 s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 n3 rest (by omega) hn3 hact
  have g1 := run_pd1 s a0
    (e8 :: e11 :: e12 :: n3 :: e7 :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega) ha0 hact
  have g2 := run_pd2 s a0 a0 (a0 + a0) a0 e8 e11 e12 n3 e7 e0 e1 e2 e3 e4 e5
    (e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega)
  have g3 := run_pd3 s (UInt256.mulMod a0 a0 e5) (UInt256.mulMod a0 a0 e5) (a0 * a0)
    ((a0 + a0) :: e5 :: e8 :: e11 :: e12 :: n3 :: e7 :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega)
  have g23 := runInstructions_append_some _ _ _ _ _ g2 g3
  have g123 := runInstructions_append_some _ _ _ _ _ g1 g23
  have g := runInstructions_append_some _ _ _ _ _ g0 g123
  simpa only [fusedBorrow_neg, dHi] using g


def prog_r0z1_0 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r0z1_0 (s : State) (x0 x1 x2 x3 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015)
    (ha1 : MachineState.readWord s.memory 2432 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z1_0
      { s with pc := UInt256.ofNat 4827, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4836,
                  stack := a1 :: x3 :: (a1 * x2) :: x0 :: x1 :: x2 :: x3 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hl2432 : (2432 : UInt256).toNat = 2432 := rfl
  simp [hc0, hz0, prog_r0z1_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hl2432, ha1, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2432 32 (by decide) (by norm_num) hact]

def prog_r0z1_1 : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r0z1_1 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) :
    runInstructions prog_r0z1_1
      { s with pc := UInt256.ofNat 4836, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4843,
                  stack := x2 :: ((UInt256.gt x2 (UInt256.mulMod x5 x0 x1)) - (UInt256.mulMod x5 x0 x1)) :: x2 :: x3 :: x4 :: x5 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [hc0, hz0, prog_r0z1_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7]

def prog_r0z1_2 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB]

theorem run_r0z1_2 (s : State) (x0 x1 x2 x3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prog_r0z1_2
      { s with pc := UInt256.ofNat 4843, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4850,
                  stack := (((UInt256.gt x3 (x3 + x0)) - x1) - x2) :: (x3 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [hc0, hz0, prog_r0z1_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5]

theorem prog_r0z1_split : prog_r0z1 = prog_r0z1_0 ++ (prog_r0z1_1 ++ (prog_r0z1_2)) := rfl

theorem run_r0z1 (s : State) (c t0 d k n0 n1 n2 n3 np a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010)
    (ha1 : MachineState.readWord s.memory 2432 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z1
      { s with pc := UInt256.ofNat 4827, stack := c :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4850,
                  stack := (zCarry a1 d c k) :: (zSum a1 d c) :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r0z1_split]
  have g0 := run_r0z1_0 s c t0 d k a1 (n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha1 := ha1) (hact := hact)
  have g1 := run_r0z1_1 s a1 k ((a1 * d)) c t0 d (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_r0z1_2 s ((a1 * d)) (((UInt256.gt (a1 * d) (UInt256.mulMod d a1 k)) - (UInt256.mulMod d a1 k))) ((a1 * d)) c (t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (g2))

def prog_r0z2_0 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r0z2_0 (s : State) (x0 x1 x2 x3 x4 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1014)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z2_0
      { s with pc := UInt256.ofNat 4850, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4859,
                  stack := a2 :: x4 :: (a2 * x3) :: x0 :: x1 :: x2 :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hl2400 : (2400 : UInt256).toNat = 2400 := rfl
  simp [hc0, hz0, prog_r0z2_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hl2400, ha2, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2400 32 (by decide) (by norm_num) hact]

def prog_r0z2_1 : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r0z2_1 (s : State) (x0 x1 x2 x3 x4 x5 x6 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015) :
    runInstructions prog_r0z2_1
      { s with pc := UInt256.ofNat 4859, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 4866,
                  stack := x2 :: ((UInt256.gt x2 (UInt256.mulMod x6 x0 x1)) - (UInt256.mulMod x6 x0 x1)) :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [hc0, hz0, prog_r0z2_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

def prog_r0z2_2 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB]

theorem run_r0z2_2 (s : State) (x0 x1 x2 x3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prog_r0z2_2
      { s with pc := UInt256.ofNat 4866, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4873,
                  stack := (((UInt256.gt x3 (x3 + x0)) - x1) - x2) :: (x3 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [hc0, hz0, prog_r0z2_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5]

theorem prog_r0z2_split : prog_r0z2 = prog_r0z2_0 ++ (prog_r0z2_1 ++ (prog_r0z2_2)) := rfl

theorem run_r0z2 (s : State) (c t1 t0 d k n0 n1 n2 n3 np a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z2
      { s with pc := UInt256.ofNat 4850, stack := c :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4873,
                  stack := (zCarry a2 d c k) :: (zSum a2 d c) :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r0z2_split]
  have g0 := run_r0z2_0 s c t1 t0 d k a2 (n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha2 := ha2) (hact := hact)
  have g1 := run_r0z2_1 s a2 k ((a2 * d)) c t1 t0 d (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_r0z2_2 s ((a2 * d)) (((UInt256.gt (a2 * d) (UInt256.mulMod d a2 k)) - (UInt256.mulMod d a2 k))) ((a2 * d)) c (t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (g2))

def prog_r0z3_0 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r0z3_0 (s : State) (x0 x1 x2 x3 x4 x5 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z3_0
      { s with pc := UInt256.ofNat 4873, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4882,
                  stack := a3 :: x5 :: (a3 * x4) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  have hl2368 : (2368 : UInt256).toNat = 2368 := rfl
  simp [hc0, hz0, prog_r0z3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hl2368, ha3, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2368 32 (by decide) (by norm_num) hact]

def prog_r0z3_1 : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r0z3_1 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1014) :
    runInstructions prog_r0z3_1
      { s with pc := UInt256.ofNat 4882, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4889,
                  stack := x2 :: ((UInt256.gt x2 (UInt256.mulMod x7 x0 x1)) - (UInt256.mulMod x7 x0 x1)) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [hc0, hz0, prog_r0z3_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9]

def prog_r0z3_2 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB]

theorem run_r0z3_2 (s : State) (x0 x1 x2 x3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prog_r0z3_2
      { s with pc := UInt256.ofNat 4889, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4896,
                  stack := (((UInt256.gt x3 (x3 + x0)) - x1) - x2) :: (x3 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [hc0, hz0, prog_r0z3_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5]

theorem prog_r0z3_split : prog_r0z3 = prog_r0z3_0 ++ (prog_r0z3_1 ++ (prog_r0z3_2)) := rfl

theorem run_r0z3 (s : State) (c t2 t1 t0 d k n0 n1 n2 n3 np a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z3
      { s with pc := UInt256.ofNat 4873, stack := c :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4896,
                  stack := (zCarry a3 d c k) :: (zSum a3 d c) :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r0z3_split]
  have g0 := run_r0z3_0 s c t2 t1 t0 d k a3 (n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha3 := ha3) (hact := hact)
  have g1 := run_r0z3_1 s a3 k ((a3 * d)) c t2 t1 t0 d (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_r0z3_2 s ((a3 * d)) (((UInt256.gt (a3 * d) (UInt256.mulMod d a3 k)) - (UInt256.mulMod d a3 k))) ((a3 * d)) c (t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (g2))

def prog_r0e_0 : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4906, .push 2 5149, .op .JUMP]

theorem run_r0e_0 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions prog_r0e_0
      { s with pc := UInt256.ofNat 4896, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := (5149 : UInt256),
                  stack := (4906 : UInt256) :: (⟨0⟩ : UInt256) :: x1 :: x2 :: x3 :: x4 :: x0 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hl4903 : (4906 : UInt256).toNat = 4906 := rfl
  have hl5158 : (5149 : UInt256).toNat = 5149 := rfl
  simp [hc0, hz0, prog_r0e_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hl4903, hl5158, hjd]

theorem prog_r0e_split : prog_r0e = prog_r0e_0 := rfl

theorem run_r0e (s : State) (c t3 t2 t1 t0 d k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions prog_r0e
      { s with pc := UInt256.ofNat 4896, stack := c :: t3 :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5149,
                  stack := (4906 : UInt256) :: (⟨0⟩ : UInt256) :: t3 :: t2 :: t1 :: t0 :: c :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r0e_split]
  have g0 := run_r0e_0 s c t3 t2 t1 t0 d (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hjd := hjd)
  exact g0

/-- The raw cancellation trace is unconditional; the model bridge below carries the guard. -/
theorem run_redm_addMod (s : State) (ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions prog_redm
      { s with pc := UInt256.ofNat 5149,
               stack := ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5160,
                  stack := UInt256.addMod p0 (UInt256.mulMod n0 (np*p0) k) k ::
                    (np*p0) :: ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
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
  have hc18 : rest.length + 18 < 1024 := by omega
  simp [prog_redm, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

theorem run_redm (s : State) (ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    runInstructions prog_redm
      { s with pc := UInt256.ofNat 5149,
               stack := ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5160,
                  stack := redC n0 (np*p0) p0 k :: (np*p0) :: ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have hr := run_redm_addMod s ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np rest hcap
  subst k
  rw [N0Carry.addMod_comm, N0Carry.addMod_redC n0 np p0 hminv hguard] at hr
  exact hr

def prog_reds1_0 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

theorem run_reds1_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions prog_reds1_0
      { s with pc := UInt256.ofNat 5160, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 5166,
                  stack := x1 :: x11 :: x9 :: (x11 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  simp [hc0, hz0, prog_reds1_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def prog_reds1_1 : List Instr :=
  [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩)]

theorem run_reds1_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prog_reds1_1
      { s with pc := UInt256.ofNat 5166, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5173,
                  stack := x4 :: x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [hc0, hz0, prog_reds1_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5]

def prog_reds1_2 : List Instr :=
  [.op .ADD, .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩)]

theorem run_reds1_2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010) :
    runInstructions prog_reds1_2
      { s with pc := UInt256.ofNat 5173, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 5180,
                  stack := ((x0 + x1) + x10) :: (x0 + x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: ((x0 + x1) + x10) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  simp [hc0, hz0, prog_reds1_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def prog_reds1_3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB,
   .op .ADD]

theorem run_reds1_3 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_reds1_3
      { s with pc := UInt256.ofNat 5180, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5187,
                  stack := ((((UInt256.gt x4 x1) - x2) - x3) + (UInt256.gt x1 x0)) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_reds1_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

theorem prog_reds1_split : prog_reds1 = prog_reds1_0 ++ (prog_reds1_1 ++ (prog_reds1_2 ++ (prog_reds1_3))) := rfl

theorem run_reds1 (s : State) (c m ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) :
    runInstructions prog_reds1
      { s with pc := UInt256.ofNat 5160, stack := c :: m :: ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5187,
                  stack := (sCarry n1 m c p1 k) :: m :: ret :: v :: p3 :: p2 :: p1 :: (mSum n1 m c p1) :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_reds1_split]
  have g0 := run_reds1_0 s c m ret v p3 p2 p1 p0 p4 k n0 n1 (n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_reds1_1 s m n1 k ((n1 * m)) c (m :: ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_reds1_2 s c ((n1 * m)) (((UInt256.gt (n1 * m) (UInt256.mulMod m n1 k)) - (UInt256.mulMod m n1 k))) ((n1 * m)) c m ret v p3 p2 p1 p0 (p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g3 := run_reds1_3 s (((c + (n1 * m)) + p1)) ((c + (n1 * m))) (((UInt256.gt (n1 * m) (UInt256.mulMod m n1 k)) - (UInt256.mulMod m n1 k))) ((n1 * m)) c (m :: ret :: v :: p3 :: p2 :: p1 :: ((c + (n1 * m)) + p1) :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (g3)))

def prog_reds2_0 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

theorem run_reds2_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions prog_reds2_0
      { s with pc := UInt256.ofNat 5187, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 5193,
                  stack := x1 :: x12 :: x9 :: (x12 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  simp [hc0, hz0, prog_reds2_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

def prog_reds2_1 : List Instr :=
  [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩)]

theorem run_reds2_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prog_reds2_1
      { s with pc := UInt256.ofNat 5193, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5200,
                  stack := x4 :: x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [hc0, hz0, prog_reds2_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5]

def prog_reds2_2 : List Instr :=
  [.op .ADD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩)]

theorem run_reds2_2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011) :
    runInstructions prog_reds2_2
      { s with pc := UInt256.ofNat 5200, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 5207,
                  stack := ((x0 + x1) + x9) :: (x0 + x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: ((x0 + x1) + x9) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  simp [hc0, hz0, prog_reds2_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12]

def prog_reds2_3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB,
   .op .ADD]

theorem run_reds2_3 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_reds2_3
      { s with pc := UInt256.ofNat 5207, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5214,
                  stack := ((((UInt256.gt x4 x1) - x2) - x3) + (UInt256.gt x1 x0)) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_reds2_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

theorem prog_reds2_split : prog_reds2 = prog_reds2_0 ++ (prog_reds2_1 ++ (prog_reds2_2 ++ (prog_reds2_3))) := rfl

theorem run_reds2 (s : State) (c m ret v p3 p2 p1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) :
    runInstructions prog_reds2
      { s with pc := UInt256.ofNat 5187, stack := c :: m :: ret :: v :: p3 :: p2 :: p1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5214,
                  stack := (sCarry n2 m c p2 k) :: m :: ret :: v :: p3 :: p2 :: (mSum n2 m c p2) :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_reds2_split]
  have g0 := run_reds2_0 s c m ret v p3 p2 p1 q0 p4 k n0 n1 n2 (n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_reds2_1 s m n2 k ((n2 * m)) c (m :: ret :: v :: p3 :: p2 :: p1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_reds2_2 s c ((n2 * m)) (((UInt256.gt (n2 * m) (UInt256.mulMod m n2 k)) - (UInt256.mulMod m n2 k))) ((n2 * m)) c m ret v p3 p2 p1 (q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g3 := run_reds2_3 s (((c + (n2 * m)) + p2)) ((c + (n2 * m))) (((UInt256.gt (n2 * m) (UInt256.mulMod m n2 k)) - (UInt256.mulMod m n2 k))) ((n2 * m)) c (m :: ret :: v :: p3 :: p2 :: ((c + (n2 * m)) + p2) :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (g3)))

def prog_reds3_0 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

theorem run_reds3_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions prog_reds3_0
      { s with pc := UInt256.ofNat 5214, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 5220,
                  stack := x1 :: x13 :: x9 :: (x13 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  have hc18 : rest.length + 18 < 1024 := by omega
  simp [hc0, hz0, prog_reds3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

def prog_reds3_1 : List Instr :=
  [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩)]

theorem run_reds3_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prog_reds3_1
      { s with pc := UInt256.ofNat 5220, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5227,
                  stack := x4 :: x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [hc0, hz0, prog_reds3_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5]

def prog_reds3_2 : List Instr :=
  [.op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩)]

theorem run_reds3_2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1012) :
    runInstructions prog_reds3_2
      { s with pc := UInt256.ofNat 5227, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest } =
    some { s with pc := UInt256.ofNat 5234,
                  stack := ((x0 + x1) + x8) :: (x0 + x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ((x0 + x1) + x8) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  simp [hc0, hz0, prog_reds3_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11]

def prog_reds3_3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB,
   .op .ADD]

theorem run_reds3_3 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_reds3_3
      { s with pc := UInt256.ofNat 5234, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5241,
                  stack := ((((UInt256.gt x4 x1) - x2) - x3) + (UInt256.gt x1 x0)) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_reds3_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

theorem prog_reds3_split : prog_reds3 = prog_reds3_0 ++ (prog_reds3_1 ++ (prog_reds3_2 ++ (prog_reds3_3))) := rfl

theorem run_reds3 (s : State) (c m ret v p3 p2 q1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) :
    runInstructions prog_reds3
      { s with pc := UInt256.ofNat 5214, stack := c :: m :: ret :: v :: p3 :: p2 :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5241,
                  stack := (sCarry n3 m c p3 k) :: m :: ret :: v :: p3 :: (mSum n3 m c p3) :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_reds3_split]
  have g0 := run_reds3_0 s c m ret v p3 p2 q1 q0 p4 k n0 n1 n2 n3 (np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_reds3_1 s m n3 k ((n3 * m)) c (m :: ret :: v :: p3 :: p2 :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_reds3_2 s c ((n3 * m)) (((UInt256.gt (n3 * m) (UInt256.mulMod m n3 k)) - (UInt256.mulMod m n3 k))) ((n3 * m)) c m ret v p3 p2 (q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g3 := run_reds3_3 s (((c + (n3 * m)) + p3)) ((c + (n3 * m))) (((UInt256.gt (n3 * m) (UInt256.mulMod m n3 k)) - (UInt256.mulMod m n3 k))) ((n3 * m)) c (m :: ret :: v :: p3 :: ((c + (n3 * m)) + p3) :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (g3)))

theorem run_redt (s : State) (c m ret v p3 q2 q1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstructions prog_redt
      { s with pc := UInt256.ofNat 5241, stack := c :: m :: ret :: v :: p3 :: q2 :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := ret,
                  stack := (p4 + c) :: q2 :: q1 :: q0 :: (v + (UInt256.lt (p4 + c) p4)) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
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
  simp [prog_redt, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    UInt256.gt, UInt256.lt, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_assoc, hjd, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def prog_r1h_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

theorem run_r1h_0 (s : State) (a1 a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020)
    (ha1 : MachineState.readWord s.memory 2432 = a1)
    (ha0 : MachineState.readWord s.memory 2464 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1h_0
      { s with pc := UInt256.ofNat 4906, stack := rest } =
    some { s with pc := UInt256.ofNat 4916,
                  stack := (⟨0⟩ : UInt256) :: a0 :: a1 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hl2432 : (2432 : UInt256).toNat = 2432 := rfl
  have hl2464 : (2464 : UInt256).toNat = 2464 := rfl
  simp [hc0, hz0, prog_r1h_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hl2432, hl2464, ha1, ha0, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2432 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2464 32 (by decide) (by norm_num) hact]

theorem prog_r1h_split : prog_r1h = prog_r1h_0 := rfl

theorem run_r1h (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a1 a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha1 : MachineState.readWord s.memory 2432 = a1)
    (ha0 : MachineState.readWord s.memory 2464 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1h
      { s with pc := UInt256.ofNat 4906, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4916,
                  stack := (⟨0⟩ : UInt256) :: a0 :: a1 :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r1h_split]
  have g0 := run_r1h_0 s a1 a0 (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha1 := ha1) (ha0 := ha0) (hact := hact)
  exact g0

theorem run_r1d (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions prog_r1d
      { s with pc := UInt256.ofNat 4917, stack := tb :: a :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4947,
                  stack := (mCarry a a (a * tb) p1 k) :: ((a + a) + tb) :: p3 :: p2 :: (mSum a a (a * tb) p1) :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }  := by
  subst k
  have h := R4Diagonal.diagRun1 s tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np rest hcap
  have he := R4Diagonal.diagonal_eq a tb p1 htb
  have hD : (a + tb) + a = (a + a) + tb := by
    change UInt256.mk ((a.val + tb.val) + a.val) = UInt256.mk ((a.val + a.val) + tb.val)
    congr 1
    simp [add_assoc, add_comm, add_left_comm]
  simpa only [R4Diagonal.diagProgram1, prog_r1d, he.1, he.2, hD, List.cons_append, List.nil_append] using h


def prog_r1c2_0 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r1c2_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c2_0
      { s with pc := UInt256.ofNat 4947, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4956,
                  stack := a2 :: x7 :: (a2 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  have hl2400 : (2400 : UInt256).toNat = 2400 := rfl
  simp [hc0, hz0, prog_r1c2_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hl2400, ha2, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2400 32 (by decide) (by norm_num) hact]

def prog_r1c2_1 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r1c2_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r1c2_1
      { s with pc := UInt256.ofNat 4956, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4963,
                  stack := x2 :: ((UInt256.gt x2 (UInt256.mulMod x4 x0 x1)) - (UInt256.mulMod x4 x0 x1)) :: x2 :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_r1c2_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

def prog_r1c2_2 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩)]

theorem run_r1c2_2 (s : State) (x0 x1 x2 x3 x4 x5 x6 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1014) :
    runInstructions prog_r1c2_2
      { s with pc := UInt256.ofNat 4963, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 4970,
                  stack := ((x3 + x0) + x6) :: x6 :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: ((x3 + x0) + x6) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [hc0, hz0, prog_r1c2_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9]

def prog_r1c2_3 : List Instr :=
  [.op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

theorem run_r1c2_3 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r1c2_3
      { s with pc := UInt256.ofNat 4970, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4976,
                  stack := ((((UInt256.gt x5 x2) - x3) - x4) + (UInt256.lt x0 x1)) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_r1c2_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

theorem prog_r1c2_split : prog_r1c2 = prog_r1c2_0 ++ (prog_r1c2_1 ++ (prog_r1c2_2 ++ (prog_r1c2_3))) := rfl

theorem run_r1c2 (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c2
      { s with pc := UInt256.ofNat 4947, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4976,
                  stack := (mCarry a2 d c p2 k) :: d :: p3 :: (mSum a2 d c p2) :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r1c2_split]
  have g0 := run_r1c2_0 s c d p3 p2 p1 p0 p4 k a2 (n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha2 := ha2) (hact := hact)
  have g1 := run_r1c2_1 s a2 k ((a2 * d)) c d (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_r1c2_2 s ((a2 * d)) (((UInt256.gt (a2 * d) (UInt256.mulMod d a2 k)) - (UInt256.mulMod d a2 k))) ((a2 * d)) c d p3 p2 (p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g3 := run_r1c2_3 s (((c + (a2 * d)) + p2)) p2 ((c + (a2 * d))) (((UInt256.gt (a2 * d) (UInt256.mulMod d a2 k)) - (UInt256.mulMod d a2 k))) ((a2 * d)) c (d :: p3 :: ((c + (a2 * d)) + p2) :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (g3)))

def prog_r1c3_0 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r1c3_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c3_0
      { s with pc := UInt256.ofNat 4976, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4985,
                  stack := a3 :: x7 :: (a3 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  have hl2368 : (2368 : UInt256).toNat = 2368 := rfl
  simp [hc0, hz0, prog_r1c3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hl2368, ha3, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2368 32 (by decide) (by norm_num) hact]

def prog_r1c3_1 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r1c3_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r1c3_1
      { s with pc := UInt256.ofNat 4985, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4992,
                  stack := x2 :: ((UInt256.gt x2 (UInt256.mulMod x4 x0 x1)) - (UInt256.mulMod x4 x0 x1)) :: x2 :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_r1c3_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

def prog_r1c3_2 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩)]

theorem run_r1c3_2 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015) :
    runInstructions prog_r1c3_2
      { s with pc := UInt256.ofNat 4992, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4999,
                  stack := ((x3 + x0) + x5) :: x5 :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: ((x3 + x0) + x5) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [hc0, hz0, prog_r1c3_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

def prog_r1c3_3 : List Instr :=
  [.op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

theorem run_r1c3_3 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r1c3_3
      { s with pc := UInt256.ofNat 4999, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 5005,
                  stack := ((((UInt256.gt x5 x2) - x3) - x4) + (UInt256.lt x0 x1)) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_r1c3_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

theorem prog_r1c3_split : prog_r1c3 = prog_r1c3_0 ++ (prog_r1c3_1 ++ (prog_r1c3_2 ++ (prog_r1c3_3))) := rfl

theorem run_r1c3 (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c3
      { s with pc := UInt256.ofNat 4976, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5005,
                  stack := (mCarry a3 d c p3 k) :: d :: (mSum a3 d c p3) :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r1c3_split]
  have g0 := run_r1c3_0 s c d p3 p2 p1 p0 p4 k a3 (n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha3 := ha3) (hact := hact)
  have g1 := run_r1c3_1 s a3 k ((a3 * d)) c d (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_r1c3_2 s ((a3 * d)) (((UInt256.gt (a3 * d) (UInt256.mulMod d a3 k)) - (UInt256.mulMod d a3 k))) ((a3 * d)) c d p3 (p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g3 := run_r1c3_3 s (((c + (a3 * d)) + p3)) p3 ((c + (a3 * d))) (((UInt256.gt (a3 * d) (UInt256.mulMod d a3 k)) - (UInt256.mulMod d a3 k))) ((a3 * d)) c (d :: ((c + (a3 * d)) + p3) :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (g3)))

def prog_r1e_0 : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP]

theorem run_r1e_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015) :
    runInstructions prog_r1e_0
      { s with pc := UInt256.ofNat 5005, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 5012,
                  stack := (UInt256.lt (x6 + x0) x6) :: x2 :: x3 :: x4 :: x5 :: (x6 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [hc0, hz0, prog_r1e_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

def prog_r1e_1 : List Instr :=
  [.push 2 5019, .push 2 5149, .op .JUMP]

theorem run_r1e_1 (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1021)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions prog_r1e_1
      { s with pc := UInt256.ofNat 5012, stack := rest } =
    some { s with pc := (5149 : UInt256),
                  stack := (5019 : UInt256) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hl5020 : (5019 : UInt256).toNat = 5019 := rfl
  have hl5158 : (5149 : UInt256).toNat = 5149 := rfl
  simp [hc0, hz0, prog_r1e_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hl5020, hl5158, hjd]

theorem prog_r1e_split : prog_r1e = prog_r1e_0 ++ (prog_r1e_1) := rfl

theorem run_r1e (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions prog_r1e
      { s with pc := UInt256.ofNat 5005, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5149,
                  stack := (5019 : UInt256) :: (UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r1e_split]
  have g0 := run_r1e_0 s c d p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_r1e_1 s  ((UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hjd := hjd)
  exact runInstructions_append_some _ _ _ _ _ g0 (g1)

def prog_r2h_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

theorem run_r2h_0 (s : State) (a2 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (ha1 : MachineState.readWord s.memory 2432 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2h_0
      { s with pc := UInt256.ofNat 5019, stack := rest } =
    some { s with pc := UInt256.ofNat 5029,
                  stack := (⟨0⟩ : UInt256) :: a1 :: a2 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hl2400 : (2400 : UInt256).toNat = 2400 := rfl
  have hl2432 : (2432 : UInt256).toNat = 2432 := rfl
  simp [hc0, hz0, prog_r2h_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hl2400, hl2432, ha2, ha1, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2400 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2432 32 (by decide) (by norm_num) hact]

theorem prog_r2h_split : prog_r2h = prog_r2h_0 := rfl

theorem run_r2h (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (ha1 : MachineState.readWord s.memory 2432 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2h
      { s with pc := UInt256.ofNat 5019, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5029,
                  stack := (⟨0⟩ : UInt256) :: a1 :: a2 :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r2h_split]
  have g0 := run_r2h_0 s a2 a1 (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha2 := ha2) (ha1 := ha1) (hact := hact)
  exact g0

theorem run_r2d (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions prog_r2d
      { s with pc := UInt256.ofNat 5030, stack := tb :: a :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5060,
                  stack := (mCarry a a (a * tb) p2 k) :: ((a + a) + tb) :: p3 :: (mSum a a (a * tb) p2) :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }  := by
  subst k
  have h := R4Diagonal.diagRun2 s tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np rest hcap
  have he := R4Diagonal.diagonal_eq a tb p2 htb
  have hD : (a + tb) + a = (a + a) + tb := by
    change UInt256.mk ((a.val + tb.val) + a.val) = UInt256.mk ((a.val + a.val) + tb.val)
    congr 1
    simp [add_assoc, add_comm, add_left_comm]
  simpa only [R4Diagonal.diagProgram2, prog_r2d, he.1, he.2, hD, List.cons_append, List.nil_append] using h


def prog_r2c3_0 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r2c3_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2c3_0
      { s with pc := UInt256.ofNat 5060, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 5069,
                  stack := a3 :: x7 :: (a3 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
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
  have hl2368 : (2368 : UInt256).toNat = 2368 := rfl
  simp [hc0, hz0, prog_r2c3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hl2368, ha3, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2368 32 (by decide) (by norm_num) hact]

def prog_r2c3_1 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r2c3_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r2c3_1
      { s with pc := UInt256.ofNat 5069, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5076,
                  stack := x2 :: ((UInt256.gt x2 (UInt256.mulMod x4 x0 x1)) - (UInt256.mulMod x4 x0 x1)) :: x2 :: x3 :: x4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_r2c3_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

def prog_r2c3_2 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩)]

theorem run_r2c3_2 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015) :
    runInstructions prog_r2c3_2
      { s with pc := UInt256.ofNat 5076, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 5083,
                  stack := ((x3 + x0) + x5) :: x5 :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: ((x3 + x0) + x5) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [hc0, hz0, prog_r2c3_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

def prog_r2c3_3 : List Instr :=
  [.op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

theorem run_r2c3_3 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r2c3_3
      { s with pc := UInt256.ofNat 5083, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 5089,
                  stack := ((((UInt256.gt x5 x2) - x3) - x4) + (UInt256.lt x0 x1)) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_r2c3_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

theorem prog_r2c3_split : prog_r2c3 = prog_r2c3_0 ++ (prog_r2c3_1 ++ (prog_r2c3_2 ++ (prog_r2c3_3))) := rfl

theorem run_r2c3 (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2c3
      { s with pc := UInt256.ofNat 5060, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5089,
                  stack := (mCarry a3 d c p3 k) :: d :: (mSum a3 d c p3) :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r2c3_split]
  have g0 := run_r2c3_0 s c d p3 p2 p1 p0 p4 k a3 (n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha3 := ha3) (hact := hact)
  have g1 := run_r2c3_1 s a3 k ((a3 * d)) c d (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g2 := run_r2c3_2 s ((a3 * d)) (((UInt256.gt (a3 * d) (UInt256.mulMod d a3 k)) - (UInt256.mulMod d a3 k))) ((a3 * d)) c d p3 (p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g3 := run_r2c3_3 s (((c + (a3 * d)) + p3)) p3 ((c + (a3 * d))) (((UInt256.gt (a3 * d) (UInt256.mulMod d a3 k)) - (UInt256.mulMod d a3 k))) ((a3 * d)) c (d :: ((c + (a3 * d)) + p3) :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (g3)))

def prog_r2e_0 : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP]

theorem run_r2e_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015) :
    runInstructions prog_r2e_0
      { s with pc := UInt256.ofNat 5089, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 5096,
                  stack := (UInt256.lt (x6 + x0) x6) :: x2 :: x3 :: x4 :: x5 :: (x6 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [hc0, hz0, prog_r2e_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

def prog_r2e_1 : List Instr :=
  [.push 2 5103, .push 2 5149, .op .JUMP]

theorem run_r2e_1 (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1021)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions prog_r2e_1
      { s with pc := UInt256.ofNat 5096, stack := rest } =
    some { s with pc := (5149 : UInt256),
                  stack := (5103 : UInt256) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hl5108 : (5103 : UInt256).toNat = 5103 := rfl
  have hl5158 : (5149 : UInt256).toNat = 5149 := rfl
  simp [hc0, hz0, prog_r2e_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hl5108, hl5158, hjd]

theorem prog_r2e_split : prog_r2e = prog_r2e_0 ++ (prog_r2e_1) := rfl

theorem run_r2e (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 5149 = true) :
    runInstructions prog_r2e
      { s with pc := UInt256.ofNat 5089, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5149,
                  stack := (5103 : UInt256) :: (UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r2e_split]
  have g0 := run_r2e_0 s c d p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_r2e_1 s  ((UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hjd := hjd)
  exact runInstructions_append_some _ _ _ _ _ g0 (g1)

def prog_r3h_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

theorem run_r3h_0 (s : State) (a3 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r3h_0
      { s with pc := UInt256.ofNat 5103, stack := rest } =
    some { s with pc := UInt256.ofNat 5113,
                  stack := (⟨0⟩ : UInt256) :: a2 :: a3 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hl2368 : (2368 : UInt256).toNat = 2368 := rfl
  have hl2400 : (2400 : UInt256).toNat = 2400 := rfl
  simp [hc0, hz0, prog_r3h_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hl2368, hl2400, ha3, ha2, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2368 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2400 32 (by decide) (by norm_num) hact]

theorem prog_r3h_split : prog_r3h = prog_r3h_0 := rfl

theorem run_r3h (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha3 : MachineState.readWord s.memory 2368 = a3)
    (ha2 : MachineState.readWord s.memory 2400 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r3h
      { s with pc := UInt256.ofNat 5103, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5113,
                  stack := (⟨0⟩ : UInt256) :: a2 :: a3 :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r3h_split]
  have g0 := run_r3h_0 s a3 a2 (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha3 := ha3) (ha2 := ha2) (hact := hact)
  exact g0

theorem run_r3d (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions prog_r3d
      { s with pc := UInt256.ofNat 5114, stack := tb :: a :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5141,
                  stack := (mCarry a a (a * tb) p3 k) :: (mSum a a (a * tb) p3) :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }  := by
  subst k
  have h := R4Diagonal.diagRun3 s tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np rest hcap
  have he := R4Diagonal.diagonal_eq a tb p3 htb
  simpa only [R4Diagonal.diagProgram3, prog_r3d, he.1, he.2, List.cons_append, List.nil_append] using h


def prog_r3e_0 : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .LT, .push 2 5255]

theorem run_r3e_0 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) :
    runInstructions prog_r3e_0
      { s with pc := UInt256.ofNat 5141, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 5149,
                  stack := (5255 : UInt256) :: (UInt256.lt (x5 + x0) x5) :: x1 :: x2 :: x3 :: x4 :: (x5 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hl5274 : (5255 : UInt256).toNat = 5255 := rfl
  simp [hc0, hz0, prog_r3e_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hl5274]

theorem prog_r3e_split : prog_r3e = prog_r3e_0 := rfl

theorem run_r3e (s : State) (c p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010) :
    runInstructions prog_r3e
      { s with pc := UInt256.ofNat 5141, stack := c :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 5149,
                  stack := (5255 : UInt256) :: (UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r3e_split]
  have g0 := run_r3e_0 s c p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact g0

def prog_exit_0 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨3, by decide⟩), .push 2 2208, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .push 2 2176, .op .MSTORE]

theorem run_exit_0 (s : State) (x0 x1 x2 x3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_exit_0
      { s with pc := UInt256.ofNat 5255, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 5266,
                  stack := x0 :: x1 :: x2 :: x3 :: rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x3.toNat 32) 2208)
          (Data.Bytes.natToBytesPadded x2.toNat 32) 2176) } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hl2208 : (2208 : UInt256).toNat = 2208 := rfl
  simp [hc0, hz0, prog_exit_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hl2176, hl2208, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact]

def prog_exit_1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 2 2144, .op .MSTORE, .op (.Dup ⟨0, by decide⟩),
   .push 2 2112, .op .MSTORE, .op (.Dup ⟨4, by decide⟩)]

theorem run_exit_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_exit_1
      { s with pc := UInt256.ofNat 5266, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 5277,
                  stack := x4 :: x0 :: x1 :: x2 :: x3 :: x4 :: rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x1.toNat 32) 2144)
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2112) } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [hc0, hz0, prog_exit_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hl2112, hl2144, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def prog_exit_2 : List Instr :=
  [.push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

theorem run_exit_2 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_exit_2
      { s with pc := UInt256.ofNat 5277, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 5286,
                  stack := rest,
                  memory := (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2080) } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hl2080 : (2080 : UInt256).toNat = 2080 := rfl
  simp [hc0, hz0, prog_exit_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hl2080, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2080 32 (by decide) (by norm_num) hact]

def prog_exit_3 : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

theorem run_exit_3 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_exit_3
      { s with pc := UInt256.ofNat 5286, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 5292,
                  stack := rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hc0, hz0, prog_exit_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6]

def prog_exit_4 : List Instr :=
  [.push 2 4367, .op .JUMP]

theorem run_exit_4 (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1022)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4367 = true) :
    runInstructions prog_exit_4
      { s with pc := UInt256.ofNat 5292, stack := rest } =
    some { s with pc := (4367 : UInt256),
                  stack := rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hl4379 : (4367 : UInt256).toNat = 4367 := rfl
  simp [hc0, hz0, prog_exit_4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hl4379, hjd]

theorem prog_exit_split : prog_exit = prog_exit_0 ++ (prog_exit_1 ++ (prog_exit_2 ++ (prog_exit_3 ++ (prog_exit_4)))) := rfl

theorem run_exit (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4367 = true) :
    runInstructions prog_exit
      { s with pc := UInt256.ofNat 5255, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4367,
                  stack := rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded p0.toNat 32) 2208)
          (Data.Bytes.natToBytesPadded p1.toNat 32) 2176)
          (Data.Bytes.natToBytesPadded p2.toNat 32) 2144)
          (Data.Bytes.natToBytesPadded p3.toNat 32) 2112)
          (Data.Bytes.natToBytesPadded p4.toNat 32) 2080) } := by
  rw [prog_exit_split]
  have g0 := run_exit_0 s p3 p2 p1 p0 (p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hact := hact)
  have g1 := run_exit_1 { s with memory := (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p0.toNat 32) 2208) (Data.Bytes.natToBytesPadded p1.toNat 32) 2176) } p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hact := hact)
  have g2 := run_exit_2 { s with memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p0.toNat 32) 2208) (Data.Bytes.natToBytesPadded p1.toNat 32) 2176) (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) (Data.Bytes.natToBytesPadded p3.toNat 32) 2112) } p4 p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hact := hact)
  have g3 := run_exit_3 { s with memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p0.toNat 32) 2208) (Data.Bytes.natToBytesPadded p1.toNat 32) 2176) (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) (Data.Bytes.natToBytesPadded p3.toNat 32) 2112) (Data.Bytes.natToBytesPadded p4.toNat 32) 2080) } k n0 n1 n2 n3 np rest
    (by omega) 
  have g4 := run_exit_4 { s with memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p0.toNat 32) 2208) (Data.Bytes.natToBytesPadded p1.toNat 32) 2176) (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) (Data.Bytes.natToBytesPadded p3.toNat 32) 2112) (Data.Bytes.natToBytesPadded p4.toNat 32) 2080) }  rest
    (by omega) (hjd := hjd)
  exact runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 (g4))))

end Challenge.Modexp.Submission.Proofs.Fast.R4Runs
