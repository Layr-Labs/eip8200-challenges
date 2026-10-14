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
  [.op .JUMPDEST, .op (.Dup ⟨11, by decide⟩), .push 0 0, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨12, by decide⟩)]

theorem run_pd0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 n3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (hn3 : MachineState.readWord s.memory 0 = n3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_pd0
      { s with pc := UInt256.ofNat 4268, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4275, stack := x8 :: x7 :: x4 :: n3 :: x11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
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
  [.push 2 2208, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩)]

theorem run_pd1 (s : State) (a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1019)
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_pd1
      { s with pc := UInt256.ofNat 4275, stack := rest } =
    some { s with pc := UInt256.ofNat 4284, stack := a0 :: a0 :: (a0 + a0) :: a0 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hl2464 : (2208 : UInt256).toNat = 2208 := rfl
  simp [prog_pd1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256, hl2464, ha0, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact, hc0, hc1, hc2, hc3, hc4]


def prog_pd2 : List Instr :=
  [.op .MUL, .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩)]

theorem run_pd2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions prog_pd2
      { s with pc := UInt256.ofNat 4284, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4291, stack := (UInt256.mulMod x3 x3 x14) :: (UInt256.mulMod x3 x3 x14) :: (x0 * x1) :: x2 :: x14 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
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
      { s with pc := UInt256.ofNat 4291, stack := x0 :: x1 :: x2 :: rest } =
    some { s with pc := UInt256.ofNat 4297, stack := ((x1 - (UInt256.gt x2 x0)) - x2) :: x2 :: rest } := by
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
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_prodiag
      { s with pc := UInt256.ofNat 4268,
               stack := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest } =
    some { s with pc := UInt256.ofNat 4297,
                  stack := dHi a0 e5 :: (a0 * a0) :: (a0 + a0) :: e5 :: e8 :: e7 :: e4 :: n3 :: e11 ::
                    e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest } := by
  have hs : prog_prodiag = prog_pd0 ++ (prog_pd1 ++ (prog_pd2 ++ prog_pd3)) := rfl
  rw [hs]
  have g0 := run_pd0 s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 n3 rest (by omega) hn3 hact
  have g1 := run_pd1 s a0
    (e8 :: e7 :: e4 :: n3 :: e11 :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega) ha0 hact
  have g2 := run_pd2 s a0 a0 (a0 + a0) a0 e8 e7 e4 n3 e11 e0 e1 e2 e3 e4 e5
    (e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega)
  have g3 := run_pd3 s (UInt256.mulMod a0 a0 e5) (UInt256.mulMod a0 a0 e5) (a0 * a0)
    ((a0 + a0) :: e5 :: e8 :: e7 :: e4 :: n3 :: e11 :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega)
  have g23 := runInstructions_append_some _ _ _ _ _ g2 g3
  have g123 := runInstructions_append_some _ _ _ _ _ g1 g23
  have g := runInstructions_append_some _ _ _ _ _ g0 g123
  simpa only [fusedBorrow_neg, dHi] using g


def prog_r0z1_0 : List Instr :=
  [.push 2 2176, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r0z1_0 (s : State) (x0 x1 x2 x3 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z1_0
      { s with pc := UInt256.ofNat 4297, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4306,
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
  have hl2432 : (2176 : UInt256).toNat = 2176 := rfl
  simp [hc0, hz0, prog_r0z1_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hl2432, ha1, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact]

def prog_r0z1_1 : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r0z1_1 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) :
    runInstructions prog_r0z1_1
      { s with pc := UInt256.ofNat 4306, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4313,
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
      { s with pc := UInt256.ofNat 4313, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4320,
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
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z1
      { s with pc := UInt256.ofNat 4297, stack := c :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4320,
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
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r0z2_0 (s : State) (x0 x1 x2 x3 x4 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1014)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z2_0
      { s with pc := UInt256.ofNat 4320, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4329,
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
  have hl2400 : (2144 : UInt256).toNat = 2144 := rfl
  simp [hc0, hz0, prog_r0z2_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hl2400, ha2, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def prog_r0z2_1 : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r0z2_1 (s : State) (x0 x1 x2 x3 x4 x5 x6 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015) :
    runInstructions prog_r0z2_1
      { s with pc := UInt256.ofNat 4329, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 4336,
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
      { s with pc := UInt256.ofNat 4336, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4343,
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
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z2
      { s with pc := UInt256.ofNat 4320, stack := c :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4343,
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
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r0z3_0 (s : State) (x0 x1 x2 x3 x4 x5 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z3_0
      { s with pc := UInt256.ofNat 4343, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4352,
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
  have hl2368 : (2112 : UInt256).toNat = 2112 := rfl
  simp [hc0, hz0, prog_r0z3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hl2368, ha3, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def prog_r0z3_1 : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r0z3_1 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1014) :
    runInstructions prog_r0z3_1
      { s with pc := UInt256.ofNat 4352, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4359,
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
      { s with pc := UInt256.ofNat 4359, stack := x0 :: x1 :: x2 :: x3 :: rest } =
    some { s with pc := UInt256.ofNat 4366,
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
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r0z3
      { s with pc := UInt256.ofNat 4343, stack := c :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4366,
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
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4376, .push 2 4616, .op .JUMP]

theorem run_r0e_0 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4616 = true) :
    runInstructions prog_r0e_0
      { s with pc := UInt256.ofNat 4366, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := (4616 : UInt256),
                  stack := (4376 : UInt256) :: (⟨0⟩ : UInt256) :: x1 :: x2 :: x3 :: x4 :: x0 :: rest } := by
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
  have hl4903 : (4376 : UInt256).toNat = 4376 := rfl
  have hl5158 : (4616 : UInt256).toNat = 4616 := rfl
  simp [hc0, hz0, prog_r0e_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hl4903, hl5158, hjd]

theorem prog_r0e_split : prog_r0e = prog_r0e_0 := rfl

theorem run_r0e (s : State) (c t3 t2 t1 t0 d k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4616 = true) :
    runInstructions prog_r0e
      { s with pc := UInt256.ofNat 4366, stack := c :: t3 :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4616,
                  stack := (4376 : UInt256) :: (⟨0⟩ : UInt256) :: t3 :: t2 :: t1 :: t0 :: c :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r0e_split]
  have g0 := run_r0e_0 s c t3 t2 t1 t0 d (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hjd := hjd)
  exact g0

/-- The raw cancellation trace is unconditional; the model bridge below carries the guard. -/
theorem run_redm_addMod (s : State) (ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions prog_redm
      { s with pc := UInt256.ofNat 4616,
               stack := ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4627,
                  stack := UInt256.addMod p0 (UInt256.mulMod n0 (np*p0) k) k ::
                    (np*p0) :: ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
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
  simp [prog_redm, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

theorem run_redm (s : State) (ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    runInstructions prog_redm
      { s with pc := UInt256.ofNat 4616,
               stack := ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4627,
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
      { s with pc := UInt256.ofNat 4627, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4633,
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
      { s with pc := UInt256.ofNat 4633, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4640,
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
      { s with pc := UInt256.ofNat 4640, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4647,
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
      { s with pc := UInt256.ofNat 4647, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4654,
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
      { s with pc := UInt256.ofNat 4627, stack := c :: m :: ret :: v :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4654,
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
      { s with pc := UInt256.ofNat 4654, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4660,
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
      { s with pc := UInt256.ofNat 4660, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4667,
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
      { s with pc := UInt256.ofNat 4667, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4674,
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
      { s with pc := UInt256.ofNat 4674, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4681,
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
      { s with pc := UInt256.ofNat 4654, stack := c :: m :: ret :: v :: p3 :: p2 :: p1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4681,
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
      { s with pc := UInt256.ofNat 4681, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4687,
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
      { s with pc := UInt256.ofNat 4687, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4694,
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
      { s with pc := UInt256.ofNat 4694, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest } =
    some { s with pc := UInt256.ofNat 4701,
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
      { s with pc := UInt256.ofNat 4701, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4708,
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
      { s with pc := UInt256.ofNat 4681, stack := c :: m :: ret :: v :: p3 :: p2 :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4708,
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

private theorem add_comm_redt (a b : UInt256) : a + b = b + a := by
  change UInt256.mk (a.val + b.val) = UInt256.mk (b.val + a.val)
  congr 1
  ac_rfl

theorem run_redt (s : State) (c m ret v p3 q2 q1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstructions prog_redt
      { s with pc := UInt256.ofNat 4708, stack := c :: m :: ret :: v :: p3 :: q2 :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := ret,
                  stack := (p4 + c) :: q2 :: q1 :: q0 :: (v + (UInt256.lt (p4 + c) p4)) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
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
  simp [prog_redt, add_comm_redt, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    UInt256.gt, UInt256.lt, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_assoc, hjd, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def prog_r1h_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2176, .op .MLOAD, .push 2 2208, .op .MLOAD, .push 0 0]

theorem run_r1h_0 (s : State) (a1 a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1h_0
      { s with pc := UInt256.ofNat 4376, stack := rest } =
    some { s with pc := UInt256.ofNat 4386,
                  stack := (⟨0⟩ : UInt256) :: a0 :: a1 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hl2432 : (2176 : UInt256).toNat = 2176 := rfl
  have hl2464 : (2208 : UInt256).toNat = 2208 := rfl
  simp [hc0, hz0, prog_r1h_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hl2432, hl2464, ha1, ha0, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact]

theorem prog_r1h_split : prog_r1h = prog_r1h_0 := rfl

theorem run_r1h (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a1 a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1h
      { s with pc := UInt256.ofNat 4376, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4386,
                  stack := (⟨0⟩ : UInt256) :: a0 :: a1 :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r1h_split]
  have g0 := run_r1h_0 s a1 a0 (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha1 := ha1) (ha0 := ha0) (hact := hact)
  exact g0

theorem run_r1d (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions prog_r1d
      { s with pc := UInt256.ofNat 4387, stack := tb :: a :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4416,
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
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r1c2_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c2_0
      { s with pc := UInt256.ofNat 4416, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4425,
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
  have hl2400 : (2144 : UInt256).toNat = 2144 := rfl
  simp [hc0, hz0, prog_r1c2_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hl2400, ha2, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def prog_r1c2_1 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r1c2_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r1c2_1
      { s with pc := UInt256.ofNat 4425, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4432,
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
      { s with pc := UInt256.ofNat 4432, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 4439,
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
      { s with pc := UInt256.ofNat 4439, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4445,
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
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c2
      { s with pc := UInt256.ofNat 4416, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4445,
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
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r1c3_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c3_0
      { s with pc := UInt256.ofNat 4445, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4454,
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
  have hl2368 : (2112 : UInt256).toNat = 2112 := rfl
  simp [hc0, hz0, prog_r1c3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hl2368, ha3, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def prog_r1c3_1 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r1c3_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r1c3_1
      { s with pc := UInt256.ofNat 4454, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4461,
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
      { s with pc := UInt256.ofNat 4461, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4468,
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
      { s with pc := UInt256.ofNat 4468, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4474,
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
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r1c3
      { s with pc := UInt256.ofNat 4445, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4474,
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
      { s with pc := UInt256.ofNat 4474, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 4481,
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
  [.push 2 4488, .push 2 4616, .op .JUMP]

theorem run_r1e_1 (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1021)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4616 = true) :
    runInstructions prog_r1e_1
      { s with pc := UInt256.ofNat 4481, stack := rest } =
    some { s with pc := (4616 : UInt256),
                  stack := (4488 : UInt256) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hl5020 : (4488 : UInt256).toNat = 4488 := rfl
  have hl5158 : (4616 : UInt256).toNat = 4616 := rfl
  simp [hc0, hz0, prog_r1e_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hl5020, hl5158, hjd]

theorem prog_r1e_split : prog_r1e = prog_r1e_0 ++ (prog_r1e_1) := rfl

theorem run_r1e (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4616 = true) :
    runInstructions prog_r1e
      { s with pc := UInt256.ofNat 4474, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4616,
                  stack := (4488 : UInt256) :: (UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r1e_split]
  have g0 := run_r1e_0 s c d p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_r1e_1 s  ((UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hjd := hjd)
  exact runInstructions_append_some _ _ _ _ _ g0 (g1)

def prog_r2h_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2144, .op .MLOAD, .push 2 2176, .op .MLOAD, .push 0 0]

theorem run_r2h_0 (s : State) (a2 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2h_0
      { s with pc := UInt256.ofNat 4488, stack := rest } =
    some { s with pc := UInt256.ofNat 4498,
                  stack := (⟨0⟩ : UInt256) :: a1 :: a2 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hl2400 : (2144 : UInt256).toNat = 2144 := rfl
  have hl2432 : (2176 : UInt256).toNat = 2176 := rfl
  simp [hc0, hz0, prog_r2h_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hl2400, hl2432, ha2, ha1, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact]

theorem prog_r2h_split : prog_r2h = prog_r2h_0 := rfl

theorem run_r2h (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2h
      { s with pc := UInt256.ofNat 4488, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4498,
                  stack := (⟨0⟩ : UInt256) :: a1 :: a2 :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r2h_split]
  have g0 := run_r2h_0 s a2 a1 (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha2 := ha2) (ha1 := ha1) (hact := hact)
  exact g0

theorem run_r2d (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions prog_r2d
      { s with pc := UInt256.ofNat 4499, stack := tb :: a :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4528,
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
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩)]

theorem run_r2c3_0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1011)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2c3_0
      { s with pc := UInt256.ofNat 4528, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest } =
    some { s with pc := UInt256.ofNat 4537,
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
  have hl2368 : (2112 : UInt256).toNat = 2112 := rfl
  simp [hc0, hz0, prog_r2c3_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hl2368, ha3, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def prog_r2c3_1 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]

theorem run_r2c3_1 (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_r2c3_1
      { s with pc := UInt256.ofNat 4537, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest } =
    some { s with pc := UInt256.ofNat 4544,
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
      { s with pc := UInt256.ofNat 4544, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4551,
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
      { s with pc := UInt256.ofNat 4551, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4557,
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
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r2c3
      { s with pc := UInt256.ofNat 4528, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4557,
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
      { s with pc := UInt256.ofNat 4557, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest } =
    some { s with pc := UInt256.ofNat 4564,
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
  [.push 2 4571, .push 2 4616, .op .JUMP]

theorem run_r2e_1 (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1021)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4616 = true) :
    runInstructions prog_r2e_1
      { s with pc := UInt256.ofNat 4564, stack := rest } =
    some { s with pc := (4616 : UInt256),
                  stack := (4571 : UInt256) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hl5108 : (4571 : UInt256).toNat = 4571 := rfl
  have hl5158 : (4616 : UInt256).toNat = 4616 := rfl
  simp [hc0, hz0, prog_r2e_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hl5108, hl5158, hjd]

theorem prog_r2e_split : prog_r2e = prog_r2e_0 ++ (prog_r2e_1) := rfl

theorem run_r2e (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4616 = true) :
    runInstructions prog_r2e
      { s with pc := UInt256.ofNat 4557, stack := c :: d :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4616,
                  stack := (4571 : UInt256) :: (UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r2e_split]
  have g0 := run_r2e_0 s c d p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  have g1 := run_r2e_1 s  ((UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hjd := hjd)
  exact runInstructions_append_some _ _ _ _ _ g0 (g1)

def prog_r3h_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MLOAD, .push 2 2144, .op .MLOAD, .push 0 0]

theorem run_r3h_0 (s : State) (a3 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r3h_0
      { s with pc := UInt256.ofNat 4571, stack := rest } =
    some { s with pc := UInt256.ofNat 4581,
                  stack := (⟨0⟩ : UInt256) :: a2 :: a3 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hl2368 : (2112 : UInt256).toNat = 2112 := rfl
  have hl2400 : (2144 : UInt256).toNat = 2144 := rfl
  simp [hc0, hz0, prog_r3h_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hl2368, hl2400, ha3, ha2, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

theorem prog_r3h_split : prog_r3h = prog_r3h_0 := rfl

theorem run_r3h (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_r3h
      { s with pc := UInt256.ofNat 4571, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4581,
                  stack := (⟨0⟩ : UInt256) :: a2 :: a3 :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r3h_split]
  have g0 := run_r3h_0 s a3 a2 (p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (ha3 := ha3) (ha2 := ha2) (hact := hact)
  exact g0

theorem run_r3d (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions prog_r3d
      { s with pc := UInt256.ofNat 4582, stack := tb :: a :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4608,
                  stack := (mCarry a a (a * tb) p3 k) :: (mSum a a (a * tb) p3) :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }  := by
  subst k
  have h := R4Diagonal.diagRun3 s tb a p3 p2 p1 p0 p4 n0 n1 n2 n3 np rest hcap
  have he := R4Diagonal.diagonal_eq a tb p3 htb
  simpa only [R4Diagonal.diagProgram3, prog_r3d, he.1, he.2, List.cons_append, List.nil_append] using h


def prog_r3e_0 : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .LT, .push 2 4719]

theorem run_r3e_0 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) :
    runInstructions prog_r3e_0
      { s with pc := UInt256.ofNat 4608, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4616,
                  stack := (4719 : UInt256) :: (UInt256.lt (x5 + x0) x5) :: x1 :: x2 :: x3 :: x4 :: (x5 + x0) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hl5274 : (4719 : UInt256).toNat = 4719 := rfl
  simp [hc0, hz0, prog_r3e_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hl5274]

theorem prog_r3e_split : prog_r3e = prog_r3e_0 := rfl

theorem run_r3e (s : State) (c p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010) :
    runInstructions prog_r3e
      { s with pc := UInt256.ofNat 4608, stack := c :: p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4616,
                  stack := (4719 : UInt256) :: (UInt256.lt (p4 + c) p4) :: p3 :: p2 :: p1 :: p0 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_r3e_split]
  have g0 := run_r3e_0 s c p3 p2 p1 p0 p4 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) 
  exact g0

/-! ## The n=4 tail (pc 5032..5124) -/

/-- Tail head with a zero overflow word: falls through to `st4`. -/
theorem run_tail_zero (s : State) (p3 p2 p1 p0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) :
    runInstructions prog_tail
      { s with pc := UInt256.ofNat 4719, stack := p3 :: p2 :: p1 :: p0 :: (⟨0⟩ : UInt256) :: rest } =
    some { s with pc := UInt256.ofNat 4725,
                  stack := p3 :: p2 :: p1 :: p0 :: (⟨0⟩ : UInt256) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hf : ¬ UInt256.isTrue (⟨0⟩ : UInt256) := by decide
  simp [prog_tail, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hf,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

/-- Tail head with a nonzero overflow word: jumps to `rare4`. -/
theorem run_tail_rare (s : State) (p3 p2 p1 p0 p4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hp4 : p4 ≠ ⟨0⟩)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4764 = true) :
    runInstructions prog_tail
      { s with pc := UInt256.ofNat 4719, stack := p3 :: p2 :: p1 :: p0 :: p4 :: rest } =
    some { s with pc := UInt256.ofNat 4764, stack := p3 :: p2 :: p1 :: p0 :: p4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have ht : UInt256.isTrue p4 := by
    show p4.toNat ≠ 0
    intro h; exact hp4 (Challenge.EvmProof.Word.word_ext (by rw [h]; rfl))
  have hl : (4764 : UInt256).toNat = 4764 := rfl
  simp [prog_tail, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, ht, hl,
    hjd, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

def prog_rare4_0 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT]

/-- `rare4`, limb 0: `d0 = p0 - n0` replaces `p0`, borrow `p0 < n0` on top. -/
theorem run_rare4_0 (s : State) (p3 p2 p1 p0 p4 k n0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009) :
    runInstructions prog_rare4_0
      { s with pc := UInt256.ofNat 4764, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: rest } =
    some { s with pc := UInt256.ofNat 4773,
                  stack := UInt256.lt p0 n0 :: p3 :: p2 :: p1 :: (p0 - n0) :: p4 :: k :: n0 :: rest } := by
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
  simp [prog_rare4_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12]

def prog_rare4_1 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB,
   .op (.Swap ⟨6, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR]

/-- `rare4`, limb 1: `e1 = n1 + b0`, `d1 = p1 - e1`, borrow `(b0 > e1) | (p1 < e1)`. -/
theorem run_rare4_1 (s : State) (b0 p3 p2 p1 d0 p4 k n0 n1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009) :
    runInstructions prog_rare4_1
      { s with pc := UInt256.ofNat 4773,
               stack := b0 :: p3 :: p2 :: p1 :: d0 :: p4 :: k :: n0 :: n1 :: rest } =
    some { s with pc := UInt256.ofNat 4787,
                  stack := UInt256.lor (UInt256.gt b0 (n1 + b0)) (UInt256.lt p1 (n1 + b0)) ::
                    p3 :: p2 :: (p1 - (n1 + b0)) :: d0 :: p4 :: k :: n0 :: n1 :: rest } := by
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
  simp [prog_rare4_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14]

def prog_rare4_2 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB,
   .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR]

/-- `rare4`, limb 2: `e2 = n2 + b1`, `d2 = p2 - e2`, borrow `(b1 > e2) | (p2 < e2)`. -/
theorem run_rare4_2 (s : State) (b1 p3 p2 d1 d0 p4 k n0 n1 n2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions prog_rare4_2
      { s with pc := UInt256.ofNat 4787,
               stack := b1 :: p3 :: p2 :: d1 :: d0 :: p4 :: k :: n0 :: n1 :: n2 :: rest } =
    some { s with pc := UInt256.ofNat 4801,
                  stack := UInt256.lor (UInt256.gt b1 (n2 + b1)) (UInt256.lt p2 (n2 + b1)) ::
                    p3 :: (p2 - (n2 + b1)) :: d1 :: d0 :: p4 :: k :: n0 :: n1 :: n2 :: rest } := by
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
  simp [prog_rare4_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

def prog_rare4_3 : List Instr :=
  [.op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB, .push 0 0,
   .op (.Swap ⟨4, by decide⟩), .op .POP, .push 2 4725, .op .JUMP]

/-- `rare4`, limb 3: `d3 = p3 - (n3 + b2)`; the overflow word becomes zero; back to `st4`. -/
theorem run_rare4_3 (s : State) (b2 p3 d2 d1 d0 p4 k n0 n1 n2 n3 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4725 = true) :
    runInstructions prog_rare4_3
      { s with pc := UInt256.ofNat 4801,
               stack := b2 :: p3 :: d2 :: d1 :: d0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: rest } =
    some { s with pc := UInt256.ofNat 4725,
                  stack := (p3 - (n3 + b2)) :: d2 :: d1 :: d0 :: (⟨0⟩ : UInt256) ::
                    k :: n0 :: n1 :: n2 :: n3 :: rest } := by
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
  have hl : (4725 : UInt256).toNat = 4725 := rfl
  simp [prog_rare4_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hl,
    hjd, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

theorem prog_rare4_split :
    prog_rare4 = prog_rare4_0 ++ (prog_rare4_1 ++ (prog_rare4_2 ++ prog_rare4_3)) := rfl

/-- `rare4`: the borrow-chain subtraction of `n0..n3`, overflow word zeroed, back to `st4`. -/
theorem run_rare4 (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4725 = true) :
    runInstructions prog_rare4
      { s with pc := UInt256.ofNat 4764,
               stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4725,
                  stack := (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t3 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t2 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t1 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t0 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t4 ::
                    k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_rare4_split]
  have g0 := run_rare4_0 s p3 p2 p1 p0 p4 k n0 (n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega)
  have g1 := run_rare4_1 s (UInt256.lt p0 n0) p3 p2 p1 (p0 - n0) p4 k n0 n1 (n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega)
  have g2 := run_rare4_2 s (UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
      (UInt256.lt p1 (n1 + UInt256.lt p0 n0))) p3 p2 (p1 - (n1 + UInt256.lt p0 n0)) (p0 - n0)
    p4 k n0 n1 n2 (n3 :: np :: rest) (by simp only [List.length_cons]; omega)
  have g3 := run_rare4_3 s
    (UInt256.lor (UInt256.gt (UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
        (UInt256.lt p1 (n1 + UInt256.lt p0 n0)))
      (n2 + UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
        (UInt256.lt p1 (n1 + UInt256.lt p0 n0))))
      (UInt256.lt p2 (n2 + UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
        (UInt256.lt p1 (n1 + UInt256.lt p0 n0)))))
    p3
    (p2 - (n2 + UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
      (UInt256.lt p1 (n1 + UInt256.lt p0 n0))))
    (p1 - (n1 + UInt256.lt p0 n0)) (p0 - n0) p4 k n0 n1 n2 n3 (np :: rest)
    (by simp only [List.length_cons]; omega) hjd
  exact runInstructions_append_some _ _ _ _ _ g0
    (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3))

def prog_st4_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE]

theorem run_st4_0 (s : State) (x0 x1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1019)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_st4_0
      { s with pc := UInt256.ofNat 4725, stack := x0 :: x1 :: rest } =
    some { s with pc := UInt256.ofNat 4734,
                  stack := rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2112)
          (Data.Bytes.natToBytesPadded x1.toNat 32) 2144) } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [hc0, hz0, prog_st4_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hl2112, hl2144, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def prog_st4_1 : List Instr :=
  [.push 2 2176, .op .MSTORE,
   .push 2 2208, .op .MSTORE]

theorem run_st4_1 (s : State) (x0 x1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_st4_1
      { s with pc := UInt256.ofNat 4734, stack := x0 :: x1 :: rest } =
    some { s with pc := UInt256.ofNat 4742,
                  stack := rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2176)
          (Data.Bytes.natToBytesPadded x1.toNat 32) 2208) } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hl2208 : (2208 : UInt256).toNat = 2208 := rfl
  simp [hc0, hz0, prog_st4_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hl2176, hl2208, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact]

def prog_st4_2 : List Instr :=
  [.push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

theorem run_st4_2 (s : State) (x0 x1 x2 x3 x4 x5 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_st4_2
      { s with pc := UInt256.ofNat 4742, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest } =
    some { s with pc := UInt256.ofNat 4751,
                  stack := rest,
                  memory := (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2080) } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hl2080 : (2080 : UInt256).toNat = 2080 := rfl
  simp [hc0, hz0, prog_st4_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hl2080, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2080 32 (by decide) (by norm_num) hact]

def prog_st4_3 : List Instr :=
  [.op .POP]

theorem run_st4_3 (s : State) (x0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions prog_st4_3
      { s with pc := UInt256.ofNat 4751, stack := x0 :: rest } =
    some { s with pc := UInt256.ofNat 4752,
                  stack := rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  simp [hc0, prog_st4_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc1]

def prog_st4_4 : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .op (.Swap ⟨14, by decide⟩), .push 2 4268, .op .JUMPI]

/-- The square counter in the frame's `pdst` slot (`c`, under fourteen words): decremented by
the all-ones word `x5`; a nonzero old count jumps back into R4. -/
theorem run_st4_4_more (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) (hc : UInt256.isTrue c)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4268 = true) :
    runInstructions prog_st4_4
      { s with pc := UInt256.ofNat 4752,
               stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
                 x12 :: x13 :: c :: rest } =
    some { s with pc := UInt256.ofNat 4268,
                  stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
                    x12 :: x13 :: (x5 + c) :: rest } := by
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
  have hl : (4268 : UInt256).toNat = 4268 := rfl
  simp [prog_st4_4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hc, hl,
    hjd, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
    hc17, hc18]

/-- The same block with a zero count: falls through to the `m4` jump. -/
theorem run_st4_4_last (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) (hc : ¬ UInt256.isTrue c) :
    runInstructions prog_st4_4
      { s with pc := UInt256.ofNat 4752,
               stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
                 x12 :: x13 :: c :: rest } =
    some { s with pc := UInt256.ofNat 4760,
                  stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
                    x12 :: x13 :: (x5 + c) :: rest } := by
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
  simp [prog_st4_4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hc,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
    hc17, hc18]

/-- `m4`: the last square leaves for `m4j` (4248). -/
theorem run_m4 (s : State) (rest : List UInt256) (hcap : rest.length ≤ 1022)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 3999 = true) :
    runInstructions prog_m4 { s with pc := UInt256.ofNat 4760, stack := rest } =
    some { s with pc := (3999 : UInt256), stack := rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hl : (3999 : UInt256).toNat = 3999 := rfl
  simp [prog_m4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hl, hjd,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc0, hc1]

/-- Two writes to disjoint windows commute (same statement and proof as
`R8ZeroFirstRowEnds.writeBytes_comm_disjoint`, restated here to avoid an import edge). -/
private theorem wb_comm (bs b1 b2 : ByteArray) (a1 a2 : Nat)
    (h1 : b1.size ≠ 0) (h2 : b2.size ≠ 0) (hd : a1 + b1.size ≤ a2 ∨ a2 + b2.size ≤ a1) :
    MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2 =
      MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1 := by
  have hsize : (MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2).size =
      (MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1).size := by
    rw [MachineState.writeBytes_size, MachineState.writeBytes_size, MachineState.writeBytes_size,
      MachineState.writeBytes_size, if_neg h1, if_neg h2, if_neg h2, if_neg h1]
    omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [MachineState.writeBytes_getElem?_getD]
  split_ifs <;> first | rfl | omega

/-- `st4` stores `0x840, 0x860, 0x880, 0x8a0` in stack order; the four windows are disjoint and
word-aligned, so the nesting is the `r4Mem` order. -/
private theorem st4_mem_reorder (m a b c d : ByteArray)
    (ha : a.size = 32) (hb : b.size = 32) (hc : c.size = 32) (hd : d.size = 32) :
    MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes m a 2112) b 2144) c 2176) d 2208 =
    MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes m d 2208) c 2176) b 2144) a 2112 := by
  have ha0 : a.size ≠ 0 := by omega
  have hb0 : b.size ≠ 0 := by omega
  have hc0 : c.size ≠ 0 := by omega
  have hd0 : d.size ≠ 0 := by omega
  rw [wb_comm (MachineState.writeBytes (MachineState.writeBytes m a 2112) b 2144) c d 2176 2208
        hc0 hd0 (by omega),
    wb_comm (MachineState.writeBytes m a 2112) b d 2144 2208 hb0 hd0 (by omega),
    wb_comm m a d 2112 2208 ha0 hd0 (by omega),
    wb_comm (MachineState.writeBytes (MachineState.writeBytes m d 2208) a 2112) b c 2144 2176
        hb0 hc0 (by omega),
    wb_comm (MachineState.writeBytes m d 2208) a c 2112 2176 ha0 hc0 (by omega),
    wb_comm (MachineState.writeBytes (MachineState.writeBytes m d 2208) c 2176) a b 2112 2144
        ha0 hb0 (by omega)]

/-- The stores of `st4` (pc 5038 → 5065): the window `p3 p2 p1 p0 p4` and the six constants
leave the stack; memory gets the `r4Mem` writes. -/
theorem run_st4_stores (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (prog_st4_0 ++ (prog_st4_1 ++ (prog_st4_2 ++ prog_st4_3)))
      { s with pc := UInt256.ofNat 4725,
               stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4752,
                  stack := rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded p0.toNat 32) 2208)
          (Data.Bytes.natToBytesPadded p1.toNat 32) 2176)
          (Data.Bytes.natToBytesPadded p2.toNat 32) 2144)
          (Data.Bytes.natToBytesPadded p3.toNat 32) 2112)
          (Data.Bytes.natToBytesPadded p4.toNat 32) 2080) } := by
  have hs : ∀ n : Nat, (Data.Bytes.natToBytesPadded n 32).size = 32 :=
    fun n => YulEvmCompiler.BytesLemmas.natToBytesPadded_size n 32
  have g0 := run_st4_0 s p3 p2 (p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hact := hact)
  have g1 := run_st4_1 { s with memory := (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p3.toNat 32) 2112) (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) } p1 p0 (p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega) (hact := hact)
  have g2 := run_st4_2 { s with memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p3.toNat 32) 2112) (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) (Data.Bytes.natToBytesPadded p1.toNat 32) 2176) (Data.Bytes.natToBytesPadded p0.toNat 32) 2208) } p4 k n0 n1 n2 n3 (np :: rest)
    (by simp only [List.length_cons]; omega) (hact := hact)
  have g3 := run_st4_3 { s with memory := (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p3.toNat 32) 2112) (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) (Data.Bytes.natToBytesPadded p1.toNat 32) 2176) (Data.Bytes.natToBytesPadded p0.toNat 32) 2208) (Data.Bytes.natToBytesPadded p4.toNat 32) 2080) } np rest (by omega)
  have h := runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3))
  rw [st4_mem_reorder s.memory (Data.Bytes.natToBytesPadded p3.toNat 32) (Data.Bytes.natToBytesPadded p2.toNat 32) (Data.Bytes.natToBytesPadded p1.toNat 32) (Data.Bytes.natToBytesPadded p0.toNat 32)
    (hs _) (hs _) (hs _) (hs _)] at h
  exact h

theorem prog_st4_split :
    prog_st4 = (prog_st4_0 ++ (prog_st4_1 ++ (prog_st4_2 ++ prog_st4_3))) ++ prog_st4_4 := rfl

end Challenge.Modexp.Submission.Proofs.Fast.R4Runs
