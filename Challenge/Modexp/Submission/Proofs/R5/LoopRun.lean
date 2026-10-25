import Challenge.Modexp.Submission.Proofs.R5.Blocks
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# The r5 square loop (execution)

At `r5_head` (4037) the stack is `[x0..x4, n1..n4, P, inv', c, rest]`. One round runs the
square block (4037 → 4712) and the loop test (`PUSH2 4037; JUMPI` on the old counter): a zero
counter leaves to the product at 4716, otherwise the round repeats with `c - 1`. Starting with
`c.toNat = m` the loop runs `m + 1` squares (`iter`).
-/

namespace CycleSubmission.R5.LoopRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open CycleSubmission.R5.SquareRun CycleSubmission.R5.Blocks

structure D5 where
  d0 : UInt256
  d1 : UInt256
  d2 : UInt256
  d3 : UInt256
  d4 : UInt256

section
variable (n1 n2 n3 n4 P inv n0 : UInt256)

def next (x : D5) (c : UInt256) : D5 :=
  ⟨sqV5_5 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0,
   sqV6_6 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0,
   sqV7_7 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0,
   sqV8_8 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0,
   sqV8_0 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0⟩

def dec (x : D5) (c : UInt256) : UInt256 :=
  sqV9_12 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0

def iter : Nat → D5 → UInt256 → D5 × UInt256
  | 0, x, c => (x, c)
  | m + 1, x, c => iter m (next n1 n2 n3 n4 P inv n0 x c) (dec n1 n2 n3 n4 P inv n0 x c)

theorem dec_eq (x : D5) (c : UInt256) : dec n1 n2 n3 n4 P inv n0 x c = c - UInt256.ofNat 1 := rfl

theorem dec_toNat (x : D5) (c : UInt256) (hc : c.toNat ≠ 0) :
    (dec n1 n2 n3 n4 P inv n0 x c).toNat = c.toNat - 1 := by
  rw [dec_eq, Challenge.EvmProof.Word.word_toNat_sub_cond, if_neg (by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num; omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num
end

def head (s : State) (x : D5) (n1 n2 n3 n4 P inv c : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4037, stack := x.d0 :: x.d1 :: x.d2 :: x.d3 :: x.d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: c :: rest}

def leave (s : State) (x : D5) (n1 n2 n3 n4 P inv c : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4716, stack := x.d0 :: x.d1 :: x.d2 :: x.d3 :: x.d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: c :: rest}

section
variable (s : State) (n1 n2 n3 n4 P inv n0 : UInt256) (rest : List UInt256)
  (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
  (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
  (h_n0 : MachineState.readWord s.memory 160 = n0) (h_inv : MachineState.readWord s.memory 192 = inv)

/-- One round: square, then the loop test on the old counter `c`. -/
noncomputable def round (x : D5) (c : UInt256) :
    GasSteps (head s x n1 n2 n3 n4 P inv c rest)
      {s with pc := (if c.toNat = 0 then UInt256.ofNat 4716 else UInt256.ofNat 4037), stack := (next n1 n2 n3 n4 P inv n0 x c).d0 :: (next n1 n2 n3 n4 P inv n0 x c).d1 :: (next n1 n2 n3 n4 P inv n0 x c).d2 :: (next n1 n2 n3 n4 P inv n0 x c).d3 :: (next n1 n2 n3 n4 P inv n0 x c).d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: dec n1 n2 n3 n4 P inv n0 x c :: rest} :=
  (squareBlock.steps (s := head s x n1 n2 n3 n4 P inv c rest) (env.transfer rfl rfl) rfl
    (sq_run s x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0 rest hcap hact h_n0 h_inv)).trans
  (ctl4712_steps s c _ env (by simp only [List.length_cons]; omega))

/-- `m + 1` rounds from a counter with value `m`. -/
noncomputable def loop : ∀ (m : Nat) (x : D5) (c : UInt256), c.toNat = m →
    GasSteps (head s x n1 n2 n3 n4 P inv c rest)
      (leave s (iter n1 n2 n3 n4 P inv n0 (m + 1) x c).1 n1 n2 n3 n4 P inv
        (iter n1 n2 n3 n4 P inv n0 (m + 1) x c).2 rest)
  | 0, x, c, hc =>
    (round s n1 n2 n3 n4 P inv n0 rest env hcap hact h_n0 h_inv x c).cast rfl
      (by simp only [hc, if_pos]; rfl)
  | m + 1, x, c, hc =>
    ((round s n1 n2 n3 n4 P inv n0 rest env hcap hact h_n0 h_inv x c).cast rfl
      (by rw [if_neg (by omega)]; rfl)).trans
    (loop m (next n1 n2 n3 n4 P inv n0 x c) (dec n1 n2 n3 n4 P inv n0 x c)
      (by rw [dec_toNat _ _ _ _ _ _ _ _ _ (by omega)]; omega))
end

end CycleSubmission.R5.LoopRun
