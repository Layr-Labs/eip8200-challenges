import Challenge.Modexp.Submission.Proofs.R5.Blocks
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# The r5 tail (execution): product, normalization rounds, pack and RETURN

From the loop exit (4716) the product runs in four segments joined by three hops and reaches
`r5_norm` (5184). A normalization round either leaves for `r5_done` (5285) with the digits
unchanged (`a4 < n4`, or the trial subtraction borrows out) or replaces them by the trial
difference and repeats. `r5_done` packs the digits into 0x00..0x80 and returns 128 bytes.
-/

namespace CycleSubmission.R5.TailRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel WindowTwentyOneBinding
open CycleSubmission.R5.ProductRun CycleSubmission.R5.ExecNorm CycleSubmission.R5.Blocks

/-- A block's steps from its run lemma (start state taken from the run lemma). -/
noncomputable def runSteps {pc : Nat} {prog : List Instr}
    (blk : Block CycleSubmission.Artifact.artifact .Osaka pc prog) {s0 t : State} (s : State)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (h : runInstructions prog s0 = some t)
    (henv : s0.executionEnv = s.executionEnv) (hhalt : s0.halt = s.halt) (hpc : s0.pc = UInt256.ofNat pc) :
    GasSteps s0 t :=
  blk.steps (env.transfer henv hhalt) hpc h

section
variable (s : State) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
  (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (rest : List UInt256)
  (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
  (h_b0 : MachineState.readWord s.memory 0 = b0) (h_b1 : MachineState.readWord s.memory 32 = b1)
  (h_b2 : MachineState.readWord s.memory 64 = b2) (h_b3 : MachineState.readWord s.memory 96 = b3)
  (h_b4 : MachineState.readWord s.memory 128 = b4) (h_n0 : MachineState.readWord s.memory 160 = n0)
  (h_inv : MachineState.readWord s.memory 192 = inv) (h_M : MachineState.readWord s.memory 224 = M)

/-- The product: loop exit (4716) to `r5_norm` (5184). -/
noncomputable def product :
    GasSteps {s with pc := UInt256.ofNat 4716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}
      {s with pc := UInt256.ofNat 5184, stack := prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M :: prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M :: prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M :: prV8_8 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M :: prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
  let a := prSeg0_run s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M rest hcap hact
    h_b0 h_b1 h_b2 h_b3 h_b4 h_n0 h_inv h_M
  let b := prSeg1_run s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M rest hcap hact
    h_b0 h_b1 h_b2 h_b3 h_b4 h_n0 h_inv h_M
  let c := prSeg2_run s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M rest hcap hact
    h_b0 h_b1 h_b2 h_b3 h_b4 h_n0 h_inv h_M
  let d := prSeg3_run s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M rest hcap hact
    h_b0 h_b1 h_b2 h_b3 h_b4 h_n0 h_inv h_M
  ((((((runSteps productSeg0Block s env a rfl rfl rfl).trans
    (ctl4800_steps s _ env (by simp only [List.length_cons]; omega))).trans
    (runSteps productSeg1Block s env b rfl rfl rfl)).trans
    (ctl3433_steps s _ env (by simp only [List.length_cons]; omega))).trans
    (runSteps productSeg2Block s env c rfl rfl rfl)).trans
    (ctl3901_steps s _ env (by simp only [List.length_cons]; omega))).trans
    (runSteps productSeg3Block s env d rfl rfl rfl)
end

section
variable (s : State) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
  (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) (rest : List UInt256)
  (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
  (h_n0 : MachineState.readWord s.memory 160 = n0) (h_M : MachineState.readWord s.memory 224 = M)

def normAt (pc : Nat) (a0 a1 a2 a3 a4 : UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

/-- `a4 < n4`: straight to `r5_done`. -/
noncomputable def roundLt (hlt : (UInt256.lt a4 n4).toNat ≠ 0) :
    GasSteps (normAt s n1 n2 n3 n4 P inv cntp rest 5184 a0 a1 a2 a3 a4)
      (normAt s n1 n2 n3 n4 P inv cntp rest 5285 a0 a1 a2 a3 a4) :=
  ((runSteps normBlock s env ((norm_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
        (congrArg some (norm_eq s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest))) rfl rfl rfl).trans
    (ctl5188_steps s _ _ env (by simp only [List.length_cons]; omega))).cast rfl
    (by simp only [norm_o0, if_neg hlt]; rfl)

/-- `a4 ≥ n4`: the trial subtraction, then either back to the digits (borrow out) or the
difference and another round. -/
noncomputable def roundSub (hlt : (UInt256.lt a4 n4).toNat = 0) :
    GasSteps (normAt s n1 n2 n3 n4 P inv cntp rest 5184 a0 a1 a2 a3 a4)
      {s with pc := (if (blk5192_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M).toNat = 0 then UInt256.ofNat 5265 else UInt256.ofNat 5279), stack := blk5192_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M :: blk5192_o2 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M :: blk5192_o3 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M :: blk5192_o4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M :: blk5192_o5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
  ((((runSteps normBlock s env ((norm_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
        (congrArg some (norm_eq s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest))) rfl rfl rfl).trans
    (ctl5188_steps s _ _ env (by simp only [List.length_cons]; omega))).cast rfl
    (by simp only [norm_o0] at hlt ⊢; simp only [hlt, if_pos])).trans
    (runSteps blk5192Block s env ((blk5192_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
        (congrArg some (blk5192_eq s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M rest h_n0 h_M))) rfl rfl rfl)).trans
    (ctl5261_steps s _ _ env (by simp only [List.length_cons]; omega))

/-- Borrow out: drop the trial digits and go to `r5_done` with `a`. -/
noncomputable def keep (d4 d3 d2 d1 d0 : UInt256) :
    GasSteps {s with pc := UInt256.ofNat 5279, stack := d4 :: d3 :: d2 :: d1 :: d0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}
      (normAt s n1 n2 n3 n4 P inv cntp rest 5285 a0 a1 a2 a3 a4) :=
  runSteps negBlock s env ((neg_run s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (neg_eq s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest))) rfl rfl rfl

/-- No borrow: the difference digits replace `a` and the round repeats. -/
noncomputable def replace (d4 d3 d2 d1 d0 : UInt256) :
    GasSteps {s with pc := UInt256.ofNat 5265, stack := d4 :: d3 :: d2 :: d1 :: d0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}
      (normAt s n1 n2 n3 n4 P inv cntp rest 5184 d0 d1 d2 d3 d4) :=
  (runSteps blk5265Block s env ((blk5265_run s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (blk5265_eq s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest))) rfl rfl rfl).trans
  (ctl5275_steps s _ env (by simp only [List.length_cons]; omega))

/-- `r5_done`: pack and return. -/
noncomputable def finish :
    GasSteps (normAt s n1 n2 n3 n4 P inv cntp rest 5285 a0 a1 a2 a3 a4)
      (ctl5330_result {s with memory := done_mem s.memory a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp}
        (a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest)) :=
  (runSteps doneBlock s env ((done_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (done_eq s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest))) rfl rfl rfl).trans
  (ctl5330_steps {s with memory := done_mem s.memory a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp} _
    (env.transfer rfl rfl) (by simp only [List.length_cons]; omega) (by exact hact))
end

end CycleSubmission.R5.TailRun
