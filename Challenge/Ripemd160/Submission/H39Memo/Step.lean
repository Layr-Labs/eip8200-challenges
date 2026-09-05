import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Generic single-instruction facts for artifact-parametric jump paths. -/

namespace Challenge.Ripemd160.Submission.H39Memo.Step

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

theorem runLocated_jump {artifact : ProgramArtifact} {fork : Fork}
    (loc : Stepper.Located artifact fork)
    (hins : loc.instruction = .op .JUMP)
    (s : State) (code : ByteArray) (dest : Nat) (rest : List UInt256)
    (hpc : s.pc.toNat = artifact.instructionPC loc.index)
    (hstack : s.stack = UInt256.ofNat dest :: rest)
    (hlen : rest.length < 1023)
    (hcode : s.executionEnv.code = code)
    (hdest : dest < 2 ^ 256)
    (hjump : Decode.isValidJumpDest code dest = true) :
    Stepper.runLocated loc s =
      some { s with stack := rest, pc := UInt256.ofNat dest } := by
  unfold Stepper.runLocated
  rw [if_pos hpc, hins]
  unfold Stepper.runInstr
  have hcap : s.stack.length < 1024 := by
    rw [hstack]
    simp
    omega
  rw [if_pos hcap]
  simp only [hstack]
  rw [hcode, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hdest, hjump]
  simp

theorem runLocated_jumpi_taken {artifact : ProgramArtifact} {fork : Fork}
    (loc : Stepper.Located artifact fork)
    (hins : loc.instruction = .op .JUMPI)
    (s : State) (code : ByteArray) (dest : Nat) (cond : UInt256)
    (rest : List UInt256)
    (hpc : s.pc.toNat = artifact.instructionPC loc.index)
    (hstack : s.stack = UInt256.ofNat dest :: cond :: rest)
    (hlen : rest.length < 1022)
    (hcond : UInt256.isTrue cond)
    (hcode : s.executionEnv.code = code)
    (hdest : dest < 2 ^ 256)
    (hjump : Decode.isValidJumpDest code dest = true) :
    Stepper.runLocated loc s =
      some { s with stack := rest, pc := UInt256.ofNat dest } := by
  unfold Stepper.runLocated
  rw [if_pos hpc, hins]
  unfold Stepper.runInstr
  have hcap : s.stack.length < 1024 := by
    rw [hstack]
    simp
    omega
  rw [if_pos hcap]
  simp only [hstack]
  rw [if_pos hcond, hcode, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hdest, hjump]
  simp

theorem runLocated_jumpi_not_taken {artifact : ProgramArtifact} {fork : Fork}
    (loc : Stepper.Located artifact fork)
    (hins : loc.instruction = .op .JUMPI)
    (s : State) (dest : Nat) (cond : UInt256)
    (rest : List UInt256)
    (hpc : s.pc.toNat = artifact.instructionPC loc.index)
    (hstack : s.stack = UInt256.ofNat dest :: cond :: rest)
    (hlen : rest.length < 1022)
    (hcond : ¬ UInt256.isTrue cond) :
    Stepper.runLocated loc s =
      some { s with stack := rest, pc := s.pc.succ } := by
  unfold Stepper.runLocated
  rw [if_pos hpc, hins]
  unfold Stepper.runInstr
  have hcap : s.stack.length < 1024 := by
    rw [hstack]
    simp
    omega
  rw [if_pos hcap]
  simp only [hstack]
  rw [if_neg hcond]

theorem runLocatedBlock_two {artifact : ProgramArtifact} {fork : Fork}
    (l1 l2 : Stepper.Located artifact fork) (s t u : State)
    (h1 : Stepper.runLocated l1 s = some t)
    (ht : t.halt = .Running)
    (h2 : Stepper.runLocated l2 t = some u) :
    Stepper.runLocatedBlock [l1, l2] s = some u := by
  simp [Stepper.runLocatedBlock, h1, ht, h2]

end Challenge.Ripemd160.Submission.H39Memo.Step
