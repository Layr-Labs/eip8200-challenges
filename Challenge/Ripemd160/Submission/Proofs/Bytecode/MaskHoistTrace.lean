import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskHelperTemplates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHoistBaseline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskProjection
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHoistTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open MaskProjection StackRoundTrace

/-! Each relation compares the shorter actual helper with its preserved baseline.
Only the final PC changes; memory, complete stack, halt, and every other field
remain those of the old execution. Both removed SWAPs precede the earlier JUMP;
the equal-width STOP padding is unreachable and not part of either template. -/

theorem left_equivalent (group : Fin 5) (constant : UInt256)
    (s : State) (startPC p0 p1 p2 p3 returnPC c0 c1 c2 c3 : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (MaskHelperTemplates.leftTemplate group constant)
      (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC c0 c1 c2 c3 working rho) =
    Option.map (fun out => {out with pc := pcAfter startPC (MaskHelperTemplates.leftTemplate group constant)})
      (runInstrSeq (MaskHoistBaseline.leftTemplate group constant)
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC c0 c1 c2 c3 working rho)) := by
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  fin_cases group <;>
    simp (config := { maxSteps := 5000000 })
      [MaskHelperTemplates.leftTemplate, MaskHoistBaseline.leftTemplate,
       MaskHelperTemplates.leftTemplate0, MaskHelperTemplates.leftTemplate1, MaskHelperTemplates.leftTemplate2, MaskHelperTemplates.leftTemplate3, MaskHelperTemplates.leftTemplate4,
       MaskHoistBaseline.leftTemplate0, MaskHoistBaseline.leftTemplate1, MaskHoistBaseline.leftTemplate2, MaskHoistBaseline.leftTemplate3, MaskHoistBaseline.leftTemplate4,
       MaskHelperTemplates.op, MaskHoistBaseline.op, Decode.opcodeOf,
       maskQuadHelperEntry, roundWords, runInstrSeq, Stepper.runInstr,
       pcAfter, List.exchange, hrun, hcap, UInt256.succ,
       Instr.size, Instr.size_op, Instr.size_push, State.activeWordsAfterUInt256,
       hadd, Word.word_add_comm, hpc, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, Nat.add_assoc]

theorem right_equivalent (group : Fin 5) (constant : UInt256)
    (s : State) (startPC p0 p1 p2 p3 returnPC c0 c1 c2 c3 : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (MaskHelperTemplates.rightTemplate group constant)
      (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC c0 c1 c2 c3 working rho) =
    Option.map (fun out => {out with pc := pcAfter startPC (MaskHelperTemplates.rightTemplate group constant)})
      (runInstrSeq (MaskHoistBaseline.rightTemplate group constant)
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC c0 c1 c2 c3 working rho)) := by
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  fin_cases group <;>
    simp (config := { maxSteps := 5000000 })
      [MaskHelperTemplates.rightTemplate, MaskHoistBaseline.rightTemplate,
       MaskHelperTemplates.rightTemplate0, MaskHelperTemplates.rightTemplate1, MaskHelperTemplates.rightTemplate2, MaskHelperTemplates.rightTemplate3, MaskHelperTemplates.rightTemplate4,
       MaskHoistBaseline.rightTemplate0, MaskHoistBaseline.rightTemplate1, MaskHoistBaseline.rightTemplate2, MaskHoistBaseline.rightTemplate3, MaskHoistBaseline.rightTemplate4,
       MaskHelperTemplates.op, MaskHoistBaseline.op, Decode.opcodeOf,
       maskQuadHelperEntry, roundWords, runInstrSeq, Stepper.runInstr,
       pcAfter, List.exchange, hrun, hcap, UInt256.succ,
       Instr.size, Instr.size_op, Instr.size_push, State.activeWordsAfterUInt256,
       hadd, Word.word_add_comm, hpc, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, Nat.add_assoc]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHoistTrace
