import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundCertificate

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySwap
open EvmSemantics PackedStepFrame PackedEmit PackedStep0

/-- Isolated experimental boundary execution gate, not yet validated. -/
theorem swap_exec (memAt : UInt256 → UInt256) (k : UInt256)
    (f : Frame) (rest : List UInt256) :
    runOps memAt [Op.push k, Op.swap 16, Op.pop] (frameStack f ++ rest)
      = some (frameStack (replaceK k f) ++ rest) := by
  obtain ⟨regs, sf, phase⟩ := f
  cases phase <;>
    simp only [frameStack, regsStack, suffixStack, replaceK, runOps, runOp,
      List.cons_append, List.nil_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, List.set_cons_succ, List.set_cons_zero,
      Option.map_some, Option.bind_some, Nat.reduceSub]

theorem kSwap_exec (memAt : UInt256 → UInt256) (group : Nat)
    (f : Frame) (rest : List UInt256) :
    runOps memAt (kSwap group) (frameStack f ++ rest)
      = some (frameStack (replaceK (packedK group) f) ++ rest) :=
  swap_exec memAt (packedK group) f rest

#print axioms swap_exec
#print axioms kSwap_exec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySwap
