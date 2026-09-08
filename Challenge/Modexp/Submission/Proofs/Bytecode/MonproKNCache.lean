import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

/-!
Artifact-independent creation and removal of the two private MONPRO constants.
The public entry and returned frames remain unchanged.  Concrete code locations
and the whole subroutine proof are separate obligations.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def negative32 : UInt256 := UInt256.lnot (UInt256.ofNat 31)
def allOnes : UInt256 := UInt256.lnot (UInt256.ofNat 0)

theorem negative32_value : negative32 = UInt256.ofNat (2 ^ 256 - 32) := by decide
theorem allOnes_value : allOnes = UInt256.ofNat (2 ^ 256 - 1) := by decide

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

def createProgram : List Instr :=
  [.push 1 31, .op .NOT, .op (.Swap ⟨1, by decide⟩),
   .push 0 0, .op .NOT, .op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩)]

def removeProgram : List Instr := [.op .POP, .op .POP]

theorem run_create (template : State) (pc pa pb destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1007) :
    runInstructions createProgram
      (framed template pc ([pa, pb, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 6 (pc + UInt256.ofNat 2))
      ([pa, pb, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, createProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    negative32, allOnes, advancePC, hc4, hc5, hc6, List.exchange]
  decide

theorem run_remove (template : State) (pc destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1007) :
    runInstructions removeProgram
      (framed template pc ([negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template pc.succ.succ ([destination, returnPC] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [runInstructions, removeProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc4, hc3]

/-- The internal peak has room under Stepper's strict pre-instruction bound. -/
theorem internal_capacity (rest : List UInt256) (hrest : rest.length ≤ 1007) :
    rest.length + 16 < 1024 := by omega

/-- Existing Exp callers need no stronger public tail assumption. -/
theorem exp_capacity (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    rest.length ≤ 1007 := by omega

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache
