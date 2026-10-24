import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace HistoricalSearch.CRTControl
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def jumpiProgram : List Instr := [.op .JUMPI]
def jumpProgram : List Instr := [.op .JUMP]
def jumpDestProgram : List Instr := [.op .JUMPDEST]
def resumeProgram : List Instr := jumpProgram ++ jumpDestProgram

def conditionalModel (s : State) : State :=
  {s with pc := if ((s.stack.drop 1).headD (UInt256.ofNat 0)).toNat = 0
    then s.pc.succ else s.stack.headD (UInt256.ofNat 0), stack := s.stack.drop 2}
def jumpModel (s : State) : State :=
  {s with pc := s.stack.headD (UInt256.ofNat 0), stack := s.stack.drop 1}
def resumeModel (s : State) : State :=
  {jumpModel s with pc := (jumpModel s).pc.succ}

theorem jumpi_run (s : State) (target flag : UInt256) (tail : List UInt256)
    (hstack : s.stack = target :: flag :: tail) (hcap : s.stack.length < 1024)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target.toNat = true) :
    runInstructions jumpiProgram s = some (conditionalModel s) := by
  have ht : tail.length < 1022 := by simp only [hstack, List.length_cons] at hcap; omega
  by_cases hz : flag.toNat = 0 <;>
    simp [jumpiProgram, conditionalModel, runInstructions,
      Challenge.EvmProof.Stepper.runInstr, hstack, hcap, ht, hvalid, UInt256.isTrue, hz]

theorem jump_run (s : State) (target : UInt256) (tail : List UInt256)
    (hstack : s.stack = target :: tail) (hcap : s.stack.length < 1024)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target.toNat = true) :
    runInstructions jumpProgram s = some (jumpModel s) := by
  have ht : tail.length < 1023 := by simp only [hstack, List.length_cons] at hcap; omega
  simp [jumpProgram, jumpModel, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hstack, hcap, ht, hvalid]

theorem jumpDest_run (s : State) (hcap : s.stack.length < 1024) :
    runInstructions jumpDestProgram s = some {s with pc := s.pc.succ} := by
  simp [jumpDestProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, hcap]

theorem resume_run (s : State) (target : UInt256) (tail : List UInt256)
    (hstack : s.stack = target :: tail) (hcap : s.stack.length < 1024)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target.toNat = true) :
    runInstructions resumeProgram s = some (resumeModel s) := by
  have hj := jump_run s target tail hstack hcap hvalid
  have hc : (jumpModel s).stack.length < 1024 := by
    simp only [jumpModel, hstack, List.drop_succ_cons, List.drop_zero, List.length_cons] at *
    omega
  exact runInstructions_append_some _ _ _ _ _ hj (jumpDest_run (jumpModel s) hc)

def hookProgram : List Instr :=
  [.op .JUMPDEST, .push 2 (UInt256.ofNat 5615), .op .JUMP]

theorem hook_run (s : State) (stack : List UInt256) (hcap : stack.length ≤ 1022)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5615 = true) :
    runInstructions hookProgram {s with pc := UInt256.ofNat 4816, stack := stack} =
      some {s with pc := UInt256.ofNat 5615, stack := stack} := by
  have h0 : stack.length < 1024 := by omega
  have h1 : stack.length + 1 < 1024 := by omega
  have hn : (UInt256.ofNat 5615).toNat = 5615 := rfl
  simp [hookProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h0, h1, hn, hvalid, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms jumpi_run
#print axioms jump_run
#print axioms jumpDest_run
#print axioms resume_run
#print axioms hook_run
end HistoricalSearch.CRTControl
