import Challenge.Modexp.Submission.Proofs.Cycle.PackExecution
import Challenge.Modexp.Submission.Proofs.Fast.Exp
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.Return
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def program : List Instr := [.push 3 256, .push 2 2112, .op .RETURN]

def result (s : State) (stack : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10549
    stack := stack
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 2112 256}

theorem cons_run (instruction : Instr) (program : List Instr) (s t u : State)
    (h : Challenge.EvmProof.Stepper.runInstr instruction s = some t)
    (ht : runInstructions program t = some u) :
    runInstructions (instruction :: program) s = some u := by
  change (Challenge.EvmProof.Stepper.runInstr instruction s).bind (fun next => runInstructions program next) = _
  rw [h]
  exact ht

theorem run (s : State) (stack : List UInt256) (hcap : stack.length ≤ 1021)
    (hact : 88 ≤ s.activeWords.toNat) (_hrun : s.halt = .Running) :
    runInstructions program {s with pc := UInt256.ofNat 10542, stack := stack} =
      some (result s stack) := by
  have h0 : stack.length < 1024 := by omega
  have h1 : stack.length+1 < 1024 := by omega
  have h2 : stack.length+2 < 1024 := by omega
  have hf := Monpro.activeWords_fix s 2112 256 (by decide) (by norm_num) hact
  have hP1 : Challenge.EvmProof.Stepper.runInstr (.push 3 256)
      {s with pc := UInt256.ofNat 10542, stack := stack} =
      some {s with pc := UInt256.ofNat 10546, stack := UInt256.ofNat 256 :: stack} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, h0, ite_true]
    rfl
  have hP2 : Challenge.EvmProof.Stepper.runInstr (.push 2 2112)
      {s with pc := UInt256.ofNat 10546, stack := UInt256.ofNat 256 :: stack} =
      some {s with pc := UInt256.ofNat 10549, stack := UInt256.ofNat 2112 :: UInt256.ofNat 256 :: stack} := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons, h1, ite_true]
    rfl
  have hRet : Challenge.EvmProof.Stepper.runInstr (.op .RETURN)
      {s with pc := UInt256.ofNat 10549, stack := UInt256.ofNat 2112 :: UInt256.ofNat 256 :: stack} =
      some (result s stack) := by
    simp only [Challenge.EvmProof.Stepper.runInstr, List.length_cons,
      show stack.length+1+1 = stack.length+2 by omega, h2, ite_true]
    change some {s with
      pc := UInt256.ofNat 10549
      stack := stack
      halt := .Returned
      hReturn := MachineState.readPadded s.memory 2112 256
      activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 256)} = _
    rw [hf]
    rfl
  exact cons_run _ _ _ _ _ hP1
    (cons_run _ _ _ _ _ hP2 (cons_run _ _ _ _ _ hRet rfl))



def block : Block Artifact.artifact .Osaka 10542 program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8406 3 10542 program
    (by change 8406+3 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8406+3 ≤ 8736)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

noncomputable def gasSteps (s : State) (stack : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : stack.length ≤ 1021) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10542, stack := stack} (result s stack) :=
  block.steps (env.transfer rfl rfl) rfl (run s stack hcap hact env.running)


theorem returned_bytes (s : State) (stack : List UInt256) (A : Nat)
    (h : Model.FastRepresents s.memory 2112 8 A) :
    (result s stack).hReturn = Precompile.natToBytes A 256 :=
  Exp.readPadded_eq_natToBytes (mem := s.memory) (ptr := 2112) (count := 8) (value := A) (msize := 256) h (by decide)

end CycleSubmission.Return
