import Challenge.Modexp.Submission.Proofs.Fast.SquareInit
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRoute
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def testProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .push 2 2720, .op .MLOAD, .op .JUMPI]

theorem run_test (s : State) (pbi pa pb flag dst ret route : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 91 ≤ s.activeWords.toNat)
    (hr : MachineState.readWord s.memory 2720 = route)
    (htarget : Decode.isValidJumpDest s.executionEnv.code route.toNat = true) :
    runInstructions testProgram
      (framed s (UInt256.ofNat 4784)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed s
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then route else UInt256.ofNat 4794)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have haddr : (2720 : UInt256).toNat = 2720 := by decide
  have ha := EarlyCsub.activeWords_fix s 2720 32 (by decide) (by decide) hact
  by_cases hcond : UInt256.isTrue (UInt256.gt (negative32+pbi) pb)
  all_goals simp [testProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc8, hc9, hc10, haddr, ha, hr, htarget, hcond,
    State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def headerProgram : List Instr := [.push 2 2720, .op .MLOAD, .op .JUMP]

theorem run_header (s : State) (mem : ByteArray) (route : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1022) (hact : 91 ≤ s.activeWords.toNat)
    (hr : MachineState.readWord mem 2720 = route)
    (htarget : Decode.isValidJumpDest s.executionEnv.code route.toNat = true) :
    runInstructions headerProgram (SquareInit.stateAt s mem 4168 rest) =
      some (framed {s with memory := mem} route rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have haddr : (2720 : UInt256).toNat = 2720 := by decide
  have ha := EarlyCsub.activeWords_fix s 2720 32 (by decide) (by decide) hact
  simp [headerProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    SquareInit.stateAt, framed, hc0, hc1, haddr, ha, hr, htarget,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.SquareRoute
