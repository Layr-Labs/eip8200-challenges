import Challenge.Modexp.Submission.Proofs.CRT.CRTKernelExecution
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
namespace HistoricalSearch.CRTControl
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open HistoricalSearch.GeneratedColumns

theorem overflow_control (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8800 = true) :
    runInstructions jumpiProgram (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) = some (conditionalModel (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  let t := overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest
  have hc : t.stack.length < 1024 := by
    dsimp only [t, overflowModel]
    simp only [List.length_cons]
    omega
  exact jumpi_run t (UInt256.ofNat 8800) (t.stack.drop 1 |>.headD (UInt256.ofNat 0)) (t.stack.drop 2) (by rfl) hc hvalid

#print axioms overflow_control

theorem overflow_complete_of_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) (before : State)
    (hrun : runInstructions overflowProgram before = some (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest))
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8800 = true) :
    runInstructions (overflowProgram ++ jumpiProgram) before =
      some (conditionalModel (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  runInstructions_append_some _ _ _ _ _ hrun (overflow_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hvalid)

#print axioms overflow_complete_of_run

theorem overflow_next_pc (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) :
    (conditionalModel (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)).pc = (if (UInt256.shiftRight (MachineState.readWord s.memory 1600) (UInt256.ofNat 192)).toNat = 0 then UInt256.ofNat 8523 else UInt256.ofNat 8800) := by rfl

#print axioms overflow_next_pc

theorem count_control (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8800 = true) :
    runInstructions jumpiProgram (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) = some (conditionalModel (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  let t := countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest
  have hc : t.stack.length < 1024 := by
    dsimp only [t, countModel]
    simp only [List.length_cons]
    omega
  exact jumpi_run t (UInt256.ofNat 8800) (t.stack.drop 1 |>.headD (UInt256.ofNat 0)) (t.stack.drop 2) (by rfl) hc hvalid

#print axioms count_control

theorem count_complete_of_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) (before : State)
    (hrun : runInstructions countProgram before = some (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest))
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8800 = true) :
    runInstructions (countProgram ++ jumpiProgram) before =
      some (conditionalModel (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  runInstructions_append_some _ _ _ _ _ hrun (count_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hvalid)

#print axioms count_complete_of_run

theorem count_next_pc (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) :
    (conditionalModel (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)).pc = (if (MachineState.readWord s.memory 1728).toNat = 0 then UInt256.ofNat 8800 else UInt256.ofNat 8532) := by
  by_cases hz : (MachineState.readWord s.memory 1728).toNat = 0 <;>
    simp [conditionalModel, countModel, Challenge.EvmProof.Word.word_toNat_isZero,
      hz, Challenge.EvmProof.Word.succ_ofNat_mod]

#print axioms count_next_pc

theorem retain_control (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5858 = true) :
    runInstructions resumeProgram (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) = some (resumeModel (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  let t := retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest
  have hc : t.stack.length < 1024 := by
    dsimp only [t, retainModel]
    simp only [List.length_cons]
    omega
  exact resume_run t (UInt256.ofNat 5858) (t.stack.drop 1) (by rfl) hc hvalid

#print axioms retain_control

theorem retain_complete_of_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) (before : State)
    (hrun : runInstructions retainProgram before = some (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest))
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5858 = true) :
    runInstructions (retainProgram ++ resumeProgram) before =
      some (resumeModel (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  runInstructions_append_some _ _ _ _ _ hrun (retain_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hvalid)

#print axioms retain_complete_of_run

theorem retain_next_pc (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) :
    (resumeModel (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)).pc = (UInt256.ofNat 5859) := by rfl

#print axioms retain_next_pc

theorem exit_control (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3942 = true) :
    runInstructions jumpProgram (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) = some (jumpModel (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  let t := exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest
  have hc : t.stack.length < 1024 := by
    dsimp only [t, exitModel]
    simp only [List.length_cons]
    omega
  exact jump_run t (UInt256.ofNat 3942) (t.stack.drop 1) (by rfl) hc hvalid

#print axioms exit_control

theorem exit_complete_of_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) (before : State)
    (hrun : runInstructions exitProgram before = some (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest))
    (hcap : rest.length ≤ 982)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3942 = true) :
    runInstructions (exitProgram ++ jumpProgram) before =
      some (jumpModel (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  runInstructions_append_some _ _ _ _ _ hrun (exit_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hvalid)

#print axioms exit_complete_of_run

theorem exit_next_pc (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) :
    (jumpModel (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)).pc = (UInt256.ofNat 3942) := by rfl

#print axioms exit_next_pc

theorem overflow_complete_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8800 = true) :
    runInstructions (overflowProgram ++ jumpiProgram)
      {s with pc := UInt256.ofNat 8507, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
        some (conditionalModel (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  overflow_complete_of_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest _
    (overflow_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact) hcap hvalid

#print axioms overflow_complete_run

theorem count_complete_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 8800 = true) :
    runInstructions (countProgram ++ jumpiProgram)
      {s with pc := UInt256.ofNat 8523, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
        some (conditionalModel (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  count_complete_of_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest _
    (count_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact) hcap hvalid

#print axioms count_complete_run

theorem retain_complete_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5858 = true) :
    runInstructions (retainProgram ++ resumeProgram)
      {s with pc := UInt256.ofNat 8532, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
        some (resumeModel (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  retain_complete_of_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest _
    (retain_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact) hcap hvalid

#print axioms retain_complete_run

theorem exit_complete_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 3942 = true) :
    runInstructions (exitProgram ++ jumpProgram)
      {s with pc := UInt256.ofNat 8800, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
        some (jumpModel (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) :=
  exit_complete_of_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest _
    (exit_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact) hcap hvalid

#print axioms exit_complete_run

end HistoricalSearch.CRTControl
