import Challenge.Modexp.Submission.Proofs.Cycle.FinalBlocks
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
import Challenge.Modexp.Submission.Proofs.Cycle.CompareArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.CompareExecution
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.NormalizeMeaning CycleSubmission.Execution
open HistoricalSearch.CRTControl
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

noncomputable def step0 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10234, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 8).toNat < (n 8).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10242, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10241
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 8) (n 8) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare0_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare0Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare0Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare0Block.steps
    (s := {s with pc := UInt256.ofNat 10234, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 8) (n 8))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare0JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 8).toNat < (n 8).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10242, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 8).toNat < (n 8).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step1 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10242, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 8).toNat < (a 8).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10249, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10248
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 8) (n 8) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare1_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare1Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare1Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare1Block.steps
    (s := {s with pc := UInt256.ofNat 10242, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 8) (n 8))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare1JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 8).toNat < (a 8).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10249, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 8).toNat < (a 8).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step2 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10249, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 7).toNat < (n 7).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10258, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10257
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 7) (n 7) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare2_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare2Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare2Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare2Block.steps
    (s := {s with pc := UInt256.ofNat 10249, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 7) (n 7))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare2JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 7).toNat < (n 7).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10258, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 7).toNat < (n 7).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step3 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10258, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 7).toNat < (a 7).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10267, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10266
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 7) (n 7) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare3_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare3Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare3Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare3Block.steps
    (s := {s with pc := UInt256.ofNat 10258, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 7) (n 7))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare3JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 7).toNat < (a 7).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10267, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 7).toNat < (a 7).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step4 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10267, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 6).toNat < (n 6).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10276, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10275
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 6) (n 6) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare4_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare4Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare4Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare4Block.steps
    (s := {s with pc := UInt256.ofNat 10267, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 6) (n 6))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare4JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 6).toNat < (n 6).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10276, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 6).toNat < (n 6).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step5 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10276, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 6).toNat < (a 6).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10285, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10284
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 6) (n 6) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare5_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare5Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare5Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare5Block.steps
    (s := {s with pc := UInt256.ofNat 10276, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 6) (n 6))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare5JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 6).toNat < (a 6).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10285, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 6).toNat < (a 6).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step6 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10285, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 5).toNat < (n 5).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10294, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10293
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 5) (n 5) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare6_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare6Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare6Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare6Block.steps
    (s := {s with pc := UInt256.ofNat 10285, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 5) (n 5))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare6JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 5).toNat < (n 5).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10294, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 5).toNat < (n 5).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step7 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10294, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 5).toNat < (a 5).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10303, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10302
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 5) (n 5) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare7_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare7Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare7Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare7Block.steps
    (s := {s with pc := UInt256.ofNat 10294, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 5) (n 5))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare7JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 5).toNat < (a 5).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10303, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 5).toNat < (a 5).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step8 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10303, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 4).toNat < (n 4).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10312, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10311
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 4) (n 4) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare8_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare8Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare8Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare8Block.steps
    (s := {s with pc := UInt256.ofNat 10303, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 4) (n 4))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare8JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 4).toNat < (n 4).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10312, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 4).toNat < (n 4).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step9 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10312, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 4).toNat < (a 4).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10321, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10320
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 4) (n 4) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare9_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare9Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare9Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare9Block.steps
    (s := {s with pc := UInt256.ofNat 10312, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 4) (n 4))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare9JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 4).toNat < (a 4).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10321, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 4).toNat < (a 4).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step10 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10321, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 3).toNat < (n 3).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10330, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10329
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 3) (n 3) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare10_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare10Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare10Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare10Block.steps
    (s := {s with pc := UInt256.ofNat 10321, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 3) (n 3))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare10JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 3).toNat < (n 3).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10330, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 3).toNat < (n 3).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step11 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10330, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 3).toNat < (a 3).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10339, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10338
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 3) (n 3) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare11_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare11Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare11Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare11Block.steps
    (s := {s with pc := UInt256.ofNat 10330, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 3) (n 3))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare11JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 3).toNat < (a 3).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10339, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 3).toNat < (a 3).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step12 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10339, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 2).toNat < (n 2).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10346, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10345
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 2) (n 2) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare12_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare12Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare12Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare12Block.steps
    (s := {s with pc := UInt256.ofNat 10339, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 2) (n 2))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare12JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 2).toNat < (n 2).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10346, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 2).toNat < (n 2).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step13 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10346, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 2).toNat < (a 2).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10353, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10352
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 2) (n 2) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare13_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare13Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare13Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare13Block.steps
    (s := {s with pc := UInt256.ofNat 10346, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 2) (n 2))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare13JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 2).toNat < (a 2).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10353, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 2).toNat < (a 2).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step14 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10353, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 1).toNat < (n 1).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10363, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10362
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 1) (n 1) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare14_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare14Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare14Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare14Block.steps
    (s := {s with pc := UInt256.ofNat 10353, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 1) (n 1))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare14JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 1).toNat < (n 1).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10363, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 1).toNat < (n 1).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step15 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10363, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 1).toNat < (a 1).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10373, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10372
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 1) (n 1) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare15_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare15Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare15Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare15Block.steps
    (s := {s with pc := UInt256.ofNat 10363, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 1) (n 1))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare15JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 1).toNat < (a 1).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10373, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 1).toNat < (a 1).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step16 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10373, stack := frame a n slot0 slot1 rest}
      {s with pc := if (a 0).toNat < (n 0).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10386, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10385
    stack := UInt256.ofNat 10409 :: UInt256.lt (a 0) (n 0) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare16_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare16Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare16Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare16Block.steps
    (s := {s with pc := UInt256.ofNat 10373, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10409 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10867
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10409) (UInt256.lt (a 0) (n 0))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare16JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (a 0).toNat < (n 0).toNat then UInt256.ofNat 10409 else UInt256.ofNat 10386, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (a 0).toNat < (n 0).toNat
    · simp only [conditionalModel, tested, UInt256.lt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.lt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2


noncomputable def step17 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10386, stack := frame a n slot0 slot1 rest}
      {s with pc := if (n 0).toNat < (a 0).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10399, stack := frame a n slot0 slot1 rest} := by
  let tested : State := {s with
    pc := UInt256.ofNat 10398
    stack := UInt256.ofNat 10399 :: UInt256.gt (a 0) (n 0) :: frame a n slot0 slot1 rest}
  have hr := canonicalCompare17_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have he : canonicalCompare17Model s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP (n 8) slot1 mask slot0 (n 3) (a 8) rest = tested := by
    simp only [canonicalCompare17Model, hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7, hm.n0, hm.n1]
    rfl
  rw [he] at hr
  have h1 := FinalBlocks.canonicalCompare17Block.steps
    (s := {s with pc := UInt256.ofNat 10386, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest tested.executionEnv.code 10399 = true := by
    rw [show tested.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump10857
  have cap : tested.stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jumpi_run tested (UInt256.ofNat 10399) (UInt256.gt (a 0) (n 0))
    (frame a n slot0 slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalCompare17JumpBlock.steps (s := tested) (env.transfer rfl rfl) rfl hj
  have hb : conditionalModel tested =
      {s with pc := if (n 0).toNat < (a 0).toNat then UInt256.ofNat 10399 else UInt256.ofNat 10399, stack := frame a n slot0 slot1 rest} := by
    by_cases hp : (n 0).toNat < (a 0).toNat
    · simp only [conditionalModel, tested, UInt256.gt, if_pos hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 1).toNat = 1 by rfl, show ¬ (1:Nat)=0 by decide, if_false]
    · simp only [conditionalModel, tested, UInt256.gt, if_neg hp,
        List.drop_succ_cons, List.drop_zero, List.headD_cons,
        show (UInt256.ofNat 0).toNat = 0 by rfl, if_pos rfl]
      rfl
  rw [hb] at h2
  exact h1.trans h2

end CycleSubmission.CompareExecution
