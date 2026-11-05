import Challenge.Modexp.Submission.Proofs.Prepared.R5Square
import Challenge.Modexp.Submission.Proofs.R5.ExecSquare

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.SquareRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open CycleSubmission.R5.ExecSquare

def sqV0_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol0_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV0_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol0_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV1_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol1_o0 ((sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV1_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol1_o1 ((sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV2_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol2_o0 ((sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV2_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol2_o1 ((sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV3_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol3_o0 ((sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV3_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol3_o1 ((sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV4_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol4_o0 ((sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV4_4 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol4_o4 ((sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV5_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol5_o0 ((sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV5_5 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol5_o5 ((sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV6_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol6_o0 ((sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV6_6 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol6_o6 ((sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV7_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol7_o0 ((sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV7_7 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol7_o7 ((sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV8_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol8_o0 ((sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a3 a4 n1 n2 n3 n4 P inv cnt

def sqV8_8 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol8_o8 ((sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a3 a4 n1 n2 n3 n4 P inv cnt

def sqV9_12 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqTail_o12 ((sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a4 n1 n2 n3 n4 P inv cnt

def sqProgram : List Instr := CycleSubmission.Prepared.R5Square.newProgram

private theorem raw_model_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv) :
    CycleSubmission.Prepared.R5Square.oldModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest = {s with pc := UInt256.ofNat 4826, stack := cnt :: (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: n1 :: n2 :: n3 :: n4 :: P :: inv :: (sqV9_12 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: rest} := by
  simp only [CycleSubmission.Prepared.R5Square.oldModel, h_n0, h_inv, fusePair, sqCol0_o0, sqCol0_o1, sqCol1_o0, sqCol1_o1, sqCol2_o0, sqCol2_o1, sqCol3_o0, sqCol3_o1, sqCol4_o0, sqCol4_o4, sqCol5_o0, sqCol5_o5, sqCol6_o0, sqCol6_o6, sqCol7_o0, sqCol7_o7, sqCol8_o0, sqCol8_o8, sqTail_o12, sqV0_0, sqV0_1, sqV1_0, sqV1_1, sqV2_0, sqV2_1, sqV3_0, sqV3_1, sqV4_0, sqV4_4, sqV5_0, sqV5_5, sqV6_0, sqV6_6, sqV7_0, sqV7_7, sqV8_0, sqV8_8, sqV9_12]

theorem sq_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv) :
    runInstructions sqProgram {s with pc := UInt256.ofNat 4185, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some {s with pc := UInt256.ofNat 4826, stack := cnt :: (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: n1 :: n2 :: n3 :: n4 :: P :: inv :: (sqV9_12 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: rest} := by
  exact (CycleSubmission.Prepared.R5Square.new_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest hcap hact).trans
    (congrArg some ((CycleSubmission.Prepared.R5Square.same_state s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest).symm.trans
      (raw_model_eq s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 rest h_n0 h_inv)))

#print axioms sq_run
end CycleSubmission.R5.SquareRun
