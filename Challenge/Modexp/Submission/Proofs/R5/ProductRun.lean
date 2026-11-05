import Challenge.Modexp.Submission.Proofs.Prepared.R5Product
import Challenge.Modexp.Submission.Proofs.R5.ExecProduct

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.ProductRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open CycleSubmission.R5.ExecProduct

def prV0_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol0_o0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0

def prV0_1 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol0_o1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0

def prV1_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol1_o0 ((prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0

def prV1_1 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol1_o1 ((prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0

def prV2_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol2_o0 ((prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0

def prV2_1 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol2_o1 ((prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0

def prV3_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol3_o0 ((prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0

def prV3_1 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol3_o1 ((prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0

def prV4_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol4_o0 ((prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0

def prV4_4 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol4_o4 ((prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0

def prV5_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol5_o0 ((prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M

def prV5_5 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol5_o5 ((prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M

def prV6_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol6_o0 ((prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M

def prV6_6 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol6_o6 ((prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M

def prV7_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol7_o0 ((prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M

def prV7_7 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol7_o7 ((prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M

def prV8_0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol8_o0 ((prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x3 x4 n1 n2 n3 n4 P inv cntp b4 M

def prV8_8 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : UInt256 :=
  prCol8_o8 ((prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x3 x4 n1 n2 n3 n4 P inv cntp b4 M

def prSeg0Program : List Instr :=
  prCol0Program ++ prCol1Program

theorem prSeg0_run (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv)
    (h_M : MachineState.readWord s.memory 224 = M) :
    runInstructions prSeg0Program {s with pc := UInt256.ofNat 4830, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some {s with pc := UInt256.ofNat 4914, stack := (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  have h0 : runInstructions prCol0Program {s with pc := UInt256.ofNat 4830, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4859, stack := (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    (prCol0_run s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (prCol0_eq s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 rest h_b0 h_n0))
  have h1 : runInstructions prCol1Program {s with pc := UInt256.ofNat 4859, stack := (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4914, stack := (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    (prCol1_run s ((prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (prCol1_eq s ((prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 rest h_b0 h_b1 h_n0))
  have g0 : runInstructions (prCol0Program ++ prCol1Program) {s with pc := UInt256.ofNat 4830, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4914, stack := (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    runInstructions_append_some _ _ _ _ _ h0 h1
  exact g0

def prSeg1Program : List Instr :=
  prCol2Program ++ prCol3Program

theorem prSeg1_run (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv)
    (h_M : MachineState.readWord s.memory 224 = M) :
    runInstructions prSeg1Program {s with pc := UInt256.ofNat 3414, stack := (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some {s with pc := UInt256.ofNat 3591, stack := (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  have h2 : runInstructions prCol2Program {s with pc := UInt256.ofNat 3414, stack := (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3492, stack := (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    (prCol2_run s ((prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (prCol2_eq s ((prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 rest h_b0 h_b1 h_b2 h_n0))
  have h3 : runInstructions prCol3Program {s with pc := UInt256.ofNat 3492, stack := (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3591, stack := (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    (prCol3_run s ((prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (prCol3_eq s ((prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 rest h_b0 h_b1 h_b2 h_b3 h_n0))
  have g2 : runInstructions (prCol2Program ++ prCol3Program) {s with pc := UInt256.ofNat 3414, stack := (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3591, stack := (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    runInstructions_append_some _ _ _ _ _ h2 h3
  exact g2

def prSeg2Program : List Instr :=
  prCol4Program

theorem prSeg2_run (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv)
    (h_M : MachineState.readWord s.memory 224 = M) :
    runInstructions prSeg2Program {s with pc := UInt256.ofNat 3923, stack := (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some {s with pc := UInt256.ofNat 4049, stack := (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  have h4 : runInstructions prCol4Program {s with pc := UInt256.ofNat 3923, stack := (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4049, stack := (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} :=
    (prCol4_run s ((prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact).trans
      (congrArg some (prCol4_eq s ((prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 rest h_b0 h_b1 h_b2 h_b3 h_b4 h_n0 h_inv))
  exact h4

def prSeg3Program : List Instr := CycleSubmission.Prepared.R5Product.newProgram

private theorem raw_model_eq (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (rest : List UInt256)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_M : MachineState.readWord s.memory 224 = M) :
    CycleSubmission.Prepared.R5Product.oldModel s ((prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) (x0) (x1) (x2) (x3) (x4) (n1) (n2) (n3) (n4) (P) (inv :: cntp :: rest) = {s with pc := UInt256.ofNat 5276, stack := (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV8_8 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [CycleSubmission.Prepared.R5Product.oldModel, h_b1, h_b2, h_b3, h_b4, h_M, prCol5_o0, prCol5_o5, prCol6_o0, prCol6_o6, prCol7_o0, prCol7_o7, prCol8_o0, prCol8_o8, prV5_0, prV5_5, prV6_0, prV6_6, prV7_0, prV7_7, prV8_0, prV8_8]

theorem prSeg3_run (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv)
    (h_M : MachineState.readWord s.memory 224 = M) :
    runInstructions prSeg3Program {s with pc := UInt256.ofNat 4973, stack := (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some {s with pc := UInt256.ofNat 5276, stack := (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV8_8 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: (prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  exact (CycleSubmission.Prepared.R5Product.new_run s ((prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) (x0) (x1) (x2) (x3) (x4) (n1) (n2) (n3) (n4) (P) (inv :: cntp :: rest)
      (by simp only [List.length_cons]; omega) hact).trans
    (congrArg some ((CycleSubmission.Prepared.R5Product.same_state s ((prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) ((prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)) (x0) (x1) (x2) (x3) (x4) (n1) (n2) (n3) (n4) (P) (inv :: cntp :: rest)).symm.trans
      (raw_model_eq s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M rest h_b1 h_b2 h_b3 h_b4 h_M)))

#print axioms prSeg3_run
end CycleSubmission.R5.ProductRun
