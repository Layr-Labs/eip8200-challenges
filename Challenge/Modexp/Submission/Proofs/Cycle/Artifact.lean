import Challenge.Modexp.Submission.Proofs.Cycle.InstructionLookup
import Challenge.Modexp.Submission.Proofs.Cycle.Bytes
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper


/-- Constant bounded opcode witnesses; source-size sharing only. -/
private abbrev dup0 : Operation.DupOp := ⟨0,by decide⟩
private abbrev dup1 : Operation.DupOp := ⟨1,by decide⟩
private abbrev dup2 : Operation.DupOp := ⟨2,by decide⟩
private abbrev dup3 : Operation.DupOp := ⟨3,by decide⟩
private abbrev dup4 : Operation.DupOp := ⟨4,by decide⟩
private abbrev dup5 : Operation.DupOp := ⟨5,by decide⟩
private abbrev dup6 : Operation.DupOp := ⟨6,by decide⟩
private abbrev dup7 : Operation.DupOp := ⟨7,by decide⟩
private abbrev dup8 : Operation.DupOp := ⟨8,by decide⟩
private abbrev dup9 : Operation.DupOp := ⟨9,by decide⟩
private abbrev dup10 : Operation.DupOp := ⟨10,by decide⟩
private abbrev dup11 : Operation.DupOp := ⟨11,by decide⟩
private abbrev dup12 : Operation.DupOp := ⟨12,by decide⟩
private abbrev dup13 : Operation.DupOp := ⟨13,by decide⟩
private abbrev dup14 : Operation.DupOp := ⟨14,by decide⟩
private abbrev dup15 : Operation.DupOp := ⟨15,by decide⟩
private abbrev swap0 : Operation.SwapOp := ⟨0,by decide⟩
private abbrev swap1 : Operation.SwapOp := ⟨1,by decide⟩
private abbrev swap2 : Operation.SwapOp := ⟨2,by decide⟩
private abbrev swap3 : Operation.SwapOp := ⟨3,by decide⟩
private abbrev swap4 : Operation.SwapOp := ⟨4,by decide⟩
private abbrev swap5 : Operation.SwapOp := ⟨5,by decide⟩
private abbrev swap6 : Operation.SwapOp := ⟨6,by decide⟩
private abbrev swap7 : Operation.SwapOp := ⟨7,by decide⟩
private abbrev swap8 : Operation.SwapOp := ⟨8,by decide⟩
private abbrev swap9 : Operation.SwapOp := ⟨9,by decide⟩
private abbrev swap10 : Operation.SwapOp := ⟨10,by decide⟩
private abbrev swap11 : Operation.SwapOp := ⟨11,by decide⟩
private abbrev swap12 : Operation.SwapOp := ⟨12,by decide⟩
private abbrev swap13 : Operation.SwapOp := ⟨13,by decide⟩
private abbrev swap14 : Operation.SwapOp := ⟨14,by decide⟩
private abbrev swap15 : Operation.SwapOp := ⟨15,by decide⟩

private abbrev i0 : Instr := .op (.Dup dup0)
private abbrev i1 : Instr := .op .MULMOD
private abbrev i2 : Instr := .op .MLOAD
private abbrev i3 : Instr := .op .ADD
private abbrev i4 : Instr := .op (.Dup dup9)
private abbrev i5 : Instr := .op (.Dup dup1)
private abbrev i6 : Instr := .op .MUL
private abbrev i7 : Instr := .op (.Dup dup3)
private abbrev i8 : Instr := .op (.Dup dup11)
private abbrev i9 : Instr := .op (.Dup dup15)
private abbrev i10 : Instr := .op (.Dup dup5)
private abbrev i11 : Instr := .op (.Dup dup14)
private abbrev i12 : Instr := .op (.Dup dup10)
private abbrev i13 : Instr := .op (.Dup dup12)
private abbrev i14 : Instr := .op (.Swap swap1)
private abbrev i15 : Instr := .op (.Dup dup2)
private abbrev i16 : Instr := .op (.Swap swap0)
private abbrev i17 : Instr := .op (.Swap swap3)
private abbrev i18 : Instr := .op .MSTORE
private abbrev i19 : Instr := .op (.Dup dup4)
private abbrev i20 : Instr := .op (.Dup dup13)
private abbrev i21 : Instr := .op .JUMPDEST
private abbrev i22 : Instr := .op (.Dup dup6)
private abbrev i23 : Instr := .op .AND
private abbrev i24 : Instr := .op (.Dup dup8)
private abbrev i25 : Instr := .op (.Dup dup7)
private abbrev i26 : Instr := .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775
private abbrev i27 : Instr := .push 0 0
private abbrev i28 : Instr := .op (.Swap swap2)
private abbrev i29 : Instr := .op .SUB
private abbrev i30 : Instr := .op (.Swap swap4)
private abbrev i31 : Instr := .op .CALLDATALOAD
private abbrev i32 : Instr := .push 2 2048
private abbrev i33 : Instr := .push 2 480
private abbrev i34 : Instr := .push 1 32
private abbrev i35 : Instr := .op .JUMPI
private abbrev i36 : Instr := .push 1 128
private abbrev i37 : Instr := .push 1 96
private abbrev i38 : Instr := .op .POP
private abbrev i39 : Instr := .push 1 64
private abbrev i40 : Instr := .push 1 160
private abbrev i41 : Instr := .push 1 224
private abbrev i42 : Instr := .push 1 192
private abbrev i43 : Instr := .op .SHR
private abbrev i44 : Instr := .op .JUMP
private abbrev i45 : Instr := .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935
private abbrev i46 : Instr := .op .GT
private abbrev i47 : Instr := .push 2 768
private abbrev i48 : Instr := .push 2 2112
private abbrev i49 : Instr := .push 2 1216
private abbrev i50 : Instr := .op (.Swap swap5)
private abbrev i51 : Instr := .op .MSIZE
private abbrev i52 : Instr := .op (.Swap swap11)
private abbrev i53 : Instr := .op .SHL
private abbrev i54 : Instr := .op .LT
private abbrev i55 : Instr := .push 2 1280
private abbrev i56 : Instr := .op (.Swap swap6)
private abbrev i57 : Instr := .op (.Swap swap7)
private abbrev i58 : Instr := .op (.Swap swap15)
private abbrev i59 : Instr := .op .OR
private abbrev i60 : Instr := .push 1 1
private abbrev i61 : Instr := .push 1 16
private abbrev i62 : Instr := .push 2 1248
private abbrev i63 : Instr := .push 2 1792
private abbrev i64 : Instr := .push 2 1856
private abbrev i65 : Instr := .push 2 1888
private abbrev i66 : Instr := .push 2 2080
private abbrev i67 : Instr := .push 2 2720
private abbrev i68 : Instr := .push 2 10352
private abbrev i69 : Instr := .push 2 1824
private abbrev i70 : Instr := .push 2 1920
private abbrev i71 : Instr := .push 2 1952
private abbrev i72 : Instr := .push 2 1984
private abbrev i73 : Instr := .push 2 2016
private abbrev i74 : Instr := .op (.Swap swap8)
private abbrev i75 : Instr := .op .RETURN
private abbrev i76 : Instr := .op (.Swap swap10)
private abbrev i77 : Instr := .push 2 1088
private abbrev i78 : Instr := .op .CALLDATACOPY
private abbrev i79 : Instr := .push 2 10342
private abbrev i80 : Instr := .op .NOT
private abbrev i81 : Instr := .push 1 3
private abbrev i82 : Instr := .push 2 1376
private abbrev i83 : Instr := .op .MCOPY
private abbrev i84 : Instr := .push 2 1344
private abbrev i85 : Instr := .push 2 2208

private def instructionsPart0 : List Instr :=
  [.push 1 34,i31,i39,i31,i3,.push 3 2097184,.op .XOR,.push 2 564,i35,i37,i31,i36,i31,i40,i31,i5,i5,i29,.push 2 8191,i60,i31,i29,i43,.push 2 717,i35,i27,i31,i34,.op .XOR,.push 1 97,i35,i21,i5,i80,i5,i3,.push 2 717,i35,.push 2 10612,i44,.push 32 26689440342447178617115869845918039756797228267049433585260346420242739014315,i27,i21,i21,i21,i34,i27,i31,i5,i5,i46,.push 1 207,i35,i16,i29,i37,i31,i5,i81,i53,i43,i5,i36,i29,i31,i15,i40,i29,i31,.push 1 48,i44,i21,i10,i31,i7,i34,i29,i81,i53,i43,i0,.push 1 149,i35,i7,i27,i75,i21,i27,i27,i21,i7,i5,.op .EQ,.push 1 180,i35,i15,i5,i24,i3,i31,i27,.op .BYTE,i19,.push 2 256,i60,i50,i1,.op .ADDMOD,i14,i3,.push 1 152,i44,i21,i38,i5,i27,.op .ISZERO,i54,i27,i21,i10,i5,.op .EQ,.push 2 3946,i35,i0,i4,i3]

private theorem instructionsPart0_wf :
    instructionsPart0.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart0,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart1 : List Instr :=
  [i0,i31,i27,.op .BYTE,i27,.push 2 3962,i44,i21,.push 2 9248,.op .CALLDATASIZE,i27,i78,i39,i31,i34,i31,i27,i31,i15,i5,i7,i3,i37,i3,.push 2 1024,i78,i0,i37,.push 2 5120,i78,i27,i7,i21,i27,i80,i3,i0,.push 2 1024,i3,i2,i5,i28,i59,i14,.push 1 242,i35,i38,.push 2 268,i35,i21,i15,i27,i75,i21,i60,i7,.push 2 3071,i3,.op .MSTORE8,i38,i27,i21,i5,i81,i53,i5,.op .EQ,.push 2 363,i35,i15,.push 2 3072,i0,.push 2 302,.push 2 380,i44,i21,i15,i27,.push 2 3072,i83,i0,i81,i43,i27,i31,i3,i37,i3,i31,i5,.push 1 7,i23,i53,.push 1 255,i43,.op .ISZERO,.push 2 355,i35,i27,i31,.push 2 5120,.push 2 3072,.push 2 348,.push 2 380,i44,i21,i15,i27,.push 2 3072,i83,i21,i60,i3,.push 2 279,i44,i21,i15,.push 2 3072,i27,i83,.push 2 8192,.push 2 264,.push 2 451,i44,i21,i39,i31,.op .CALLDATASIZE]

private theorem instructionsPart1_wf :
    instructionsPart1.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart1,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart2 : List Instr :=
  [i27,i78,i27,i21,i19,i81,i53,i5,.op .EQ,.push 2 444,i35,i27,.push 2 407,.push 2 451,i44,i21,i0,i81,i43,i19,i3,i2,i5,.push 1 7,i23,i53,.push 1 255,i43,.op .ISZERO,.push 2 436,i35,i15,.push 2 436,.push 2 451,i44,i21,i60,i3,.push 2 388,i44,i21,i38,i28,i38,i38,i38,i44,i21,.push 2 1024,i21,i60,i39,i31,i21,i27,i80,i3,i0,i10,i3,i2,i27,.op .BYTE,i5,i2,i27,.op .BYTE,i3,i7,i15,i3,i2,i80,i27,.op .BYTE,i21,i3,i15,i3,i0,i15,.op .MSTORE8,.push 1 8,i43,i14,i38,i0,.push 2 461,i35,i38,.push 2 514,i35,i14,i38,.push 2 8192,.push 2 455,i44,i21,i38,i16,i38,i44,i21,i27,i31,i34,i31,i39,i31,i0,.push 2 536,i35,i27,i27,i75,i21,i15,i37,i3,i15,i5,i3,i34,i7,i46,.push 1 207,i35,.push 2 1186]

private theorem instructionsPart2_wf :
    instructionsPart2.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart2,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart3 : List Instr :=
  [i5,i7,i37,i22,i24,i12,.push 1 131,i44,i21,i39,i31,.push 1 33,i5,i29,.push 1 223,i54,.push 2 3473,i35,i34,i31,i27,i31,.push 1 31,i7,i3,.push 1 5,i43,i0,.push 1 5,i53,i37,i7,i3,i19,i3,i0,i31,i27,.op .SGT,.op .ISZERO,i34,i25,i7,i3,i29,i31,i80,i0,i27,i29,i23,.push 1 2,i46,i25,.push 1 127,i23,i59,i59,.push 1 207,i35,i7,i37,i3,.push 2 2656,i18,i5,i51,i18,i34,i15,i29,.push 2 2752,i18,i5,i66,i3,i51,i18,i10,i5,i27,i78,i38,.push 2 2357,i44,i21,i38,i19,i60,i27,i75,i21,i21,.push 5 137506062208,.push 1 68,i31,i29,.push 2 519,i35,i27,i31,i60,i29,i34,i31,.push 1 2,i29,i59,.push 1 100,i31,i59,.push 2 519,i35,i34,.push 1 62,i27,.op .CODECOPY,i51,i27,i75,i21,i0,i7,i60,i27,i18,i0,i51]

private theorem instructionsPart3_wf :
    instructionsPart3.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart3,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart4 : List Instr :=
  [i18,i5,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i20,i11,i1,i0,i51,i18,i20,i1,i0,i51,i18,i13,i1,i0,i51,i18,i8,i1,i0,i51,i18,i12,i1,i0,i51,i18,i4,i1,i0,i51,i18,i24,i1,i0,i51,i18,i25,i1,i0,i51,i18,i22,i1,i0,i51,i18,i10,i1,i0,i51,i18,i19,i1,i0,i51,i18,i7,i1,i0,i51,i18,i15,i1,i0,i51,i18,i1,i51,i18,i5,i81,i43,i51,i18,i5,.push 1 7,i43,i51,i18,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0]

private theorem instructionsPart4_wf :
    instructionsPart4.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart4,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart5 : List Instr :=
  [i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0]

private theorem instructionsPart5_wf :
    instructionsPart5.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart5,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart6 : List Instr :=
  [i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0]

private theorem instructionsPart6_wf :
    instructionsPart6.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart6,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart7 : List Instr :=
  [i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,.push 2 514,i2,i33,i23,i2,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 482,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 515,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 483,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 516,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 484,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 517,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 485,i2,i33,i23,i2,i1,i0,i1]

private theorem instructionsPart7_wf :
    instructionsPart7.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart7,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart8 : List Instr :=
  [i0,i1,i0,i1,i0,i1,.push 2 518,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 486,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 519,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 487,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 520,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 488,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 521,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 489,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 522,i2,i33,i23,i2,i1,i0,i1,i0,i1]

private theorem instructionsPart8_wf :
    instructionsPart8.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart8,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart9 : List Instr :=
  [i0,i1,i0,i1,.push 2 490,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 523,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 491,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 524,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 492,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 525,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 493,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 526,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 494,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1]

private theorem instructionsPart9_wf :
    instructionsPart9.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart9,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart10 : List Instr :=
  [i0,i1,.push 2 527,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 495,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 528,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 496,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 529,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 497,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 530,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 498,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 531,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1]

private theorem instructionsPart10_wf :
    instructionsPart10.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart10,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart11 : List Instr :=
  [.push 2 499,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 532,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 500,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 533,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 501,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 534,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 502,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 535,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 503,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 536,i2]

private theorem instructionsPart11_wf :
    instructionsPart11.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart11,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart12 : List Instr :=
  [i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 504,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 537,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 505,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 538,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 506,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 539,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 507,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 540,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 508,i2,i33,i23]

private theorem instructionsPart12_wf :
    instructionsPart12.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart12,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart13 : List Instr :=
  [i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 541,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 509,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 542,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 510,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 543,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 511,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 544,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 512,i2,i33,i23,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,i25,i60,i53,i33,i23,i2]

private theorem instructionsPart13_wf :
    instructionsPart13.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart13,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart14 : List Instr :=
  [i1,i0,i1,i0,i1,i0,i1,i0,i1,i15,.push 1 5,i53,i33,i23,i2,i1,i27,i18,i34,i27,i75,i21,i37,i2,i27,i29,i82,i18,.push 2 2436,i44,i21,i27,.push 3 2336,i44,i27,i27,i27,i27,i27,i21,i0,i37,i3,i31,.push 1 232,i43,.push 3 65537,.op .XOR,i34,i31,i81,.op .XOR,i59,.push 1 207,i35,.push 1 15,i21,i27,i5,.push 7 512,i48,.push 2 3710,.push 2 3146,i44,i21,i0,i7,.op .XOR,.push 1 207,i35,i0,i37,i48,i78,.push 2 2378,.push 2 3484,i44,i21,i0,i48,.push 2 256,i83,i0,i36,.op .EQ,.push 2 2284,i35,i41,i2,i27,i29,.push 2 1504,i18,i42,i2,i80,.push 2 1472,i18,i40,i2,i80,.push 2 1440,i18,i36,i2,i80,.push 2 1408,i18,i37,i2,i80,i82,i18,i21,i39,i2,i80,i84,i18,i34,i2,i80,.push 2 1312,i18,i27,i2,i0,i80]

private theorem instructionsPart14_wf :
    instructionsPart14.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart14,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart15 : List Instr :=
  [i55,i18,i0,i27,i29,i5,i23,i0,.op .CLZ,i0,i60,i3,.push 2 1600,i18,.push 1 255,i29,.push 2 1536,i18,i16,.op .DIV,i0,.push 2 1568,i18,i0,i0,i27,i29,.op .MOD,.push 2 1632,i18,.push 2 2752,i2,i2,i0,i15,i6,i0,i81,i6,.push 1 2,.op .XOR,i0,i15,i6,.push 1 2,i29,i6,i0,i15,i6,.push 1 2,i29,i6,i0,i15,i6,.push 1 2,i29,i6,i0,i15,i6,.push 1 2,i29,i6,i0,i15,i6,.push 1 2,i29,i6,i0,i14,i6,.push 1 2,i29,i6,i0,i14,i6,.push 2 1664,i18,i6,i27,i29,i67,i18,.push 4 2310,i19,i60,.op .EQ,.push 2 2656,i2,i31,i27,.op .BYTE,i81,.op .EQ,i23,i19,i19,i34,i2,.push 4 128,i43,.push 2 1536,i2,.push 2 1568,i2,.push 2 1664,i2,.push 2 1632,i2,.push 2 1504,i2,.push 2 1472,i2,.push 2 1440,i2,.push 2 1408,i2,i82,i2,i84,i2,.push 2 1312,i2,i13]

private theorem instructionsPart15_wf :
    instructionsPart15.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart15,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart16 : List Instr :=
  [i9,i43,i20,.push 2 2008,i6,.push 2 18724,i29,i16,i5,i44,i21,i9,i48,i66,i83,i66,i2,i0,i11,i43,i16,.push 2 1600,i2,i53,i48,i2,i9,i43,i3,i20,i0,i20,i19,i1,i15,.op .ADDMOD,i16,i29,i13,i6,i9,i5,i36,i43,i6,i5,i27,i2,i6,i48,i2,i29,i54,i16,i29,i45,i14,i11,i46,i15,i3,i59,i0,i8,i6,i15,i13,i7,i1,i5,.push 2 2336,i18,i0,i15,i46,i16,i29,i29,i5,i8,i6,i7,i13,i19,i1,i0,i15,i46,i29,i5,i7,i3,.push 2 2304,i2,i5,i3,i0,.push 2 2304,i18,i5,i46,i17,i46,i29,i29,i3,i5,i12,i6,i7,i8,i19,i1,i0,i15,i46,i29,i5,i7,i3,.push 2 2272,i2,i5,i3,i0,.push 2 2272,i18,i5]

private theorem instructionsPart16_wf :
    instructionsPart16.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart16,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart17 : List Instr :=
  [i46,i17,i46,i29,i29,i3,i5,i4,i6,i7,i12,i19,i1,i0,i15,i46,i29,i5,i7,i3,.push 2 2240,i2,i5,i3,i0,.push 2 2240,i18,i5,i46,i17,i46,i29,i29,i3,i5,i24,i6,i7,i4,i19,i1,i0,i15,i46,i29,i5,i7,i3,i85,i2,i5,i3,i0,i85,i18,i5,i46,i17,i46,i29,i29,i3,i5,i25,i6,i7,i24,i19,i1,i0,i15,i46,i29,i5,i7,i3,.push 2 2176,i2,i5,i3,i0,.push 2 2176,i18,i5,i46,i17,i46,i29,i29,i3,i5,i22,i6,i7,i25,i19,i1,i0,i15,i46,i29,i5,i7,i3,.push 2 2144,i2,i5,i3,i0,.push 2 2144,i18,i5,i46,i17,i46,i29,i29,i3,i55,i2,i7,i7,i15,i6,i14,i19,i1,i0]

private theorem instructionsPart17_wf :
    instructionsPart17.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart17,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart18 : List Instr :=
  [i15,i46,i29,i5,i7,i3,i48,i2,i5,i3,i0,i48,i18,i5,i46,i17,i46,i29,i29,i3,i66,i2,i3,i29,i0,i66,i18,.push 30 3069,i35,i21,i3,i0,i15,i35,i21,i58,.push 7 10971,i35,i58,i11,i11,i14,i44,.push 1 0,i21,i38,i21,i27,.push 2 2784,i2,i21,i0,i2,i48,i15,i29,i2,i5,i3,i16,i5,i54,i16,i7,i3,i28,i7,i54,i59,i14,i5,i18,.push 1 31,i80,i3,.push 2 2111,i5,i46,.push 2 3077,i35,i38,i66,i2,i5,i3,i0,i66,i18,i54,.op .ISZERO,.push 2 3071,i35,i27,i80,.push 6 3046,i44,.push 2 3051,i44,i21,i27,i27,i27,i27,i36,i2,i45,i27,.push 2 3347,i27,i76,i9,i67,i2,i76,i5,i27,.op (.Swap swap13),i5,i0,i3,i64,i3,i83,i14,.push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,i3,i14,i16]

private theorem instructionsPart18_wf :
    instructionsPart18.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart18,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart19 : List Instr :=
  [i15,i3,i5,i44,i21,i0,i39,i2,i10,i6,i3,i34,i2,i22,i6,i3,i27,i2,i25,i6,i3,i12,i19,i6,i3,i4,i7,i6,i3,i11,i6,i61,i43,i16,i20,i39,i2,i22,i1,i3,i20,i34,i2,i25,i1,i3,i20,i27,i2,i24,i1,i3,i20,i8,i10,i1,i3,i20,i12,i19,i1,i3,i20,i40,i2,i7,i1,i3,i20,i16,i32,i1,i0,i37,i2,i22,i6,i3,i39,i2,i25,i6,i3,i34,i2,i24,i6,i3,i27,i2,i4,i6,i3,i13,i10,i6,i3,i8,i19,i6,i3,i12,i7,i6,i3,i9,i6,i61,i43,i16,i11,i37,i2,i25,i1,i3,i11,i39,i2,i24,i1,i3,i11,i34,i2,i4,i1,i3]

private theorem instructionsPart19_wf :
    instructionsPart19.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart19,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart20 : List Instr :=
  [i11,i27,i2,i12,i1,i3,i11,i20,i22,i1,i3,i11,i13,i10,i1,i3,i11,i8,i19,i1,i3,i11,i40,i2,i7,i1,i3,i11,i16,i32,i1,.push 2 3747,i44,i21,i34,i31,.push 2 673,i35,i39,i31,i34,i54,.push 2 673,i35,i39,.push 2 4717,i44,i29,i21,i85,i2,i37,i2,i0,i15,i29,i65,i18,i46,.push 2 3611,i44,i21,.push 2 3428,i35,i27,i27,i75,i29,i29,i29,i21,i27,i2,i48,i2,i54,i16,i35,.push 2 2378,i48,.push 2 2688,i2,i36,.op .EQ,.push 2 3453,i35,i21,.push 2 2336,i2,i41,i2,i0,i15,i29,i73,i18,i46,i0,i42,i2,i3,i0,.push 2 2304,i2,i5,i5,i29,i72,i18,i54,i14,i46,i59,i0,i40,i2,i3,i0,.push 2 2272,i2,i5,i5,i29,i71,i18,i54,i14,i46]

private theorem instructionsPart20_wf :
    instructionsPart20.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart20,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart21 : List Instr :=
  [i59,i0,i36,i2,i3,i0,.push 2 2240,i2,i5,i5,i29,i70,i18,i54,i14,i46,i59,i0,i37,i2,i3,i0,i85,i2,i5,i5,i29,i65,i18,i54,i14,i46,i59,i21,i0,i39,i2,i3,i0,.push 2 2176,i2,i5,i5,i29,i64,i18,i54,i14,i46,i59,i0,i34,i2,i3,i0,.push 2 2144,i2,i5,i5,i29,i69,i18,i54,i14,i46,i59,i0,i27,i2,i3,i0,i48,i2,i5,i5,i29,i63,i18,i54,i14,i46,i59,.op .ISZERO,i66,i2,i59,.push 2 3699,i35,.push 2 3688,i44,i21,i48,.push 2 2688,i2,i14,i83,i44,i21,i63,.push 2 2688,i2,i14,i83,i44,i21,i33,i29,i0,i36,i3,.op .ISZERO,.push 2 5197,i35,.push 2 2368,i2,i80,.push 1 146,i43,.push 2 5383,i35,.push 1 207,i44,i21,i21,i21,i21,i21,i21]

private theorem instructionsPart21_wf :
    instructionsPart21.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart21,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart22 : List Instr :=
  [i21,i21,i21,i0,i9,i36,i2,i24,i1,i3,i9,i37,i2,i4,i1,i3,i9,i39,i2,i12,i1,i3,i9,i34,i2,i8,i1,i3,i9,i27,i2,i13,i1,i3,i9,i9,i25,i1,i3,i9,i11,i22,i1,i3,i9,i20,i10,i1,i3,i9,i13,i19,i1,i3,i16,i36,i2,i25,i6,i3,i37,i2,i24,i6,i3,i39,i2,i4,i6,i3,i34,i2,i12,i6,i3,i27,i2,i8,i6,i3,i11,i22,i6,i3,i20,i10,i6,i3,i13,i19,i6,i3,i8,i7,i6,i3,i42,i2,i6,i61,i43,i30,i38,i11,i40,i2,i22,i1,i3,i11,i16,i32,i1,.push 2 4758,i44,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3]

private theorem instructionsPart22_wf :
    instructionsPart22.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart22,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart23 : List Instr :=
  [i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i3,i21,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,i38,.push 2 2284,i3,i44,i21,i38,i38,i38,i60,i3,.push 1 187,i44,i21,i38,i0,i22,i34,i29,i81,i53,i53,i27,i18,i10,i27,i75,i21,i60,i22,i29,i21,i25,i60,i19,i19,.push 1 7,i29,i43,i23,i15,i6,i60,i3,i5,i24,i0,i1,i1,i50,i38,i60,i15,i3,i14,.push 1 7,i46,.push 2 3967,i35,i38,.push 2 3936,i44,i21,i0,i0,i6,i8,i6,i61,i43,i12,i8,i7,i0,i0,i3,i30,i1,i13,i40,i2,i19,i1,i3,i32,i1,i0]

private theorem instructionsPart23_wf :
    instructionsPart23.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart23,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart24 : List Instr :=
  [i19,i19,i6,i3,i24,i7,i6,i3,i20,i6,i61,i43,i16,i13,i10,i10,i1,i3,i13,i4,i19,i1,i3,i13,i40,i2,i7,i1,i3,i13,i16,i32,i1,i0,i22,i10,i6,i3,i10,i0,i6,i3,i12,i19,i6,i3,i4,i7,i6,i3,i11,i6,i61,i43,i16,i20,i25,i22,i1,i3,i20,i22,i0,i0,i3,i57,i1,i3,i20,i8,i10,i1,i3,i20,i12,i19,i1,i3,i20,i40,i2,i7,i1,i3,i20,i16,i32,i1,i0,i24,i22,i6,i24,i24,i6,i3,i3,i13,i10,i6,i3,i8,i19,i6,i3,i12,i7,i6,i3,i9,i6,i61,i43,i16,i11,i4,i25,i1,i9,i4,i4,i1,i3,i3,i11,i20,i22,i1]

private theorem instructionsPart24_wf :
    instructionsPart24.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart24,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart25 : List Instr :=
  [i3,i11,i13,i10,i1,i3,i11,i8,i19,i1,i3,i11,i40,i2,i7,i1,i3,i11,i16,i32,i1,i11,i22,i8,i1,i9,i24,i8,i1,i3,i5,i3,i9,i4,i0,i1,i3,i9,i9,i25,i1,i3,i9,i11,i22,i1,i3,i9,i20,i10,i1,i3,i9,i13,i19,i1,i3,i16,i12,i25,i6,i12,i4,i6,i3,i3,i24,i0,i0,i3,.op (.Swap swap9),i6,i3,i11,i22,i6,i3,i20,i10,i6,i3,i13,i19,i6,i3,i8,i7,i6,i3,i42,i2,i6,i61,i43,i30,i38,i11,i40,i2,i22,i1,i3,i11,i16,i32,i1,i0,i12,i24,i6,i12,i12,i6,i3,i3,i11,i10,i6,i3,i20,i19,i6,i3,i13,i7,i6,i3,i8]

private theorem instructionsPart25_wf :
    instructionsPart25.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart25,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart26 : List Instr :=
  [i22,i6,i3,i16,i9,i0,i13,i12,i1,i16,i8,i8,i1,i3,i3,i9,i9,i22,i1,i3,i9,i11,i10,i1,i3,i9,i20,i19,i1,i3,i9,i13,i25,i1,i3,i16,i26,i23,i0,i56,i38,i9,i14,i29,i5,i3,i32,i1,i0,i12,i4,i6,i3,i4,i0,i6,i3,i11,i19,i6,i3,i20,i7,i6,i3,i13,i22,i6,i3,i16,i9,i8,i12,i1,i3,i9,i12,i0,i0,i3,i52,i1,i3,i9,i9,i10,i1,i3,i9,i11,i19,i1,i3,i9,i20,i25,i1,i3,i16,i26,i23,i0,i57,i38,i9,i14,i29,i5,i3,i32,i1,i0,i12,i12,i6,i3,i11,i7,i6,i3,i20,i22,i6,i3,i26,i23,i57,i38]

private theorem instructionsPart26_wf :
    instructionsPart26.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart26,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart27 : List Instr :=
  [i11,i4,i8,i1,i3,i11,i15,i9,i1,i3,i11,i10,i11,i1,i3,i32,i9,i4,i5,i17,i29,i3,i1,i0,i12,i0,i6,i3,i10,i9,i6,i3,i26,i23,i74,i38,i11,i12,i0,i1,i3,i11,i10,i9,i1,i3,i32,i9,i12,i5,i17,i29,i3,i1,i74,i38,i38,i38,i38,i38,i60,i13,i29,i52,.push 2 4007,i35,i27,i2,i5,i6,i8,i6,i61,i43,i12,i8,i27,i2,i19,i1,i13,i40,i2,i19,i1,i3,i32,i1,i0,i34,i2,i19,i6,i3,i27,i2,i10,i6,i3,i24,i7,i6,i3,i20,i6,i61,i43,i16,i13,i34,i2,i10,i1,i3,i13,i27,i2,i22,i1,i3,i13,i4,i19,i1,i3,i13,i40,i2]

private theorem instructionsPart27_wf :
    instructionsPart27.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart27,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart28 : List Instr :=
  [i7,i1,i3,i13,i16,i32,i1,.push 2 3251,i44,i21,i31,i27,i31,i37,i3,i31,i5,i34,i29,i81,i53,i43,i60,i54,i27,i18,i0,i51,i29,i75,i21,i27,i38,i21,i21,i21,i21,i15,.op .MOD,i27,i54,i27,i18,i51,i27,i75,i21,i0,i36,i2,i24,i6,i3,i37,i2,i4,i6,i3,i39,i2,i12,i6,i3,i34,i2,i8,i6,i3,i11,i10,i6,i3,i20,i19,i6,i3,i13,i7,i6,i3,i8,i22,i6,i3,i16,i9,i36,i2,i4,i1,i3,i9,i37,i2,i12,i1,i3,i9,i39,i2,i8,i1,i3,i9,i34,i2,i13,i1,i3,i9,i9,i22,i1,i3,i9,i11,i10,i1,i3,i9,i20,i19,i1,i3,i9,i13,i25,i1]

private theorem instructionsPart28_wf :
    instructionsPart28.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart28,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart29 : List Instr :=
  [i3,i50,i38,i41,i2,i23,i0,i50,i29,i11,i3,i32,i9,i14,i1,i0,i36,i2,i4,i6,i3,i37,i2,i12,i6,i3,i39,i2,i8,i6,i3,i11,i19,i6,i3,i20,i7,i6,i3,i13,i22,i6,i3,i16,i9,i36,i2,i12,i1,i3,i9,i37,i2,i8,i1,i3,i9,i39,i2,i13,i1,i3,i9,i9,i10,i1,i3,i9,i11,i19,i1,i3,i9,i20,i25,i1,i3,i56,i38,i41,i2,i23,i0,i56,i29,i11,i3,i32,i9,i14,i1,i0,i36,i2,i12,i6,i3,i37,i2,i8,i6,i3,i11,i7,i6,i3,i20,i22,i6,i3,i16,i9,i36,i2,i8,i1,i3,i9,i37,i2,i13,i1,i3,i9,i9,i19,i1,i3]

private theorem instructionsPart29_wf :
    instructionsPart29.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart29,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart30 : List Instr :=
  [i9,i11,i25,i1,i3,i57,i38,i41,i2,i23,i0,i57,i29,i11,i3,i32,i9,i14,i1,i36,i2,i9,i5,i13,i1,.op (.Swap swap9),i38,i12,i6,i5,i3,i10,i9,i6,i3,i41,i2,i23,i74,i3,i11,i10,i9,i1,i3,i32,i9,i12,i5,i17,i29,i3,i1,i74,i38,i38,i38,i38,i38,i21,i24,i10,i54,.push 2 5148,i35,.push 1 255,i40,i2,i15,i29,i25,i5,i7,i43,i10,i29,i29,i4,i5,i19,i43,i25,i29,i29,i41,i2,i0,i15,i23,i28,i5,i23,i17,i23,i17,i43,i25,i29,i8,i16,i29,i0,.push 1 255,i43,i16,i41,i2,i23,i16,i4,i29,i20,i16,i29,i0,.push 1 255,i43,.push 2 5142,i35,i74,i38,i56,i38,i30,i38,i28,i38,i16]

private theorem instructionsPart30_wf :
    instructionsPart30.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart30,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart31 : List Instr :=
  [i38,.push 2 5058,i44,i21,i38,i38,i38,i38,i38,i21,i5,.push 1 240,i53,i5,i59,i37,i18,i15,i41,i53,i15,i61,i43,i59,i39,i18,i7,.push 1 208,i53,i7,i34,i43,i59,i34,i18,i19,i42,i53,i19,.push 1 48,i43,i59,i27,i18,i36,i27,i75,i21,i11,i13,i61,i53,i0,i42,i18,.push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,i0,.push 1 11,i43,.push 4 224,i18,i27,i2,i42,i43,i41,i2,i0,.push 1 36,i2,i15,i23,.push 1 66,i2,i7,i23,i37,i2,.push 1 6,i2,i10,i23,i30,i23,i40,i18,.push 2 352,i2,i7,i23,i27,i18,.push 2 322,i2,i7,i23,i34,i18,.push 2 292,i2,i7,i23,i39,i18,i16,i14,.push 2 262,i2,i23,i37,i18,.push 2 256,i2,i42,i43,i36,i18,i48,i2,i61,i43,i0,.push 1 200,i43,.push 5 1099511627775,.op .EQ,.push 1 207,i35]

private theorem instructionsPart31_wf :
    instructionsPart31.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart31,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart32 : List Instr :=
  [i41,i2,.push 2 2170,i2,i5,i23,.push 2 2200,i2,i15,i23,i85,i2,.push 1 176,i53,.push 2 2140,i2,i19,i23,i17,i23,.push 2 4007,i44,i21,i11,i22,i61,i43,.push 2 2368,i2,i61,i43,.push 1 134,i2,i15,i23,i41,i2,i7,i23,i0,i84,i18,i16,i14,i28,.push 1 194,i2,i5,i23,i0,i82,i18,i27,i2,i36,i43,i0,.push 2 1600,i18,.push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,.push 1 14,i2,i19,i23,i0,.push 2 1568,i18,.push 1 74,i2,i10,i23,.push 2 2546,i2,i22,i23,.push 2 2576,i2,i25,i23,.push 1 104,i2,i24,i23,.push 1 44,i2,i4,i23,.push 1 164,i2,i12,i23,.push 2 2592,i2,.push 1 112,i53,i8,i23,i47,i18,.push 2 2516,i2,i8,i23,i34,i18,.push 2 2486,i2,i8,i23,i39,i18,.push 2 2456,i2,i8,i23,i37,i18,.push 2 2426,i2,i8,i23,i36,i18,.push 2 2396,i2,i8,i23,i40]

private theorem instructionsPart32_wf :
    instructionsPart32.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart32,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart33 : List Instr :=
  [i18,i21,i67,i2,i76,i47,i2,i0,i12,i28,i5,i0,i6,i9,i6,i23,i52,i38,i15,i14,i1,i5,i8,i9,i1,i3,i32,i1,i47,i2,i0,i3,i0,i47,i18,i4,i5,i25,i1,i16,i22,i6,i15,i3,i8,i20,i6,i3,i14,i3,i4,i13,i13,i1,i3,i4,i11,i11,i15,i30,i6,.push 32 1766847064778384329583297500742918515827483896875618958121606201292619775,i23,i0,i52,i38,i1,i3,i32,i1,i47,i2,i15,i8,i6,i22,i0,i6,i8,i7,i12,i1,i28,i4,i6,i19,i3,i3,i3,i4,i20,i6,i3,i14,i3,i4,i22,i0,i0,i3,i57,i1,i3,i4,i7,i13,i1,i3,i4,i13,i12,i1,i3,i4,i11,i11,i15,i30,i6,.push 32 1766847064778384329583297500742918515827483896875618958121606201292619775,i23,i0,i42,i18,i1,i3,i32,i1]

private theorem instructionsPart33_wf :
    instructionsPart33.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart33,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart34 : List Instr :=
  [i34,i2,i4,i47,i2,i0,i7,i6,i4,i4,i6,i3,i28,i1,i12,i24,i24,i1,i3,i15,i3,i14,i3,i11,i8,i6,i3,i15,i4,i6,i3,i8,i42,i2,i6,i3,i16,i4,i9,i13,i1,i3,i4,i7,i12,i1,i3,i4,i13,i42,i2,i1,i3,i4,i11,i11,i15,i30,i6,i26,i23,i0,i27,i18,i1,i3,i32,i1,i39,i2,i4,i47,i2,i0,i7,i6,i34,i2,i4,i6,i3,i28,i1,i12,i34,i2,i24,i1,i3,i15,i3,i14,i3,i22,i0,i6,i3,i19,i8,i6,i3,i11,i4,i6,i3,i15,i42,i2,i6,i3,i8,i27,i2,i6,i3,i16,i4,i25,i0,i0,i3,i74,i1,i3,i4,i10,i13,i1]

private theorem instructionsPart34_wf :
    instructionsPart34.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart34,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart35 : List Instr :=
  [i3,i4,i9,i12,i1,i3,i4,i7,i42,i2,i1,i3,i4,i13,i27,i2,i1,i3,i4,i11,i11,i15,i30,i6,i26,i23,i0,i41,i18,i1,i3,i32,i1,i37,i2,i4,i47,i2,i0,i7,i6,i39,i2,i4,i6,i3,i34,i2,i12,i6,i3,i28,i1,i12,i39,i2,i24,i1,i3,i12,i34,i2,i4,i1,i3,i15,i3,i14,i3,i25,i8,i6,i3,i19,i4,i6,i3,i11,i42,i2,i6,i3,i15,i27,i2,i6,i3,i8,i41,i2,i6,i3,i16,i4,i24,i13,i1,i3,i4,i10,i12,i1,i3,i4,i9,i42,i2,i1,i3,i4,i7,i27,i2,i1,i3,i4,i13,i41,i2,i1,i3,i4,i11,i11,i15,i30,i6,i26]

private theorem instructionsPart35_wf :
    instructionsPart35.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart35,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart36 : List Instr :=
  [i23,i0,i49,i18,i1,i3,i32,i1,i36,i2,i4,i47,i2,i0,i7,i6,i37,i2,i4,i6,i3,i39,i2,i12,i6,i3,i28,i1,i12,i37,i2,i24,i1,i3,i12,i39,i2,i4,i1,i3,i15,i3,i14,i3,i34,i2,i0,i6,i3,i7,i8,i6,i3,i25,i4,i6,i3,i19,i42,i2,i6,i3,i11,i27,i2,i6,i3,i15,i41,i2,i6,i3,i8,i49,i2,i6,i3,i16,i4,i34,i2,i0,i0,i0,i3,i34,i18,i1,i3,i4,i19,i13,i1,i3,i4,i24,i12,i1,i3,i4,i10,i42,i2,i1,i3,i4,i9,i27,i2,i1,i3,i4,i7,i41,i2,i1,i3,i4,i13,i49,i2,i1,i3,i4,i11,i11,i15,i30]

private theorem instructionsPart36_wf :
    instructionsPart36.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart36,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart37 : List Instr :=
  [i6,i26,i23,i0,i62,i18,i1,i3,i32,i1,.push 2 1568,i2,i57,i40,i2,i12,i47,i2,i0,i7,i6,i4,i36,i2,i6,i3,i37,i2,i8,i6,i3,i39,i2,i34,i2,i6,i3,i28,i1,i8,i36,i2,i4,i1,i3,i8,i37,i2,i12,i1,i3,i8,i39,i2,i34,i2,i1,i3,i7,i3,i28,i3,i8,i12,i6,i3,i19,i15,i6,i3,i24,i42,i2,i6,i3,i10,i27,i2,i6,i3,i9,i41,i2,i6,i3,i7,i49,i2,i6,i3,i13,i62,i2,i6,i3,i14,i12,i13,i8,i1,i3,i12,i10,i7,i1,i3,i16,i77,i18,i4,i24,i42,i2,i1,i3,i4,i10,i27,i2,i1,i3,i4,i9,i41,i2,i1,i3,i4]

private theorem instructionsPart37_wf :
    instructionsPart37.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart37,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart38 : List Instr :=
  [i7,i49,i2,i1,i3,i4,i13,i62,i2,i1,i3,i4,i11,i11,i15,i30,i6,i26,i23,i0,i55,i18,i1,i3,i32,i1,i11,i4,i47,i2,i0,i7,i6,i24,i40,i2,i6,i3,i36,i2,i12,i6,i3,i37,i2,i34,i2,i6,i3,i28,i1,i12,i40,i2,i24,i1,i3,i12,i36,i2,i4,i1,i3,i12,i37,i2,i34,i2,i1,i3,i15,i3,i14,i3,i39,i2,i0,i6,i3,.push 2 1600,i2,i76,i8,i28,i8,i15,i10,i1,i3,i28,i6,i3,i77,i2,i4,i6,i3,i7,i42,i2,i6,i3,i25,i27,i2,i6,i3,i19,i41,i2,i6,i3,i11,i49,i2,i6,i3,i15,i62,i2,i6,i3,i8,i55,i2,i6,i3,i16]

private theorem instructionsPart38_wf :
    instructionsPart38.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart38,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart39 : List Instr :=
  [i4,i39,i2,i0,i0,i0,i3,i39,i18,i1,i3,i4,i77,i2,i12,i1,i3,i4,i19,i42,i2,i1,i3,i4,i24,i27,i2,i1,i3,i4,i10,i41,i2,i1,i3,i4,i9,i49,i2,i1,i3,i4,i7,i62,i2,i1,i3,i4,i13,i55,i2,i1,i3,i4,i26,i7,i5,i58,i6,i23,i0,i58,i1,i3,i32,i12,i28,i38,i1,i11,i4,i62,i2,i56,i0,i7,i6,i40,i2,i12,i6,i3,i36,i2,i34,i2,i6,i3,i37,i2,i39,i2,i6,i3,i28,i1,i12,i40,i2,i4,i1,i3,i12,i36,i2,i34,i2,i1,i3,i12,i37,i2,i39,i2,i1,i3,i15,i3,i14,i3,i77,i2,i8,i6,i3,i42,i2,i4]

private theorem instructionsPart39_wf :
    instructionsPart39.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart39,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart40 : List Instr :=
  [i6,i3,i7,i27,i2,i6,i3,i25,i41,i2,i6,i3,i19,i49,i2,i6,i3,i11,i22,i6,i3,i15,i55,i2,i6,i3,i8,i11,i6,i3,i16,i4,i77,i2,i13,i1,i3,i4,i42,i2,i12,i1,i3,i4,i19,i27,i2,i1,i3,i4,i24,i41,i2,i1,i3,i4,i10,i49,i2,i1,i3,i4,i9,i25,i1,i3,i4,i7,i55,i2,i1,i3,i4,i13,i9,i1,i3,i16,i13,i23,i0,i47,i18,i4,i14,i29,i5,i3,i32,i1,i11,i4,i49,i2,i55,i2,.op (.Swap swap13),i38,i57,i0,i7,i6,i40,i2,i34,i2,i6,i3,i36,i2,i39,i2,i6,i3,i28,i1,i12,i40,i2,i34,i2,i1,i3,i12,i36,i2,i39,i2]

private theorem instructionsPart40_wf :
    instructionsPart40.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart40,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart41 : List Instr :=
  [i1,i3,i15,i3,i14,i3,i37,i2,i0,i6,i3,i42,i2,i8,i6,i3,i27,i2,i4,i6,i3,i7,i41,i2,i6,i3,i25,i25,i6,i3,i19,i22,i6,i3,i8,i9,i6,i3,i15,i11,i6,i3,i16,i4,i37,i2,i0,i0,i0,i3,i37,i18,i1,i3,i4,i42,i2,i13,i1,i3,i4,i27,i2,i12,i1,i3,i4,i19,i41,i2,i1,i3,i4,i24,i24,i1,i3,i4,i10,i25,i1,i3,i4,i9,i20,i1,i3,i4,i7,i9,i1,i3,i16,i13,i23,i0,.push 2 800,i18,i4,i14,i29,i5,i3,i32,i1,i11,i16,i36,i2,i37,i2,i40,i2,i39,i2,i34,i2,i11,i25,i15,i1,i9,i7,i10,i1,i3,i9,i10]

private theorem instructionsPart41_wf :
    instructionsPart41.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart41,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart42 : List Instr :=
  [i25,i1,i3,i22,i3,i56,i6,i14,i6,i3,i14,i6,i3,i3,i27,i2,i8,i6,i3,i41,i2,i4,i6,i3,i7,i25,i6,i3,i25,i22,i6,i3,i8,i10,i6,i3,i11,i11,i6,i3,i16,i4,i27,i2,i13,i1,i3,i4,i41,i2,i12,i1,i3,i4,i19,i24,i1,i3,i4,i24,i25,i1,i3,i4,i10,i20,i1,i3,i4,i9,i9,i1,i3,i16,i13,i23,i0,.push 2 832,i18,i4,i14,i29,i5,i3,i32,i1,i11,i16,i40,i2,i37,i2,i39,i2,i13,i10,i15,i1,i20,i7,i10,i1,i3,i19,i3,i30,i6,i14,i6,i3,i3,i36,i2,i0,i6,i3,i41,i2,i8,i6,i3,i22,i4,i6,i3,i7,i22,i6]

private theorem instructionsPart42_wf :
    instructionsPart42.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart42,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart43 : List Instr :=
  [i3,i8,i24,i6,i3,i19,i11,i6,i3,i16,i4,i36,i2,i0,i1,i3,i4,i41,i2,i13,i1,i3,i4,i25,i12,i1,i3,i4,i19,i25,i1,i3,i4,i13,i4,i1,i3,i4,i10,i9,i1,i3,i16,i13,i23,i0,i34,i18,i4,i14,i29,i5,i3,i32,i1,i11,i16,i40,i2,i36,i2,i0,i3,i37,i2,i13,i10,i15,i1,i20,i7,i10,i1,i3,i19,i3,i30,i6,i14,i6,i3,i3,i22,i8,i6,i3,i10,i4,i6,i3,i8,i19,i6,i3,i25,i11,i6,i3,i16,i4,i25,i13,i1,i3,i4,i22,i12,i1,i3,i4,i19,i20,i1,i3,i4,i24,i9,i1,i3,i16,i13,i23,i0,i39,i18,i4,i14,i29]

private theorem instructionsPart43_wf :
    instructionsPart43.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart43,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart44 : List Instr :=
  [i5,i3,i32,i1,.push 2 832,i2,i50,i38,i11,i4,i36,i2,i0,i3,i0,i7,i6,i28,i1,i15,i3,i14,i3,i40,i2,i0,i6,i3,i10,i8,i6,i3,i8,i4,i6,i3,i7,i11,i6,i3,i16,i4,i40,i2,i0,i1,i3,i4,i22,i13,i1,i3,i4,i13,i12,i1,i3,i4,i11,i10,i1,i3,i16,i13,i23,i0,i37,i18,i4,i14,i29,i5,i3,i32,i1,.push 2 800,i2,i30,i38,i11,i40,i2,i0,i3,i12,i5,i7,i1,i14,i6,i15,i3,i8,i20,i6,i3,i4,i9,i6,i3,i14,i3,i4,i8,i20,i1,i3,i4,i11,i12,i1,i3,i16,i13,i23,i0,i36,i18,i4,i14,i29,i5,i3,i32,i1,.op (.Swap swap9),i38,i25]

private theorem instructionsPart44_wf :
    instructionsPart44.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart44,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart45 : List Instr :=
  [i4,i20,i1,i24,i9,i0,i1,i8,i3,i3,i4,i20,i6,i9,i0,i6,i82,i2,.op (.Swap swap12),i3,i3,i13,i23,i0,i40,i18,i4,i14,i29,i5,i3,i32,i1,.op (.Swap swap13),i38,.push 32 1344,i2,i52,i38,i60,i9,i29,.op (.Swap swap14),.push 2 5567,i35,i33,i2,i8,i23,i63,i18,.push 2 450,i2,i8,i23,i69,i18,.push 2 420,i2,i8,i23,i64,i18,.push 2 390,i2,i8,i23,i65,i18,.push 2 360,i2,i8,i23,i70,i18,.push 2 330,i2,i8,i23,i71,i18,.push 2 300,i2,i8,i23,i72,i18,.push 2 270,i2,i8,i23,i73,i18,.push 2 256,i2,i36,i43,i32,i18,i47,i2,i24,i63,i2,i0,i7,i6,i67,i2,i6,i11,i23,i52,i38,i12,i28,i1,i5,i8,i9,i1,i3,i32,i1,i0,i4,i47,i2]

private theorem instructionsPart45_wf :
    instructionsPart45.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart45,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart46 : List Instr :=
  [i69,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i8,i20,i6,i63,i2,i17,i3,i7,i24,i6,i3,i28,i25,i1,i3,i4,i8,i20,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0,i52,i38,i1,i3,i32,i1,i69,i2,i47,i2,i64,i2,i8,i5,i7,i1,i14,i6,i7,i3,i8,i7,i4,i1,i28,i24,i6,i3,i28,i3,i3,i4,i25,i63,i2,i17,i5,i10,i6,i3,i10,i11,i6,i3,i8,i9,i6,i3,i17,i1,i3,i4,i7,i13,i1,i3,i4,i4,i20,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0,i42,i18,i1,i3,i32,i1,i64,i2,i47,i2,i65,i2,i8,i5,i7,i1]

private theorem instructionsPart46_wf :
    instructionsPart46.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart46,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart47 : List Instr :=
  [i14,i6,i7,i3,i8,i7,i4,i1,i28,i24,i6,i3,i28,i3,i3,i34,i2,i69,i2,i8,i5,i12,i1,i63,i2,i20,i5,i10,i1,i28,i8,i6,i17,i6,i17,i3,i3,i28,i3,i3,i11,i8,i6,i3,i15,i4,i6,i3,i8,i42,i2,i6,i3,i16,i4,i9,i13,i1,i3,i4,i7,i12,i1,i3,i4,i13,i42,i2,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0,i27,i18,i1,i3,i32,i1,i65,i2,i47,i2,i70,i2,i8,i5,i7,i1,i14,i6,i7,i3,i8,i7,i4,i1,i28,i24,i6,i3,i28,i3,i3,i4,i25,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i34,i2,i69]

private theorem instructionsPart47_wf :
    instructionsPart47.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart47,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart48 : List Instr :=
  [i2,i13,i5,i7,i1,i14,i6,i63,i2,i30,i3,i28,i3,i8,i15,i10,i1,i3,i28,i6,i3,i19,i8,i6,i3,i11,i4,i6,i3,i15,i42,i2,i6,i3,i8,i27,i2,i6,i3,i16,i4,i10,i13,i1,i3,i4,i9,i12,i1,i3,i4,i7,i42,i2,i1,i3,i4,i13,i27,i2,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0,i41,i18,i1,i3,i32,i1,i70,i2,i47,i2,i71,i2,i8,i5,i7,i1,i14,i6,i7,i3,i8,i7,i4,i1,i28,i24,i6,i3,i28,i3,i3,i4,i25,i65,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i34,i2,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3]

private theorem instructionsPart48_wf :
    instructionsPart48.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart48,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart49 : List Instr :=
  [i37,i2,i39,i2,i69,i2,i13,i5,i7,i1,i14,i6,i63,i2,i30,i3,i28,i3,i8,i15,i10,i1,i3,i28,i6,i3,i25,i8,i6,i3,i19,i4,i6,i3,i11,i42,i2,i6,i3,i15,i27,i2,i6,i3,i8,i41,i2,i6,i3,i16,i4,i24,i13,i1,i3,i4,i10,i12,i1,i3,i4,i9,i42,i2,i1,i3,i4,i7,i27,i2,i1,i3,i4,i13,i41,i2,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0,i49,i18,i1,i3,i32,i1,i71,i2,i47,i2,i72,i2,i8,i5,i7,i1,i14,i6,i7,i3,i8,i7,i4,i1,i28,i24,i6,i3,i28,i3,i3,i4,i25,i70,i2,i17,i5,i10,i6,i3]

private theorem instructionsPart49_wf :
    instructionsPart49.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart49,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart50 : List Instr :=
  [i17,i1,i3,i4,i34,i2,i65,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i39,i2,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i36,i2,i37,i2,i69,i2,i13,i5,i7,i1,i14,i6,i63,i2,i30,i3,i28,i3,i8,i15,i10,i1,i3,i28,i6,i3,i7,i8,i6,i3,i25,i4,i6,i3,i19,i42,i2,i6,i3,i11,i27,i2,i6,i3,i15,i41,i2,i6,i3,i8,i49,i2,i6,i3,i16,i4,i19,i13,i1,i3,i4,i24,i12,i1,i3,i4,i10,i42,i2,i1,i3,i4,i9,i27,i2,i1,i3,i4,i7,i41,i2,i1,i3,i4,i13,i49,i2,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0]

private theorem instructionsPart50_wf :
    instructionsPart50.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart50,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart51 : List Instr :=
  [i62,i18,i1,i3,i32,i1,.push 2 1568,i2,i57,i5,i12,i47,i2,i73,i2,i30,i5,i22,i6,i3,i30,i1,i3,i12,i25,i72,i2,i30,i5,i22,i6,i3,i30,i1,i3,i12,i24,i71,i2,i30,i5,i22,i6,i3,i30,i1,i3,i12,i34,i2,i70,i2,i30,i5,i22,i6,i3,i30,i1,i3,i12,i39,i2,i65,i2,i30,i5,i22,i6,i3,i30,i1,i3,i12,i37,i2,i64,i2,i30,i5,i22,i6,i3,i30,i1,i3,i40,i2,i36,i2,i69,i2,i20,i5,i7,i1,i14,i6,i63,i2,i50,i3,i28,i3,i13,i15,i22,i1,i3,i17,i6,i3,i8,i12,i6,i3,i19,i15,i6,i3,i24,i42,i2,i6,i3,i10,i27,i2]

private theorem instructionsPart51_wf :
    instructionsPart51.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart51,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart52 : List Instr :=
  [i6,i3,i9,i41,i2,i6,i3,i7,i49,i2,i6,i3,i13,i62,i2,i6,i3,i14,i12,i13,i8,i1,i3,i12,i10,i7,i1,i3,i16,i77,i18,i4,i24,i42,i2,i1,i3,i4,i10,i27,i2,i1,i3,i4,i9,i41,i2,i1,i3,i4,i7,i49,i2,i1,i3,i4,i13,i62,i2,i1,i3,i4,i11,i67,i2,i15,i30,i6,i9,i23,i0,i55,i18,i1,i3,i32,i1,i73,i2,i47,i2,i32,i2,i8,i5,i7,i1,i14,i6,i7,i3,i8,i7,i4,i1,i28,i24,i6,i3,i28,i3,i3,i14,.op (.Swap swap14),i14,i4,i25,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i34,i2,i71,i2,i17,i5,i10,i6,i3,i17]

private theorem instructionsPart52_wf :
    instructionsPart52.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart52,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart53 : List Instr :=
  [i1,i3,i4,i39,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i65,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i36,i2,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i40,i2,i69,i2,i8,i5,i7,i1,i14,i6,i63,i2,i17,i3,i14,i3,i12,i7,i10,i1,i3,i14,i7,i6,i3,.push 2 1600,i2,i76,i8,i28,i8,i15,i10,i1,i3,i28,i6,i3,i77,i2,i4,i6,i3,i42,i2,i19,i6,i3,i27,i2,i24,i6,i3,i41,i2,i10,i6,i3,i49,i2,i9,i6,i3,i9,i62,i2,i6,i3,i55,i2,i13,i6,i3,i16,i4,i77,i2,i12,i1,i3,i4,i42,i2,i10,i1,i3,i4]

private theorem instructionsPart53_wf :
    instructionsPart53.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart53,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart54 : List Instr :=
  [i27,i2,i4,i1,i3,i4,i41,i2,i22,i1,i3,i4,i9,i49,i2,i1,i3,i9,i12,i16,i62,i2,i1,i3,i4,i55,i2,i20,i1,i3,i4,i20,i67,i2,i15,i30,i6,i23,.op (.Swap swap14),i9,i1,i3,i32,i1,i32,i2,i4,i5,i25,i1,i15,i3,i50,i6,i3,i62,i2,i30,i4,i25,i73,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i34,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i39,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i36,i2,i65,i2,i17,i5,i10,i6,i3,i17,i1,i3,i40,i2,i64,i2,i8,i5]

private theorem instructionsPart54_wf :
    instructionsPart54.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart54,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart55 : List Instr :=
  [i7,i1,i14,i6,i69,i2,i17,i3,i14,i3,i12,i7,i10,i1,i3,i14,i7,i6,i3,i77,i2,i8,i6,i3,i42,i2,i4,i6,i3,i27,i2,i19,i6,i3,i41,i2,i24,i6,i3,i49,i2,i10,i6,i3,i10,i9,i6,i3,i9,i55,i2,i6,i3,i20,i13,i6,i3,i16,i4,i77,i2,i13,i1,i3,i4,i42,i2,i12,i1,i3,i4,i27,i2,i10,i1,i3,i4,i41,i2,i4,i1,i3,i4,i49,i2,i22,i1,i3,i4,i9,i25,i1,i3,i9,i12,i16,i55,i2,i1,i3,i4,i11,i20,i1,i3,i16,i13,i23,i0,i47,i18,i4,i14,i29,i5,i3,i32,i1,i55,i2,i76,i38,i32,i2,i5,i12,i15,i4]

private theorem instructionsPart55_wf :
    instructionsPart55.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart55,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart56 : List Instr :=
  [i1,i3,i56,i6,i3,i49,i2,i50,i4,i34,i2,i73,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i39,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i36,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i40,i2,i65,i2,i8,i5,i7,i1,i14,i6,i64,i2,i17,i3,i14,i3,i12,i7,i10,i1,i3,i14,i7,i6,i3,i42,i2,i8,i6,i3,i27,i2,i4,i6,i3,i41,i2,i19,i6,i3,i22,i24,i6,i3,i10,i10,i6,i3,i8,i9,i6,i3,i9,i11,i6,i3,i16,i4,i42,i2,i13,i1,i3,i4,i27,i2,i12,i1]

private theorem instructionsPart56_wf :
    instructionsPart56.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart56,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart57 : List Instr :=
  [i3,i4,i41,i2,i10,i1,i3,i4,i25,i4,i1,i3,i4,i22,i22,i1,i3,i4,i9,i20,i1,i3,i9,i12,i16,i9,i1,i3,i16,i13,i23,i0,i14,i29,i4,i3,i32,i12,i14,i1,i4,i34,i2,i15,i32,i2,i30,.push 2 800,i18,i5,i10,i6,i3,i17,i1,i3,i4,i39,i2,i73,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i36,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i40,i2,i70,i2,i8,i5,i7,i1,i14,i6,i65,i2,i17,i3,i14,i3,i12,i7,i10,i1,i3,i14,i7,i6,i3,i27,i2,i8,i6,i3,i41,i2,i4]

private theorem instructionsPart57_wf :
    instructionsPart57.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart57,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart58 : List Instr :=
  [i6,i3,i22,i19,i6,i3,i10,i24,i6,i3,i8,i10,i6,i3,i20,i9,i6,i3,i16,i4,i27,i2,i13,i1,i3,i4,i41,i2,i12,i1,i3,i4,i25,i10,i1,i3,i4,i22,i4,i1,i3,i4,i13,i22,i1,i3,i4,i9,i9,i1,i3,i16,i13,i23,i0,i14,i29,i4,i3,i32,i12,i14,i1,i4,i39,i2,i15,i32,i2,i30,.push 2 832,i18,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i73,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i36,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i40,i2,i71,i2,i8,i5,i7,i1,i14,i6,i70,i2,i17,i3,i14,i3,i12,i7,i10,i1,i3,i14,i7]

private theorem instructionsPart58_wf :
    instructionsPart58.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart58,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart59 : List Instr :=
  [i6,i3,i41,i2,i8,i6,i3,i22,i4,i6,i3,i10,i19,i6,i3,i8,i24,i6,i3,i20,i10,i6,i3,i16,i4,i41,i2,i13,i1,i3,i4,i25,i12,i1,i3,i4,i22,i10,i1,i3,i4,i13,i4,i1,i3,i4,i11,i22,i1,i3,i16,i13,i23,i0,i14,i29,i4,i3,i32,i12,i14,i1,i4,i37,i2,i15,i32,i2,i30,i34,i18,i5,i10,i6,i3,i17,i1,i3,i4,i36,i2,i73,i2,i17,i5,i10,i6,i3,i17,i1,i3,i40,i2,i72,i2,i8,i5,i7,i1,i14,i6,i71,i2,i17,i3,i14,i3,i12,i7,i10,i1,i3,i14,i7,i6,i3,i22,i8,i6,i3,i10,i4,i6,i3,i8,i19,i6,i3]

private theorem instructionsPart59_wf :
    instructionsPart59.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart59,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart60 : List Instr :=
  [i20,i24,i6,i3,i16,i4,i25,i13,i1,i3,i4,i22,i12,i1,i3,i4,i13,i10,i1,i3,i4,i11,i4,i1,i3,i16,i13,i23,i0,i39,i18,i4,i14,i29,i5,i3,i32,i1,i36,i2,i40,i2,i73,i2,i8,i5,i7,i1,i74,i38,i6,i32,i2,i8,i5,i19,i1,i28,i6,i7,i3,i3,i14,i3,.push 2 832,i2,i56,i3,i4,i7,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i16,i10,i8,i6,i3,i8,i4,i6,i3,i20,i19,i6,i3,i16,i4,i22,i13,i1,i3,i4,i13,i12,i1,i3,i4,i11,i10,i1,i3,i16,i13,i23,i0,i37,i18,i4,i14,i29,i5,i3,i32,i1,i32,i2,i40,i2,i12,i5]

private theorem instructionsPart60_wf :
    instructionsPart60.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart60,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart61 : List Instr :=
  [i7,i1,i56,i38,i6,i73,i2,i50,i15,i3,i12,i19,i24,i1,i3,i14,i3,.push 2 800,i2,i50,i7,i6,i3,i8,i8,i6,i3,i20,i4,i6,i3,i16,i4,i13,i13,i1,i3,i4,i11,i12,i1,i3,i16,i13,i23,i0,i36,i18,i4,i14,i29,i5,i3,i32,i1,i32,i2,i4,i5,i19,i1,i12,i9,i20,i1,i14,i19,i6,i7,i3,i9,i20,i6,i3,i11,i23,i28,i3,i3,i5,i40,i18,i29,i24,i3,i32,i4,i28,i38,i1,.op (.Swap swap12),i24,i11,i54,i68,i35,i24,i11,i46,i79,i35,i22,i40,i2,i54,i68,i35,i22,i40,i2,i46,i79,i35,i5,i36,i2,i54,i68,i35,i5,i36,i2,i46,i79,i35,i10,i37,i2]

private theorem instructionsPart61_wf :
    instructionsPart61.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart61,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart62 : List Instr :=
  [i54,i68,i35,i10,i37,i2,i46,i79,i35,i15,i39,i2,i54,i68,i35,i15,i39,i2,i46,i79,i35,i13,i34,i2,i54,i68,i35,i13,i34,i2,i46,i79,i35,i0,i10,i54,i68,i35,i0,i10,i46,i79,i35,i82,i2,i19,i54,i68,i35,i82,i2,i19,i46,i79,i35,i84,i2,i47,i2,i54,i68,i35,i84,i2,i47,i2,i46,i38,i21,i68,i52,i38,.push 2 10490,i44,i21,i47,i2,i19,.push 1 240,i53,i59,.push 2 2336,i18,i7,i61,i43,i10,i41,i53,i59,.push 2 2304,i18,i19,i34,i43,i34,i2,.push 1 208,i53,i59,.push 2 2272,i18,i34,i2,.push 1 48,i43,i39,i2,i42,i53,i59,.push 2 2240,i18,i39,i2,i39,i43,i37,i2,.push 1 176,i53,i59,i85,i18,i37,i2,.push 1 80,i43]

private theorem instructionsPart62_wf :
    instructionsPart62.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart62,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart63 : List Instr :=
  [i36,i2,i40,i53,i59,.push 2 2176,i18,i36,i2,i37,i43,i40,i2,.push 1 144,i53,i59,.push 2 2144,i18,i40,i2,.push 1 112,i43,i11,i36,i53,i59,i48,i18,.push 2 256,i48,i75,i21,.push 2 7627,i52,i38,i21,i47,i2,i84,i2,i0,i15,i54,i14,i29,i13,i23,i47,i18,i82,i2,i3,i0,i10,i29,i13,i23,i30,i54,i5,i3,i0,i22,i29,i13,i23,i50,i54,i20,i3,i34,i2,i5,i5,i29,i20,i23,i34,i18,i54,i7,i3,i39,i2,i5,i5,i29,i20,i23,i39,i18,i54,i22,i3,i37,i2,i5,i5,i29,i20,i23,i37,i18,i54,i15,i3,i36,i2,i5,i5,i29,i20,i23,i36,i18,i54,i25,i3,i40,i2,i5,i5,i29,i20,i23,i40,i18,i54]

private theorem instructionsPart63_wf :
    instructionsPart63.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart63,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart64 : List Instr :=
  [i4,i3,i84,.op (.Swap swap14),i29,.op (.Swap swap13),i2,i52,i44,i21,i0,.push 32 21888242871839275222246405745257275088696311157297823662689037894645226208583,.op .EQ,i5,.push 32 115792089237316195423570985008687907853269984665640564039457584007908834671663,.op .EQ,i59,.push 2 4748,i35,.push 2 717,i44,i21,i9,i48,i66,i83,i66,i2,i0,i11,i43,i16,.push 2 1600,i2,i53,i48,i2,i9,i43,i3,i20,i0,i20,i19,i1,i15,.op .ADDMOD,i16,i29,i13,i6,i9,i5,i36,i43,i6,i5,i27,i2,i6,i48,i2,i29,i54,i16,i29,i45,i14,i11,i46,i15,i3,i59,i0,i25,i6,i15,i24,i7,i1,i5,i85,i18,i0,i15,i46,i16,i29,i29,i5,i25,i6,i7,i24,i19,i1,i0,i15,i46,i29,i5,i7,i3,.push 2 2176,i2,i5,i3,i0,.push 2 2176,i18,i5,i46,i17,i46,i29,i29,i3,i5,i22,i6,i7,i25,i19,i1,i0,i15,i46,i29]

private theorem instructionsPart64_wf :
    instructionsPart64.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart64,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart65 : List Instr :=
  [i5,i7,i3,.push 2 2144,i2,i5,i3,i0,.push 2 2144,i18,i5,i46,i17,i46,i29,i29,i3,i55,i2,i7,i7,i15,i6,i14,i19,i1,i0,i15,i46,i29,i5,i7,i3,i48,i2,i5,i3,i0,i48,i18,i5,i46,i17,i46,i29,i29,i3,i66,i2,i3,i29,i0,i66,i18,.push 31 3069,i35,i3,i0,i15,i35,i58,.push 6 10971,i35,i58,i11,i11,i14,i44,.push 1 0,i21,i58,i38,.push 4 2298,i58,i11,i48,.push 2 256,i83,i20,.push 1 2,i43,i5,i44]

private theorem instructionsPart65_wf :
    instructionsPart65.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart65,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart66 : List Instr :=
  []

private theorem instructionsPart66_wf :
    instructionsPart66.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  rfl

private def instructionsPart67 : List Instr :=
  []

private theorem instructionsPart67_wf :
    instructionsPart67.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  rfl

def instructions : List Instr :=
  instructionsPart0 ++ (instructionsPart1 ++ (instructionsPart2 ++ (instructionsPart3 ++ (instructionsPart4 ++ (instructionsPart5 ++ (instructionsPart6 ++ (instructionsPart7 ++ (instructionsPart8 ++ (instructionsPart9 ++ (instructionsPart10 ++ (instructionsPart11 ++ (instructionsPart12 ++ (instructionsPart13 ++ (instructionsPart14 ++ (instructionsPart15 ++ (instructionsPart16 ++ (instructionsPart17 ++ (instructionsPart18 ++ (instructionsPart19 ++ (instructionsPart20 ++ (instructionsPart21 ++ (instructionsPart22 ++ (instructionsPart23 ++ (instructionsPart24 ++ (instructionsPart25 ++ (instructionsPart26 ++ (instructionsPart27 ++ (instructionsPart28 ++ (instructionsPart29 ++ (instructionsPart30 ++ (instructionsPart31 ++ (instructionsPart32 ++ (instructionsPart33 ++ (instructionsPart34 ++ (instructionsPart35 ++ (instructionsPart36 ++ (instructionsPart37 ++ (instructionsPart38 ++ (instructionsPart39 ++ (instructionsPart40 ++ (instructionsPart41 ++ (instructionsPart42 ++ (instructionsPart43 ++ (instructionsPart44 ++ (instructionsPart45 ++ (instructionsPart46 ++ (instructionsPart47 ++ (instructionsPart48 ++ (instructionsPart49 ++ (instructionsPart50 ++ (instructionsPart51 ++ (instructionsPart52 ++ (instructionsPart53 ++ (instructionsPart54 ++ (instructionsPart55 ++ (instructionsPart56 ++ (instructionsPart57 ++ (instructionsPart58 ++ (instructionsPart59 ++ (instructionsPart60 ++ (instructionsPart61 ++ (instructionsPart62 ++ (instructionsPart63 ++ (instructionsPart64 ++ (instructionsPart65 ++ (instructionsPart66 ++ (instructionsPart67)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Lookup shares the existing instruction chunks; finite sizes are checked. -/
def instructionTree : CycleSubmission.InstructionLookup.Table Instr :=
  .node 4352 (.node 2176 (.node 1024 (.node 512 (.node 256 (.node 128 (.leaf instructionsPart0) (.leaf instructionsPart1)) (.node 128 (.leaf instructionsPart2) (.leaf instructionsPart3))) (.node 256 (.node 128 (.leaf instructionsPart4) (.leaf instructionsPart5)) (.node 128 (.leaf instructionsPart6) (.leaf instructionsPart7)))) (.node 512 (.node 256 (.node 128 (.leaf instructionsPart8) (.leaf instructionsPart9)) (.node 128 (.leaf instructionsPart10) (.leaf instructionsPart11))) (.node 256 (.node 128 (.leaf instructionsPart12) (.leaf instructionsPart13)) (.node 128 (.leaf instructionsPart14) (.node 128 (.leaf instructionsPart15) (.leaf instructionsPart16)))))) (.node 1024 (.node 512 (.node 256 (.node 128 (.leaf instructionsPart17) (.leaf instructionsPart18)) (.node 128 (.leaf instructionsPart19) (.leaf instructionsPart20))) (.node 256 (.node 128 (.leaf instructionsPart21) (.leaf instructionsPart22)) (.node 128 (.leaf instructionsPart23) (.leaf instructionsPart24)))) (.node 512 (.node 256 (.node 128 (.leaf instructionsPart25) (.leaf instructionsPart26)) (.node 128 (.leaf instructionsPart27) (.leaf instructionsPart28))) (.node 256 (.node 128 (.leaf instructionsPart29) (.leaf instructionsPart30)) (.node 128 (.leaf instructionsPart31) (.node 128 (.leaf instructionsPart32) (.leaf instructionsPart33))))))) (.node 2176 (.node 1024 (.node 512 (.node 256 (.node 128 (.leaf instructionsPart34) (.leaf instructionsPart35)) (.node 128 (.leaf instructionsPart36) (.leaf instructionsPart37))) (.node 256 (.node 128 (.leaf instructionsPart38) (.leaf instructionsPart39)) (.node 128 (.leaf instructionsPart40) (.leaf instructionsPart41)))) (.node 512 (.node 256 (.node 128 (.leaf instructionsPart42) (.leaf instructionsPart43)) (.node 128 (.leaf instructionsPart44) (.leaf instructionsPart45))) (.node 256 (.node 128 (.leaf instructionsPart46) (.leaf instructionsPart47)) (.node 128 (.leaf instructionsPart48) (.node 128 (.leaf instructionsPart49) (.leaf instructionsPart50)))))) (.node 1024 (.node 512 (.node 256 (.node 128 (.leaf instructionsPart51) (.leaf instructionsPart52)) (.node 128 (.leaf instructionsPart53) (.leaf instructionsPart54))) (.node 256 (.node 128 (.leaf instructionsPart55) (.leaf instructionsPart56)) (.node 128 (.leaf instructionsPart57) (.leaf instructionsPart58)))) (.node 512 (.node 256 (.node 128 (.leaf instructionsPart59) (.leaf instructionsPart60)) (.node 128 (.leaf instructionsPart61) (.leaf instructionsPart62))) (.node 256 (.node 128 (.leaf instructionsPart63) (.leaf instructionsPart64)) (.node 83 (.leaf instructionsPart65) (.node 0 (.leaf instructionsPart66) (.leaf instructionsPart67)))))))
theorem instructionTree_valid : instructionTree.valid = true := by decide
theorem instructionTree_flatten : instructionTree.flatten = instructions := by
  simp only [instructionTree, CycleSubmission.InstructionLookup.Table.flatten, instructions, List.append_assoc]
theorem instruction_get (i : Nat) : instructions[i]? = instructionTree.get? i := by
  rw [← instructionTree_flatten]
  exact (CycleSubmission.InstructionLookup.Table.get?_eq instructionTree instructionTree_valid i).symm

theorem instructionCount : instructions.length = 8403 := by decide
theorem assembly : assemble instructions = bytecode := by rfl
def artifact : ProgramArtifact where
  code := bytecode
  instructions := instructions
  assembly_eq := assembly
theorem wellFormed : AllWellFormed artifact .Osaka := by
  unfold AllWellFormed artifact instructions
  simp only [List.all_append,instructionsPart0_wf,instructionsPart1_wf,instructionsPart2_wf,instructionsPart3_wf,instructionsPart4_wf,instructionsPart5_wf,instructionsPart6_wf,instructionsPart7_wf,instructionsPart8_wf,instructionsPart9_wf,instructionsPart10_wf,instructionsPart11_wf,instructionsPart12_wf,instructionsPart13_wf,instructionsPart14_wf,instructionsPart15_wf,instructionsPart16_wf,instructionsPart17_wf,instructionsPart18_wf,instructionsPart19_wf,instructionsPart20_wf,instructionsPart21_wf,instructionsPart22_wf,instructionsPart23_wf,instructionsPart24_wf,instructionsPart25_wf,instructionsPart26_wf,instructionsPart27_wf,instructionsPart28_wf,instructionsPart29_wf,instructionsPart30_wf,instructionsPart31_wf,instructionsPart32_wf,instructionsPart33_wf,instructionsPart34_wf,instructionsPart35_wf,instructionsPart36_wf,instructionsPart37_wf,instructionsPart38_wf,instructionsPart39_wf,instructionsPart40_wf,instructionsPart41_wf,instructionsPart42_wf,instructionsPart43_wf,instructionsPart44_wf,instructionsPart45_wf,instructionsPart46_wf,instructionsPart47_wf,instructionsPart48_wf,instructionsPart49_wf,instructionsPart50_wf,instructionsPart51_wf,instructionsPart52_wf,instructionsPart53_wf,instructionsPart54_wf,instructionsPart55_wf,instructionsPart56_wf,instructionsPart57_wf,instructionsPart58_wf,instructionsPart59_wf,instructionsPart60_wf,instructionsPart61_wf,instructionsPart62_wf,instructionsPart63_wf,instructionsPart64_wf,instructionsPart65_wf,instructionsPart66_wf,instructionsPart67_wf,Bool.and_self]
theorem bytecodeSize : bytecode.size = 10994 := by
  simp only [bytecode,ByteArray.size_append]
  decide
end CycleSubmission.Artifact
