import Challenge.Modexp.Submission.Proofs.Cycle.ChunkLookup
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
private abbrev i14 : Instr := .op (.Dup dup2)
private abbrev i15 : Instr := .op (.Swap swap1)
private abbrev i16 : Instr := .op (.Swap swap0)
private abbrev i17 : Instr := .op (.Swap swap3)
private abbrev i18 : Instr := .op (.Dup dup4)
private abbrev i19 : Instr := .op .MSTORE
private abbrev i20 : Instr := .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775
private abbrev i21 : Instr := .op (.Dup dup13)
private abbrev i22 : Instr := .push 0 0
private abbrev i23 : Instr := .op .JUMPDEST
private abbrev i24 : Instr := .op (.Dup dup6)
private abbrev i25 : Instr := .op (.Dup dup8)
private abbrev i26 : Instr := .op .AND
private abbrev i27 : Instr := .op (.Dup dup7)
private abbrev i28 : Instr := .op (.Swap swap2)
private abbrev i29 : Instr := .op .SUB
private abbrev i30 : Instr := .op (.Swap swap4)
private abbrev i31 : Instr := .op .CALLDATALOAD
private abbrev i32 : Instr := .push 2 2048
private abbrev i33 : Instr := .push 2 480
private abbrev i34 : Instr := .push 1 32
private abbrev i35 : Instr := .push 1 128
private abbrev i36 : Instr := .op .JUMPI
private abbrev i37 : Instr := .push 1 96
private abbrev i38 : Instr := .push 1 64
private abbrev i39 : Instr := .push 1 160
private abbrev i40 : Instr := .op .POP
private abbrev i41 : Instr := .push 1 224
private abbrev i42 : Instr := .push 1 192
private abbrev i43 : Instr := .op .SHR
private abbrev i44 : Instr := .op .JUMP
private abbrev i45 : Instr := .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935
private abbrev i46 : Instr := .push 2 2112
private abbrev i47 : Instr := .op .GT
private abbrev i48 : Instr := .push 2 768
private abbrev i49 : Instr := .op (.Swap swap11)
private abbrev i50 : Instr := .push 2 1216
private abbrev i51 : Instr := .op .LT
private abbrev i52 : Instr := .op (.Swap swap5)
private abbrev i53 : Instr := .op .MSIZE
private abbrev i54 : Instr := .op .SHL
private abbrev i55 : Instr := .push 2 2080
private abbrev i56 : Instr := .push 2 1280
private abbrev i57 : Instr := .push 1 1
private abbrev i58 : Instr := .op (.Swap swap6)
private abbrev i59 : Instr := .op (.Swap swap7)
private abbrev i60 : Instr := .op .OR
private abbrev i61 : Instr := .push 1 16
private abbrev i62 : Instr := .push 2 1248
private abbrev i63 : Instr := .push 2 1792
private abbrev i64 : Instr := .push 2 1888
private abbrev i65 : Instr := .push 2 2720
private abbrev i66 : Instr := .push 2 10399
private abbrev i67 : Instr := .push 2 1824
private abbrev i68 : Instr := .push 2 1856
private abbrev i69 : Instr := .push 2 1920
private abbrev i70 : Instr := .push 2 1952
private abbrev i71 : Instr := .push 2 1984
private abbrev i72 : Instr := .push 2 2016
private abbrev i73 : Instr := .op (.Swap swap8)
private abbrev i74 : Instr := .op .RETURN
private abbrev i75 : Instr := .op (.Swap swap10)
private abbrev i76 : Instr := .push 2 1088
private abbrev i77 : Instr := .op .CALLDATACOPY
private abbrev i78 : Instr := .op .MCOPY
private abbrev i79 : Instr := .op .ISZERO
private abbrev i80 : Instr := .push 2 10389
private abbrev i81 : Instr := .op (.Swap swap13)
private abbrev i82 : Instr := .op (.Swap swap14)
private abbrev i83 : Instr := .op .NOT
private abbrev i84 : Instr := .push 1 3
private abbrev i85 : Instr := .push 2 1376
private abbrev i86 : Instr := .push 2 256
private abbrev i87 : Instr := .push 2 1344
private abbrev i88 : Instr := .push 2 2208

private def instructionsPart0 : List Instr :=
  [.push 1 34,i31,i38,i31,i3,.push 3 2097184,.op .XOR,.push 2 564,i36,i37,i31,i35,i31,i39,i31,i5,i5,i29,.push 2 8191,i57,i31,i29,i43,.push 2 717,i36,i22,i31,i34,.op .XOR,.push 1 97,i36,i23,i5,i83,i5,i3,.push 2 717,i36,.push 2 10659,i44,.push 32 26689440342447178617115869845918039756797228267049433585260346420242739014315,i22,i23,i23,i23,i34,i22,i31,i5,i5,i47,.push 1 207,i36,i16,i29,i37,i31,i5,i84,i54,i43,i5,i35,i29,i31,i14,i39,i29,i31,.push 1 48,i44,i23,i10,i31,i7,i34,i29,i84,i54,i43,i0,.push 1 149,i36,i7,i22,i74,i23,i22,i22,i23,i7,i5,.op .EQ,.push 1 180,i36,i14,i5,i25,i3,i31,i22,.op .BYTE,i18,i86,i57,i52,i1,.op .ADDMOD,i15,i3,.push 1 152,i44,i23,i40,i5,i22,i79,i51,i22,i23,i10,i5,.op .EQ,.push 2 3993,i36,i0,i4,i3]

private theorem instructionsPart0_wf :
    instructionsPart0.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart0,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart1 : List Instr :=
  [i0,i31,i22,.op .BYTE,i22,.push 2 4009,i44,i23,.push 2 9248,.op .CALLDATASIZE,i22,i77,i38,i31,i34,i31,i22,i31,i14,i5,i7,i3,i37,i3,.push 2 1024,i77,i0,i37,.push 2 5120,i77,i22,i7,i23,i22,i83,i3,i0,.push 2 1024,i3,i2,i5,i28,i60,i15,.push 1 242,i36,i40,.push 2 268,i36,i23,i14,i22,i74,i23,i57,i7,.push 2 3071,i3,.op .MSTORE8,i40,i22,i23,i5,i84,i54,i5,.op .EQ,.push 2 363,i36,i14,.push 2 3072,i0,.push 2 302,.push 2 380,i44,i23,i14,i22,.push 2 3072,i78,i0,i84,i43,i22,i31,i3,i37,i3,i31,i5,.push 1 7,i26,i54,.push 1 255,i43,i79,.push 2 355,i36,i22,i31,.push 2 5120,.push 2 3072,.push 2 348,.push 2 380,i44,i23,i14,i22,.push 2 3072,i78,i23,i57,i3,.push 2 279,i44,i23,i14,.push 2 3072,i22,i78,.push 2 8192,.push 2 264,.push 2 451,i44,i23,i38,i31,.op .CALLDATASIZE]

private theorem instructionsPart1_wf :
    instructionsPart1.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart1,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart2 : List Instr :=
  [i22,i77,i22,i23,i18,i84,i54,i5,.op .EQ,.push 2 444,i36,i22,.push 2 407,.push 2 451,i44,i23,i0,i84,i43,i18,i3,i2,i5,.push 1 7,i26,i54,.push 1 255,i43,i79,.push 2 436,i36,i14,.push 2 436,.push 2 451,i44,i23,i57,i3,.push 2 388,i44,i23,i40,i28,i40,i40,i40,i44,i23,.push 2 1024,i23,i57,i38,i31,i23,i22,i83,i3,i0,i10,i3,i2,i22,.op .BYTE,i5,i2,i22,.op .BYTE,i3,i7,i14,i3,i2,i83,i22,.op .BYTE,i23,i3,i14,i3,i0,i14,.op .MSTORE8,.push 1 8,i43,i15,i40,i0,.push 2 461,i36,i40,.push 2 514,i36,i15,i40,.push 2 8192,.push 2 455,i44,i23,i40,i16,i40,i44,i23,i22,i31,i34,i31,i38,i31,i0,.push 2 536,i36,i22,i22,i74,i23,i14,i37,i3,i14,i5,i3,i34,i7,i47,.push 1 207,i36,.push 2 1186]

private theorem instructionsPart2_wf :
    instructionsPart2.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart2,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart3 : List Instr :=
  [i5,i7,i37,i24,i25,i12,.push 1 131,i44,i23,i38,i31,.push 1 33,i5,i29,.push 1 223,i51,.push 2 3502,i36,i34,i31,i22,i31,.push 1 31,i7,i3,.push 1 5,i43,i0,.push 1 5,i54,i37,i7,i3,i18,i3,i0,i31,i22,.op .SGT,i79,i34,i27,i7,i3,i29,i31,i83,i0,i22,i29,i26,.push 1 2,i47,i27,.push 1 127,i26,i60,i60,.push 1 207,i36,i7,i37,i3,.push 2 2656,i19,i5,i53,i19,i34,i14,i29,.push 2 2752,i19,i5,i55,i3,i53,i19,i10,i5,i22,i77,i40,.push 2 2357,i44,i23,i40,i18,i57,i22,i74,i23,i23,.push 5 137506062208,.push 1 68,i31,i29,.push 2 519,i36,i22,i31,i57,i29,i34,i31,.push 1 2,i29,i60,.push 1 100,i31,i60,.push 2 519,i36,i34,.push 1 62,i22,.op .CODECOPY,i53,i22,i74,i23,i0,i7,i57,i22,i19,i0,i53]

private theorem instructionsPart3_wf :
    instructionsPart3.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart3,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart4 : List Instr :=
  [i19,i5,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i21,i11,i1,i0,i53,i19,i21,i1,i0,i53,i19,i13,i1,i0,i53,i19,i8,i1,i0,i53,i19,i12,i1,i0,i53,i19,i4,i1,i0,i53,i19,i25,i1,i0,i53,i19,i27,i1,i0,i53,i19,i24,i1,i0,i53,i19,i10,i1,i0,i53,i19,i18,i1,i0,i53,i19,i7,i1,i0,i53,i19,i14,i1,i0,i53,i19,i1,i53,i19,i5,i84,i43,i53,i19,i5,.push 1 7,i43,i53,i19,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0]

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
  [i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,i0,.push 2 514,i2,i33,i26,i2,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 482,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 515,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 483,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 516,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 484,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 517,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 485,i2,i33,i26,i2,i1,i0,i1]

private theorem instructionsPart7_wf :
    instructionsPart7.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart7,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart8 : List Instr :=
  [i0,i1,i0,i1,i0,i1,.push 2 518,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 486,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 519,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 487,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 520,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 488,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 521,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 489,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 522,i2,i33,i26,i2,i1,i0,i1,i0,i1]

private theorem instructionsPart8_wf :
    instructionsPart8.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart8,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart9 : List Instr :=
  [i0,i1,i0,i1,.push 2 490,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 523,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 491,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 524,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 492,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 525,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 493,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 526,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 494,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1]

private theorem instructionsPart9_wf :
    instructionsPart9.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart9,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart10 : List Instr :=
  [i0,i1,.push 2 527,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 495,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 528,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 496,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 529,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 497,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 530,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 498,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 531,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1]

private theorem instructionsPart10_wf :
    instructionsPart10.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart10,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart11 : List Instr :=
  [.push 2 499,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 532,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 500,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 533,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 501,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 534,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 502,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 535,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 503,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 536,i2]

private theorem instructionsPart11_wf :
    instructionsPart11.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart11,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart12 : List Instr :=
  [i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 504,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 537,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 505,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 538,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 506,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 539,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 507,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 540,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 508,i2,i33,i26]

private theorem instructionsPart12_wf :
    instructionsPart12.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart12,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart13 : List Instr :=
  [i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 541,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 509,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 542,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 510,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 543,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 511,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 544,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,.push 2 512,i2,i33,i26,i2,i1,i0,i1,i0,i1,i0,i1,i0,i1,i27,i57,i54,i33,i26,i2]

private theorem instructionsPart13_wf :
    instructionsPart13.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart13,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart14 : List Instr :=
  [i1,i0,i1,i0,i1,i0,i1,i0,i1,i14,.push 1 5,i54,i33,i26,i2,i1,i22,i19,i34,i22,i74,i23,i37,i2,i22,i29,i85,i19,.push 2 2436,i44,i23,i11,i22,.push 2 3238,i44,i22,i22,i22,i22,i22,i23,i11,.push 1 15,i5,i37,i3,i31,.push 1 232,i43,.push 3 65537,.op .XOR,i34,i31,i84,.op .XOR,i60,i79,.push 2 3238,i36,.push 1 207,i44,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i23,i0,i7,.op .XOR,.push 1 207,i36,i0,i37,i46,i77,.push 2 2378,.push 2 3513,i44,i23,i0,i46,i86,i78,i0,i35,.op .EQ,.push 2 2284,i36,i41,i2,i22,i29,.push 2 1504,i19,i42,i2,i83,.push 2 1472,i19,i39,i2,i83,.push 2 1440,i19,i35,i2,i83,.push 2 1408,i19,i37,i2,i83,i85,i19,i23,i38,i2]

private theorem instructionsPart14_wf :
    instructionsPart14.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart14,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart15 : List Instr :=
  [i83,i87,i19,i34,i2,i83,.push 2 1312,i19,i22,i2,i0,i83,i56,i19,i0,i22,i29,i5,i26,i0,.op .CLZ,i0,i57,i3,.push 2 1600,i19,.push 1 255,i29,.push 2 1536,i19,i16,.op .DIV,i0,.push 2 1568,i19,i0,i0,i22,i29,.op .MOD,.push 2 1632,i19,.push 2 2752,i2,i2,i0,i14,i6,i0,i84,i6,.push 1 2,.op .XOR,i0,i14,i6,.push 1 2,i29,i6,i0,i14,i6,.push 1 2,i29,i6,i0,i14,i6,.push 1 2,i29,i6,i0,i14,i6,.push 1 2,i29,i6,i0,i14,i6,.push 1 2,i29,i6,i0,i15,i6,.push 1 2,i29,i6,i0,i15,i6,.push 2 1664,i19,i6,i22,i29,i65,i19,.push 2 2310,i18,i57,.op .EQ,i79,.push 2 2597,i36,.push 2 2656,i2,i31,i22,.op .BYTE,i84,.op .EQ,.push 2 1653,i6,i3,i23,.push 2 2519,i34,i2,i35,i43,.push 2 1536,i2,.push 2 1568,i2,.push 2 1664,i2]

private theorem instructionsPart15_wf :
    instructionsPart15.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart15,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart16 : List Instr :=
  [.push 2 1632,i2,.push 2 1504,i2,.push 2 1472,i2,.push 2 1440,i2,.push 2 1408,i2,i85,i2,i87,i2,.push 2 1312,i2,i9,i8,i79,.push 2 2675,i36,i0,.push 2 2011,i6,.push 2 18783,i29,i16,i9,i57,i26,i43,i5,i44,i23,i49,i75,i49,i0,.push 1 44,i6,.push 2 4092,i29,i16,i9,i57,i26,i43,i5,i44,i23,i86,i46,i55,i78,i55,i2,i0,i11,i43,i16,.push 2 1600,i2,i54,i46,i2,i9,i43,i3,i21,i0,i21,i18,i1,i14,.op .ADDMOD,i16,i29,i13,i6,i9,i5,i35,i43,i6,i5,i22,i2,i6,i46,i2,i29,i51,i16,i29,i23,i45,i15,i11,i47,i14,i3,i60,i0,i8,i6,i14,i13,i7,i1,i5,.push 2 2336,i19,i0,i14,i47,i16,i29,i29,i5,i8,i6,i7,i13,i18,i1,i0,i14,i47]

private theorem instructionsPart16_wf :
    instructionsPart16.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart16,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart17 : List Instr :=
  [i29,i5,i7,i3,.push 2 2304,i2,i5,i3,i0,.push 2 2304,i19,i5,i47,i17,i47,i29,i29,i3,i5,i12,i6,i7,i8,i18,i1,i0,i14,i47,i29,i5,i7,i3,.push 2 2272,i2,i5,i3,i0,.push 2 2272,i19,i5,i47,i17,i47,i29,i29,i3,i5,i4,i6,i7,i12,i18,i1,i0,i14,i47,i29,i5,i7,i3,.push 2 2240,i2,i5,i3,i0,.push 2 2240,i19,i5,i47,i17,i47,i29,i29,i3,i5,i25,i6,i7,i4,i18,i1,i0,i14,i47,i29,i5,i7,i3,i88,i2,i5,i3,i0,i88,i19,i5,i47,i17,i47,i29,i29,i3,i5,i27,i6,i7,i25,i18,i1,i0,i14,i47,i29,i5,i7,i3,.push 2 2176,i2,i5,i3,i0,.push 2 2176,i19,i5,i47,i17,i47,i29]

private theorem instructionsPart17_wf :
    instructionsPart17.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart17,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart18 : List Instr :=
  [i29,i3,i5,i24,i6,i7,i27,i18,i1,i0,i14,i47,i29,i5,i7,i3,.push 2 2144,i2,i5,i3,i0,.push 2 2144,i19,i5,i47,i17,i47,i29,i29,i3,i56,i2,i7,i7,i14,i6,i15,i18,i1,i0,i14,i47,i29,i5,i7,i3,i46,i2,i5,i3,i0,i46,i19,i5,i47,i17,i47,i29,i29,i3,i55,i2,i3,i29,i0,i23,i23,.push 2 3068,i36,i16,i40,i23,i83,i3,i0,i14,i36,i23,i23,i40,i81,i44,i22,i23,i55,i19,i40,i23,i22,.push 2 2784,i2,i23,i0,i2,i46,i14,i29,i2,i5,i3,i16,i5,i51,i16,i7,i3,i28,i7,i51,i60,i15,i5,i19,.push 1 31,i83,i3,.push 2 2111,i5,i47,.push 2 3080,i36,i40,i55,i2,i5,i3,i0,i55]

private theorem instructionsPart18_wf :
    instructionsPart18.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart18,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart19 : List Instr :=
  [i19,i51,i79,.push 2 3074,i36,i55,i2,i0,i79,.push 2 3056,i36,i22,i22,i23,i46,i2,.push 32 115792089237316195423570985008687818650289190543147997896584493414467105718271,i51,.push 1 207,i36,i86,i46,.push 2 2368,i78,.op (.Swap swap12),i45,i30,.push 2 5430,i44,i23,i5,i35,.op .XOR,.push 2 3147,i36,i23,.op (.Swap swap12),i65,i2,i75,.push 2 5244,i44,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i22,i23,i0,i38,i2,i10,i6,i3,i34,i2,i24,i6,i3,i22,i2,i27,i6,i3,i12,i18,i6,i3,i4,i7,i6,i3,i11,i6,i61,i43,i16,i21,i38,i2,i24,i1,i3,i21,i34,i2,i27,i1,i3,i21,i22,i2,i25,i1,i3,i21,i8,i10,i1,i3,i21,i12,i18,i1,i3,i21,i39,i2,i7,i1,i3]

private theorem instructionsPart19_wf :
    instructionsPart19.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart19,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart20 : List Instr :=
  [i21,i16,i32,i1,i0,i37,i2,i24,i6,i3,i38,i2,i27,i6,i3,i34,i2,i25,i6,i3,i22,i2,i4,i6,i3,i13,i10,i6,i3,i8,i18,i6,i3,i12,i7,i6,i3,i9,i6,i61,i43,i16,i11,i37,i2,i27,i1,i3,i11,i38,i2,i25,i1,i3,i11,i34,i2,i4,i1,i3,i11,i22,i2,i12,i1,i3,i11,i21,i24,i1,i3,i11,i13,i10,i1,i3,i11,i8,i18,i1,i3,i11,i39,i2,i7,i1,i3,i11,i16,i32,i1,.push 2 3787,i44,i23,i34,i31,.push 2 673,i36,i38,i31,i34,i51,.push 2 673,i36,i38,.push 2 4764,i44,i29,i23,i88,i2,i37,i2,i0,i14,i29,i64,i19,i47,.push 2 3640,i44,i23,.push 2 3457,i36,i22,i22,i74,i29]

private theorem instructionsPart20_wf :
    instructionsPart20.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart20,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart21 : List Instr :=
  [i29,i29,i23,i22,i2,i46,i2,i51,i16,i36,.push 2 2378,i46,.push 2 2688,i2,i35,.op .EQ,.push 2 3482,i36,i23,.push 2 2336,i2,i41,i2,i0,i14,i29,i72,i19,i47,i0,i42,i2,i3,i0,.push 2 2304,i2,i5,i5,i29,i71,i19,i51,i15,i47,i60,i0,i39,i2,i3,i0,.push 2 2272,i2,i5,i5,i29,i70,i19,i51,i15,i47,i60,i0,i35,i2,i3,i0,.push 2 2240,i2,i5,i5,i29,i69,i19,i51,i15,i47,i60,i0,i37,i2,i3,i0,i88,i2,i5,i5,i29,i64,i19,i51,i15,i47,i60,i23,i0,i38,i2,i3,i0,.push 2 2176,i2,i5,i5,i29,i68,i19,i51,i15,i47,i60,i0,i34,i2,i3,i0,.push 2 2144,i2,i5,i5,i29,i67,i19,i51,i15,i47,i60,i0,i22]

private theorem instructionsPart21_wf :
    instructionsPart21.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart21,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart22 : List Instr :=
  [i2,i3,i0,i46,i2,i5,i5,i29,i63,i19,i51,i15,i47,i60,i79,i55,i2,i60,.push 2 3728,i36,.push 2 3717,i44,i23,i46,.push 2 2688,i2,i15,i78,i44,i23,i63,.push 2 2688,i2,i15,i78,i44,i22,i23,i86,i46,i55,i78,i55,i2,i46,i2,i21,i0,i21,i18,i1,i14,.op .ADDMOD,i0,i15,i29,i21,i6,i9,i5,i35,i43,i6,i16,i15,i51,i16,i29,.push 2 2755,i44,i22,i23,i0,i9,i35,i2,i25,i1,i3,i9,i37,i2,i4,i1,i3,i9,i38,i2,i12,i1,i3,i9,i34,i2,i8,i1,i3,i9,i22,i2,i13,i1,i3,i9,i9,i27,i1,i3,i9,i11,i24,i1,i3,i9,i21,i10,i1,i3,i9,i13,i18,i1,i3,i16,i35,i2,i27,i6]

private theorem instructionsPart22_wf :
    instructionsPart22.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart22,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart23 : List Instr :=
  [i3,i37,i2,i25,i6,i3,i38,i2,i4,i6,i3,i34,i2,i12,i6,i3,i22,i2,i8,i6,i3,i11,i24,i6,i3,i21,i10,i6,i3,i13,i18,i6,i3,i8,i7,i6,i3,i42,i2,i6,i61,i43,i30,i40,i11,i39,i2,i24,i1,i3,i11,i16,i32,i1,.push 2 4805,i44,i22,i23,i35,i46,i55,i78,i55,i2,i46,i2,i21,i0,i21,i18,i1,i14,.op .ADDMOD,i0,i15,i29,i21,i6,i9,i5,i35,i43,i6,i16,i15,i51,i16,i29,.push 2 10798,i44,.push 1 0,i23,i11,i46,i86,i78,i11,.push 1 7,i43,.push 2 2298,i82,i16,i5,i44,i23,i40,i40,i40,i57,i3,.push 1 187,i44,i23,i40,i0,i24,i34,i29,i84,i54,i54,i22,i19,i10,i22,i74,i23,i57]

private theorem instructionsPart23_wf :
    instructionsPart23.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart23,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart24 : List Instr :=
  [i24,i29,i23,i27,i57,i18,i18,.push 1 7,i29,i43,i26,i14,i6,i57,i3,i5,i25,i0,i1,i1,i52,i40,i57,i14,i3,i15,.push 1 7,i47,.push 2 4014,i36,i40,.push 2 3983,i44,i23,i0,i0,i6,i8,i6,i61,i43,i12,i8,i7,i0,i0,i3,i30,i1,i13,i39,i2,i18,i1,i3,i32,i1,i0,i18,i18,i6,i3,i25,i7,i6,i3,i21,i6,i61,i43,i16,i13,i10,i10,i1,i3,i13,i4,i18,i1,i3,i13,i39,i2,i7,i1,i3,i13,i16,i32,i1,i0,i24,i10,i6,i3,i10,i0,i6,i3,i12,i18,i6,i3,i4,i7,i6,i3,i11,i6,i61,i43,i16,i21,i27,i24,i1,i3,i21,i24,i0,i0,i3,i59,i1,i3,i21,i8]

private theorem instructionsPart24_wf :
    instructionsPart24.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart24,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart25 : List Instr :=
  [i10,i1,i3,i21,i12,i18,i1,i3,i21,i39,i2,i7,i1,i3,i21,i16,i32,i1,i0,i25,i24,i6,i25,i25,i6,i3,i3,i13,i10,i6,i3,i8,i18,i6,i3,i12,i7,i6,i3,i9,i6,i61,i43,i16,i11,i4,i27,i1,i9,i4,i4,i1,i3,i3,i11,i21,i24,i1,i3,i11,i13,i10,i1,i3,i11,i8,i18,i1,i3,i11,i39,i2,i7,i1,i3,i11,i16,i32,i1,i11,i24,i8,i1,i9,i25,i8,i1,i3,i5,i3,i9,i4,i0,i1,i3,i9,i9,i27,i1,i3,i9,i11,i24,i1,i3,i9,i21,i10,i1,i3,i9,i13,i18,i1,i3,i16,i12,i27,i6,i12,i4,i6,i3,i3,i25,i0,i0,i3]

private theorem instructionsPart25_wf :
    instructionsPart25.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart25,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart26 : List Instr :=
  [.op (.Swap swap9),i6,i3,i11,i24,i6,i3,i21,i10,i6,i3,i13,i18,i6,i3,i8,i7,i6,i3,i42,i2,i6,i61,i43,i30,i40,i11,i39,i2,i24,i1,i3,i11,i16,i32,i1,i0,i12,i25,i6,i12,i12,i6,i3,i3,i11,i10,i6,i3,i21,i18,i6,i3,i13,i7,i6,i3,i8,i24,i6,i3,i16,i9,i0,i13,i12,i1,i16,i8,i8,i1,i3,i3,i9,i9,i24,i1,i3,i9,i11,i10,i1,i3,i9,i21,i18,i1,i3,i9,i13,i27,i1,i3,i16,i20,i26,i0,i58,i40,i9,i15,i29,i5,i3,i32,i1,i0,i12,i4,i6,i3,i4,i0,i6,i3,i11,i18,i6,i3,i21,i7,i6,i3,i13,i24,i6,i3,i16]

private theorem instructionsPart26_wf :
    instructionsPart26.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart26,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart27 : List Instr :=
  [i9,i8,i12,i1,i3,i9,i12,i0,i0,i3,i49,i1,i3,i9,i9,i10,i1,i3,i9,i11,i18,i1,i3,i9,i21,i27,i1,i3,i16,i20,i26,i0,i59,i40,i9,i15,i29,i5,i3,i32,i1,i0,i12,i12,i6,i3,i11,i7,i6,i3,i21,i24,i6,i3,i20,i26,i59,i40,i11,i4,i8,i1,i3,i11,i14,i9,i1,i3,i11,i10,i11,i1,i3,i32,i9,i4,i5,i17,i29,i3,i1,i0,i12,i0,i6,i3,i10,i9,i6,i3,i20,i26,i73,i40,i11,i12,i0,i1,i3,i11,i10,i9,i1,i3,i32,i9,i12,i5,i17,i29,i3,i1,i73,i40,i40,i40,i40,i40,i57,i13,i29,i49,.push 2 4054,i36,i22,i2,i5,i6]

private theorem instructionsPart27_wf :
    instructionsPart27.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart27,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart28 : List Instr :=
  [i8,i6,i61,i43,i12,i8,i22,i2,i18,i1,i13,i39,i2,i18,i1,i3,i32,i1,i0,i34,i2,i18,i6,i3,i22,i2,i10,i6,i3,i25,i7,i6,i3,i21,i6,i61,i43,i16,i13,i34,i2,i10,i1,i3,i13,i22,i2,i24,i1,i3,i13,i4,i18,i1,i3,i13,i39,i2,i7,i1,i3,i13,i16,i32,i1,.push 2 3280,i44,i23,i31,i22,i31,i37,i3,i31,i5,i34,i29,i84,i54,i43,i57,i51,i22,i19,i0,i53,i29,i74,i23,i22,i40,i23,i23,i23,i23,i14,.op .MOD,i22,i51,i22,i19,i53,i22,i74,i23,i0,i35,i2,i25,i6,i3,i37,i2,i4,i6,i3,i38,i2,i12,i6,i3,i34,i2,i8,i6,i3,i11,i10]

private theorem instructionsPart28_wf :
    instructionsPart28.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart28,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart29 : List Instr :=
  [i6,i3,i21,i18,i6,i3,i13,i7,i6,i3,i8,i24,i6,i3,i16,i9,i35,i2,i4,i1,i3,i9,i37,i2,i12,i1,i3,i9,i38,i2,i8,i1,i3,i9,i34,i2,i13,i1,i3,i9,i9,i24,i1,i3,i9,i11,i10,i1,i3,i9,i21,i18,i1,i3,i9,i13,i27,i1,i3,i52,i40,i41,i2,i26,i0,i52,i29,i11,i3,i32,i9,i15,i1,i0,i35,i2,i4,i6,i3,i37,i2,i12,i6,i3,i38,i2,i8,i6,i3,i11,i18,i6,i3,i21,i7,i6,i3,i13,i24,i6,i3,i16,i9,i35,i2,i12,i1,i3,i9,i37,i2,i8,i1,i3,i9,i38,i2,i13,i1,i3,i9,i9,i10,i1,i3,i9,i11,i18]

private theorem instructionsPart29_wf :
    instructionsPart29.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart29,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart30 : List Instr :=
  [i1,i3,i9,i21,i27,i1,i3,i58,i40,i41,i2,i26,i0,i58,i29,i11,i3,i32,i9,i15,i1,i0,i35,i2,i12,i6,i3,i37,i2,i8,i6,i3,i11,i7,i6,i3,i21,i24,i6,i3,i16,i9,i35,i2,i8,i1,i3,i9,i37,i2,i13,i1,i3,i9,i9,i18,i1,i3,i9,i11,i27,i1,i3,i59,i40,i41,i2,i26,i0,i59,i29,i11,i3,i32,i9,i15,i1,i35,i2,i9,i5,i13,i1,.op (.Swap swap9),i40,i12,i6,i5,i3,i10,i9,i6,i3,i41,i2,i26,i73,i3,i11,i10,i9,i1,i3,i32,i9,i12,i5,i17,i29,i3,i1,i73,i40,i40,i40,i40,i40,i23,i25,i10,i51,.push 2 5195,i36,.push 1 255,i39,i2,i14,i29]

private theorem instructionsPart30_wf :
    instructionsPart30.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart30,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart31 : List Instr :=
  [i27,i5,i7,i43,i10,i29,i29,i4,i5,i18,i43,i27,i29,i29,i41,i2,i0,i14,i26,i28,i5,i26,i17,i26,i17,i43,i27,i29,i8,i16,i29,i0,.push 1 255,i43,i16,i41,i2,i26,i16,i4,i29,i21,i16,i29,i0,.push 1 255,i43,.push 2 5189,i36,i73,i40,i58,i40,i30,i40,i28,i40,i16,i40,.push 2 5105,i44,i23,i40,i40,i40,i40,i40,i23,i5,.push 1 240,i54,i5,i60,i37,i19,i14,i41,i54,i14,i61,i43,i60,i38,i19,i7,.push 1 208,i54,i7,i34,i43,i60,i34,i19,i18,i42,i54,i18,.push 1 48,i43,i60,i22,i19,i35,i22,i74,i23,i11,i13,i61,i54,i0,i42,i19,.push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,i0,.push 1 11,i43,.push 4 224,i19,i22,i2,i42,i43,i41,i2,i0,.push 1 36,i2]

private theorem instructionsPart31_wf :
    instructionsPart31.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart31,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart32 : List Instr :=
  [i14,i26,.push 1 66,i2,i7,i26,i37,i2,.push 1 6,i2,i10,i26,i30,i26,i39,i19,.push 2 352,i2,i7,i26,i22,i19,.push 2 322,i2,i7,i26,i34,i19,.push 2 292,i2,i7,i26,i38,i19,i16,i15,.push 2 262,i2,i26,i37,i19,i86,i2,i42,i43,i35,i19,i46,i2,i61,i43,i0,.push 1 200,i43,.push 5 1099511627775,.op .EQ,.push 1 207,i36,i41,i2,.push 2 2170,i2,i5,i26,.push 2 2200,i2,i14,i26,i88,i2,.push 1 176,i54,.push 2 2140,i2,i18,i26,i17,i26,.push 2 4054,i44,i23,i11,i24,i61,i43,.push 2 2368,i2,i61,i43,.push 1 134,i2,i14,i26,i41,i2,i7,i26,i0,i87,i19,i16,i15,i28,.push 1 194,i2,i5,i26,i0,i85,i19,i22,i2,i35,i43,i0,.push 2 1600,i19,.push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,.push 1 14,i2,i18,i26,i0,.push 2 1568,i19,.push 1 74,i2,i10]

private theorem instructionsPart32_wf :
    instructionsPart32.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart32,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart33 : List Instr :=
  [i26,.push 2 2546,i2,i24,i26,.push 2 2576,i2,i27,i26,.push 1 104,i2,i25,i26,.push 1 44,i2,i4,i26,.push 1 164,i2,i12,i26,.push 2 2592,i2,.push 1 112,i54,i8,i26,i48,i19,.push 2 2516,i2,i8,i26,i34,i19,.push 2 2486,i2,i8,i26,i38,i19,.push 2 2456,i2,i8,i26,i37,i19,.push 2 2426,i2,i8,i26,i35,i19,.push 2 2396,i2,i8,i26,i39,i19,i23,i65,i2,i75,i40,i48,i2,i25,i5,i0,i0,i6,i11,i6,i20,i26,i49,i40,i12,i28,i1,i5,i8,i9,i1,i3,i32,i1,i48,i2,i0,i3,i0,i48,i19,i4,i5,i27,i1,i16,i24,i6,i14,i3,i8,i21,i6,i3,i15,i3,i4,i13,i13,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i49,i40,i1,i3,i32]

private theorem instructionsPart33_wf :
    instructionsPart33.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart33,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart34 : List Instr :=
  [i1,i48,i2,i14,i8,i6,i24,i0,i6,i8,i7,i12,i1,i28,i4,i6,i18,i3,i3,i3,i4,i21,i6,i3,i15,i3,i4,i24,i0,i0,i3,i59,i1,i3,i4,i7,i13,i1,i3,i4,i13,i12,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i42,i19,i1,i3,i32,i1,i34,i2,i4,i48,i2,i0,i7,i6,i4,i4,i6,i3,i28,i1,i12,i25,i25,i1,i3,i14,i3,i15,i3,i11,i8,i6,i3,i14,i4,i6,i3,i8,i42,i2,i6,i3,i16,i4,i9,i13,i1,i3,i4,i7,i12,i1,i3,i4,i13,i42,i2,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i22,i19,i1,i3,i32,i1,i38]

private theorem instructionsPart34_wf :
    instructionsPart34.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart34,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart35 : List Instr :=
  [i2,i4,i48,i2,i0,i7,i6,i34,i2,i4,i6,i3,i28,i1,i12,i34,i2,i25,i1,i3,i14,i3,i15,i3,i24,i0,i6,i3,i18,i8,i6,i3,i11,i4,i6,i3,i14,i42,i2,i6,i3,i8,i22,i2,i6,i3,i16,i4,i27,i0,i0,i3,i73,i1,i3,i4,i10,i13,i1,i3,i4,i9,i12,i1,i3,i4,i7,i42,i2,i1,i3,i4,i13,i22,i2,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i41,i19,i1,i3,i32,i1,i37,i2,i4,i48,i2,i0,i7,i6,i38,i2,i4,i6,i3,i34,i2,i12,i6,i3,i28,i1,i12,i38,i2,i25,i1,i3,i12,i34,i2,i4,i1,i3,i14,i3,i15,i3]

private theorem instructionsPart35_wf :
    instructionsPart35.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart35,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart36 : List Instr :=
  [i27,i8,i6,i3,i18,i4,i6,i3,i11,i42,i2,i6,i3,i14,i22,i2,i6,i3,i8,i41,i2,i6,i3,i16,i4,i25,i13,i1,i3,i4,i10,i12,i1,i3,i4,i9,i42,i2,i1,i3,i4,i7,i22,i2,i1,i3,i4,i13,i41,i2,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i50,i19,i1,i3,i32,i1,i35,i2,i4,i48,i2,i0,i7,i6,i37,i2,i4,i6,i3,i38,i2,i12,i6,i3,i28,i1,i12,i37,i2,i25,i1,i3,i12,i38,i2,i4,i1,i3,i14,i3,i15,i3,i34,i2,i0,i6,i3,i7,i8,i6,i3,i27,i4,i6,i3,i18,i42,i2,i6,i3,i11,i22,i2,i6,i3,i14,i41]

private theorem instructionsPart36_wf :
    instructionsPart36.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart36,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart37 : List Instr :=
  [i2,i6,i3,i8,i50,i2,i6,i3,i16,i4,i34,i2,i0,i0,i0,i3,i34,i19,i1,i3,i4,i18,i13,i1,i3,i4,i25,i12,i1,i3,i4,i10,i42,i2,i1,i3,i4,i9,i22,i2,i1,i3,i4,i7,i41,i2,i1,i3,i4,i13,i50,i2,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i62,i19,i1,i3,i32,i1,.push 2 1568,i2,i59,i39,i2,i12,i48,i2,i0,i7,i6,i4,i35,i2,i6,i3,i37,i2,i8,i6,i3,i38,i2,i34,i2,i6,i3,i28,i1,i8,i35,i2,i4,i1,i3,i8,i37,i2,i12,i1,i3,i8,i38,i2,i34,i2,i1,i3,i7,i3,i28,i3,i8,i12,i6,i3,i18,i14,i6]

private theorem instructionsPart37_wf :
    instructionsPart37.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart37,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart38 : List Instr :=
  [i3,i25,i42,i2,i6,i3,i10,i22,i2,i6,i3,i9,i41,i2,i6,i3,i7,i50,i2,i6,i3,i13,i62,i2,i6,i3,i15,i12,i13,i8,i1,i3,i12,i10,i7,i1,i3,i16,i76,i19,i4,i25,i42,i2,i1,i3,i4,i10,i22,i2,i1,i3,i4,i9,i41,i2,i1,i3,i4,i7,i50,i2,i1,i3,i4,i13,i62,i2,i1,i3,i4,i11,i11,i14,i30,i6,i20,i26,i0,i56,i19,i1,i3,i32,i1,i11,i4,i48,i2,i0,i7,i6,i25,i39,i2,i6,i3,i35,i2,i12,i6,i3,i37,i2,i34,i2,i6,i3,i28,i1,i12,i39,i2,i25,i1,i3,i12,i35,i2,i4,i1,i3,i12,i37,i2,i34,i2,i1]

private theorem instructionsPart38_wf :
    instructionsPart38.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart38,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart39 : List Instr :=
  [i3,i14,i3,i15,i3,i38,i2,i0,i6,i3,.push 2 1600,i2,i75,i8,i28,i8,i14,i10,i1,i3,i28,i6,i3,i76,i2,i4,i6,i3,i7,i42,i2,i6,i3,i27,i22,i2,i6,i3,i18,i41,i2,i6,i3,i11,i50,i2,i6,i3,i14,i62,i2,i6,i3,i8,i56,i2,i6,i3,i16,i4,i38,i2,i0,i0,i0,i3,i38,i19,i1,i3,i4,i76,i2,i12,i1,i3,i4,i18,i42,i2,i1,i3,i4,i25,i22,i2,i1,i3,i4,i10,i41,i2,i1,i3,i4,i9,i50,i2,i1,i3,i4,i7,i62,i2,i1,i3,i4,i13,i56,i2,i1,i3,i4,i20,i7,i5,.op (.Swap swap15),i6,i26,i0,.op (.Swap swap15),i1,i3,i32,i12,i28,i40,i1]

private theorem instructionsPart39_wf :
    instructionsPart39.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart39,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart40 : List Instr :=
  [i11,i4,i62,i2,i58,i0,i7,i6,i39,i2,i12,i6,i3,i35,i2,i34,i2,i6,i3,i37,i2,i38,i2,i6,i3,i28,i1,i12,i39,i2,i4,i1,i3,i12,i35,i2,i34,i2,i1,i3,i12,i37,i2,i38,i2,i1,i3,i14,i3,i15,i3,i76,i2,i8,i6,i3,i42,i2,i4,i6,i3,i7,i22,i2,i6,i3,i27,i41,i2,i6,i3,i18,i50,i2,i6,i3,i11,i24,i6,i3,i14,i56,i2,i6,i3,i8,i11,i6,i3,i16,i4,i76,i2,i13,i1,i3,i4,i42,i2,i12,i1,i3,i4,i18,i22,i2,i1,i3,i4,i25,i41,i2,i1,i3,i4,i10,i50,i2,i1,i3,i4,i9,i27,i1,i3,i4,i7,i56]

private theorem instructionsPart40_wf :
    instructionsPart40.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart40,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart41 : List Instr :=
  [i2,i1,i3,i4,i13,i9,i1,i3,i16,i13,i26,i0,i48,i19,i4,i15,i29,i5,i3,i32,i1,i11,i4,i50,i2,i56,i2,i81,i40,i59,i0,i7,i6,i39,i2,i34,i2,i6,i3,i35,i2,i38,i2,i6,i3,i28,i1,i12,i39,i2,i34,i2,i1,i3,i12,i35,i2,i38,i2,i1,i3,i14,i3,i15,i3,i37,i2,i0,i6,i3,i42,i2,i8,i6,i3,i22,i2,i4,i6,i3,i7,i41,i2,i6,i3,i27,i27,i6,i3,i18,i24,i6,i3,i8,i9,i6,i3,i14,i11,i6,i3,i16,i4,i37,i2,i0,i0,i0,i3,i37,i19,i1,i3,i4,i42,i2,i13,i1,i3,i4,i22,i2,i12,i1,i3,i4,i18,i41]

private theorem instructionsPart41_wf :
    instructionsPart41.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart41,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart42 : List Instr :=
  [i2,i1,i3,i4,i25,i25,i1,i3,i4,i10,i27,i1,i3,i4,i9,i21,i1,i3,i4,i7,i9,i1,i3,i16,i13,i26,i0,.push 2 800,i19,i4,i15,i29,i5,i3,i32,i1,i11,i16,i35,i2,i37,i2,i39,i2,i38,i2,i34,i2,i11,i27,i14,i1,i9,i7,i10,i1,i3,i9,i10,i27,i1,i3,i24,i3,i58,i6,i15,i6,i3,i15,i6,i3,i3,i22,i2,i8,i6,i3,i41,i2,i4,i6,i3,i7,i27,i6,i3,i27,i24,i6,i3,i8,i10,i6,i3,i11,i11,i6,i3,i16,i4,i22,i2,i13,i1,i3,i4,i41,i2,i12,i1,i3,i4,i18,i25,i1,i3,i4,i25,i27,i1,i3,i4,i10,i21,i1,i3,i4]

private theorem instructionsPart42_wf :
    instructionsPart42.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart42,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart43 : List Instr :=
  [i9,i9,i1,i3,i16,i13,i26,i0,.push 2 832,i19,i4,i15,i29,i5,i3,i32,i1,i11,i16,i39,i2,i37,i2,i38,i2,i13,i10,i14,i1,i21,i7,i10,i1,i3,i18,i3,i30,i6,i15,i6,i3,i3,i35,i2,i0,i6,i3,i41,i2,i8,i6,i3,i24,i4,i6,i3,i7,i24,i6,i3,i8,i25,i6,i3,i18,i11,i6,i3,i16,i4,i35,i2,i0,i1,i3,i4,i41,i2,i13,i1,i3,i4,i27,i12,i1,i3,i4,i18,i27,i1,i3,i4,i13,i4,i1,i3,i4,i10,i9,i1,i3,i16,i13,i26,i0,i34,i19,i4,i15,i29,i5,i3,i32,i1,i11,i16,i39,i2,i35,i2,i0,i3,i37,i2,i13,i10,i14,i1]

private theorem instructionsPart43_wf :
    instructionsPart43.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart43,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart44 : List Instr :=
  [i21,i7,i10,i1,i3,i18,i3,i30,i6,i15,i6,i3,i3,i24,i8,i6,i3,i10,i4,i6,i3,i8,i18,i6,i3,i27,i11,i6,i3,i16,i4,i27,i13,i1,i3,i4,i24,i12,i1,i3,i4,i18,i21,i1,i3,i4,i25,i9,i1,i3,i16,i13,i26,i0,i38,i19,i4,i15,i29,i5,i3,i32,i1,.push 2 832,i2,i52,i40,i11,i4,i35,i2,i0,i3,i0,i7,i6,i28,i1,i14,i3,i15,i3,i39,i2,i0,i6,i3,i10,i8,i6,i3,i8,i4,i6,i3,i7,i11,i6,i3,i16,i4,i39,i2,i0,i1,i3,i4,i24,i13,i1,i3,i4,i13,i12,i1,i3,i4,i11,i10,i1,i3,i16,i13,i26,i0,i37,i19,i4]

private theorem instructionsPart44_wf :
    instructionsPart44.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart44,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart45 : List Instr :=
  [i15,i29,i5,i3,i32,i1,.push 2 800,i2,i30,i40,i11,i39,i2,i0,i3,i12,i5,i7,i1,i15,i6,i14,i3,i8,i21,i6,i3,i4,i9,i6,i3,i15,i3,i4,i8,i21,i1,i3,i4,i11,i12,i1,i3,i16,i13,i26,i0,i35,i19,i4,i15,i29,i5,i3,i32,i1,.op (.Swap swap9),i40,i27,i4,i21,i1,i25,i9,i0,i1,i8,i3,i3,i4,i21,i6,i9,i0,i6,i85,i2,.op (.Swap swap12),i3,i3,i13,i26,i0,i39,i19,i4,i15,i29,i5,i3,i32,i1,i81,i40,.push 5 1344,i2,i49,i40,i57,i9,i29,i82,.push 2 5614,i36,i33,i2,i8,i26,i63,i19,.push 2 450,i2,i8,i26,i67,i19,.push 2 420,i2,i8,i26,i68,i19,.push 2 390,i2,i8,i26,i64,i19]

private theorem instructionsPart45_wf :
    instructionsPart45.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart45,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart46 : List Instr :=
  [.push 2 360,i2,i8,i26,i69,i19,.push 2 330,i2,i8,i26,i70,i19,.push 2 300,i2,i8,i26,i71,i19,.push 2 270,i2,i8,i26,i72,i19,i86,i2,i35,i43,i32,i19,i48,i2,i25,i63,i2,i0,i7,i6,i65,i2,i6,i11,i26,i49,i40,i12,i28,i1,i5,i8,i9,i1,i3,i32,i1,i0,i4,i48,i2,i67,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i8,i21,i6,i63,i2,i17,i3,i7,i25,i6,i3,i28,i27,i1,i3,i4,i8,i21,i1,i3,i4,i11,i65,i2,i14,i30,i6,i9,i26,i0,i49,i40,i1,i3,i32,i1,i67,i2,i48,i2,i68,i2,i8,i5,i7,i1,i15,i6,i7,i3,i8,i7,i4,i1,i28,i25,i6,i3]

private theorem instructionsPart46_wf :
    instructionsPart46.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart46,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart47 : List Instr :=
  [i28,i3,i3,i4,i27,i63,i2,i17,i5,i10,i6,i3,i10,i11,i6,i3,i8,i9,i6,i3,i17,i1,i3,i4,i7,i13,i1,i3,i4,i4,i21,i1,i3,i4,i11,i65,i2,i14,i30,i6,i9,i26,i0,i42,i19,i1,i3,i32,i1,i68,i2,i48,i2,i64,i2,i8,i5,i7,i1,i15,i6,i7,i3,i8,i7,i4,i1,i28,i25,i6,i3,i28,i3,i3,i34,i2,i67,i2,i8,i5,i12,i1,i63,i2,i21,i5,i10,i1,i28,i8,i6,i17,i6,i17,i3,i3,i28,i3,i3,i11,i8,i6,i3,i14,i4,i6,i3,i8,i42,i2,i6,i3,i16,i4,i9,i13,i1,i3,i4,i7,i12,i1,i3,i4,i13,i42,i2,i1]

private theorem instructionsPart47_wf :
    instructionsPart47.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart47,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart48 : List Instr :=
  [i3,i4,i11,i65,i2,i14,i30,i6,i9,i26,i0,i22,i19,i1,i3,i32,i1,i64,i2,i48,i2,i69,i2,i8,i5,i7,i1,i15,i6,i7,i3,i8,i7,i4,i1,i28,i25,i6,i3,i28,i3,i3,i4,i27,i68,i2,i17,i5,i10,i6,i3,i17,i1,i3,i38,i2,i34,i2,i67,i2,i13,i5,i7,i1,i15,i6,i63,i2,i30,i3,i28,i3,i8,i14,i10,i1,i3,i28,i6,i3,i18,i8,i6,i3,i11,i4,i6,i3,i14,i42,i2,i6,i3,i8,i22,i2,i6,i3,i16,i4,i10,i13,i1,i3,i4,i9,i12,i1,i3,i4,i7,i42,i2,i1,i3,i4,i13,i22,i2,i1,i3,i4,i11,i65,i2,i14,i30,i6]

private theorem instructionsPart48_wf :
    instructionsPart48.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart48,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart49 : List Instr :=
  [i9,i26,i0,i41,i19,i1,i3,i32,i1,i69,i2,i48,i2,i70,i2,i8,i5,i7,i1,i15,i6,i7,i3,i8,i7,i4,i1,i28,i25,i6,i3,i28,i3,i3,i4,i27,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i34,i2,i68,i2,i17,i5,i10,i6,i3,i17,i1,i3,i37,i2,i38,i2,i67,i2,i13,i5,i7,i1,i15,i6,i63,i2,i30,i3,i28,i3,i8,i14,i10,i1,i3,i28,i6,i3,i27,i8,i6,i3,i18,i4,i6,i3,i11,i42,i2,i6,i3,i14,i22,i2,i6,i3,i8,i41,i2,i6,i3,i16,i4,i25,i13,i1,i3,i4,i10,i12,i1,i3,i4,i9,i42,i2,i1,i3,i4,i7,i22]

private theorem instructionsPart49_wf :
    instructionsPart49.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart49,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart50 : List Instr :=
  [i2,i1,i3,i4,i13,i41,i2,i1,i3,i4,i11,i65,i2,i14,i30,i6,i9,i26,i0,i50,i19,i1,i3,i32,i1,i70,i2,i48,i2,i71,i2,i8,i5,i7,i1,i15,i6,i7,i3,i8,i7,i4,i1,i28,i25,i6,i3,i28,i3,i3,i4,i27,i69,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i34,i2,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i38,i2,i68,i2,i17,i5,i10,i6,i3,i17,i1,i3,i35,i2,i37,i2,i67,i2,i13,i5,i7,i1,i15,i6,i63,i2,i30,i3,i28,i3,i8,i14,i10,i1,i3,i28,i6,i3,i7,i8,i6,i3,i27,i4,i6,i3,i18,i42,i2,i6,i3,i11]

private theorem instructionsPart50_wf :
    instructionsPart50.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart50,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart51 : List Instr :=
  [i22,i2,i6,i3,i14,i41,i2,i6,i3,i8,i50,i2,i6,i3,i16,i4,i18,i13,i1,i3,i4,i25,i12,i1,i3,i4,i10,i42,i2,i1,i3,i4,i9,i22,i2,i1,i3,i4,i7,i41,i2,i1,i3,i4,i13,i50,i2,i1,i3,i4,i11,i65,i2,i14,i30,i6,i9,i26,i0,i62,i19,i1,i3,i32,i1,.push 2 1568,i2,i59,i5,i12,i48,i2,i72,i2,i30,i5,i24,i6,i3,i30,i1,i3,i12,i27,i71,i2,i30,i5,i24,i6,i3,i30,i1,i3,i12,i25,i70,i2,i30,i5,i24,i6,i3,i30,i1,i3,i12,i34,i2,i69,i2,i30,i5,i24,i6,i3,i30,i1,i3,i12,i38,i2,i64,i2,i30,i5,i24,i6]

private theorem instructionsPart51_wf :
    instructionsPart51.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart51,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart52 : List Instr :=
  [i3,i30,i1,i3,i12,i37,i2,i68,i2,i30,i5,i24,i6,i3,i30,i1,i3,i39,i2,i35,i2,i67,i2,i21,i5,i7,i1,i15,i6,i63,i2,i52,i3,i28,i3,i13,i14,i24,i1,i3,i17,i6,i3,i8,i12,i6,i3,i18,i14,i6,i3,i25,i42,i2,i6,i3,i10,i22,i2,i6,i3,i9,i41,i2,i6,i3,i7,i50,i2,i6,i3,i13,i62,i2,i6,i3,i15,i12,i13,i8,i1,i3,i12,i10,i7,i1,i3,i16,i76,i19,i4,i25,i42,i2,i1,i3,i4,i10,i22,i2,i1,i3,i4,i9,i41,i2,i1,i3,i4,i7,i50,i2,i1,i3,i4,i13,i62,i2,i1,i3,i4,i11,i65,i2,i14,i30,i6,i9]

private theorem instructionsPart52_wf :
    instructionsPart52.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart52,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart53 : List Instr :=
  [i26,i0,i56,i19,i1,i3,i32,i1,i72,i2,i48,i2,i32,i2,i8,i5,i7,i1,i15,i6,i7,i3,i8,i7,i4,i1,i28,i25,i6,i3,i28,i3,i3,i15,i82,i15,i4,i27,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i34,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i38,i2,i69,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i35,i2,i68,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i67,i2,i8,i5,i7,i1,i15,i6,i63,i2,i17,i3,i15,i3,i12,i7,i10,i1,i3,i15,i7,i6,i3,.push 2 1600,i2,i75]

private theorem instructionsPart53_wf :
    instructionsPart53.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart53,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart54 : List Instr :=
  [i8,i28,i8,i14,i10,i1,i3,i28,i6,i3,i76,i2,i4,i6,i3,i42,i2,i18,i6,i3,i22,i2,i25,i6,i3,i41,i2,i10,i6,i3,i50,i2,i9,i6,i3,i9,i62,i2,i6,i3,i56,i2,i13,i6,i3,i16,i4,i76,i2,i12,i1,i3,i4,i42,i2,i10,i1,i3,i4,i22,i2,i4,i1,i3,i4,i41,i2,i24,i1,i3,i4,i9,i50,i2,i1,i3,i9,i12,i16,i62,i2,i1,i3,i4,i56,i2,i21,i1,i3,i4,i21,i65,i2,i14,i30,i6,i26,i82,i9,i1,i3,i32,i1,i32,i2,i4,i5,i27,i1,i14,i3,i52,i6,i3,i62,i2,i30,i4,i27,i72,i2,i17,i5,i10,i6,i3,i17,i1]

private theorem instructionsPart54_wf :
    instructionsPart54.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart54,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart55 : List Instr :=
  [i3,i4,i34,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i38,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i69,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i35,i2,i64,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i68,i2,i8,i5,i7,i1,i15,i6,i67,i2,i17,i3,i15,i3,i12,i7,i10,i1,i3,i15,i7,i6,i3,i76,i2,i8,i6,i3,i42,i2,i4,i6,i3,i22,i2,i18,i6,i3,i41,i2,i25,i6,i3,i50,i2,i10,i6,i3,i10,i9,i6,i3,i9,i56,i2,i6,i3,i21,i13,i6,i3,i16,i4,i76,i2,i13,i1,i3,i4,i42,i2,i12,i1]

private theorem instructionsPart55_wf :
    instructionsPart55.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart55,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart56 : List Instr :=
  [i3,i4,i22,i2,i10,i1,i3,i4,i41,i2,i4,i1,i3,i4,i50,i2,i24,i1,i3,i4,i9,i27,i1,i3,i9,i12,i16,i56,i2,i1,i3,i4,i11,i21,i1,i3,i16,i13,i26,i0,i48,i19,i4,i15,i29,i5,i3,i32,i1,i56,i2,i75,i40,i32,i2,i5,i12,i14,i4,i1,i3,i58,i6,i3,i50,i2,i52,i4,i34,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i38,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i35,i2,i69,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i64,i2,i8,i5,i7,i1,i15]

private theorem instructionsPart56_wf :
    instructionsPart56.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart56,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart57 : List Instr :=
  [i6,i68,i2,i17,i3,i15,i3,i12,i7,i10,i1,i3,i15,i7,i6,i3,i42,i2,i8,i6,i3,i22,i2,i4,i6,i3,i41,i2,i18,i6,i3,i24,i25,i6,i3,i10,i10,i6,i3,i8,i9,i6,i3,i9,i11,i6,i3,i16,i4,i42,i2,i13,i1,i3,i4,i22,i2,i12,i1,i3,i4,i41,i2,i10,i1,i3,i4,i27,i4,i1,i3,i4,i24,i24,i1,i3,i4,i9,i21,i1,i3,i9,i12,i16,i9,i1,i3,i16,i13,i26,i0,i15,i29,i4,i3,i32,i12,i15,i1,i4,i34,i2,i14,i32,i2,i30,.push 2 800,i19,i5,i10,i6,i3,i17,i1,i3,i4,i38,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3]

private theorem instructionsPart57_wf :
    instructionsPart57.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart57,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart58 : List Instr :=
  [i4,i37,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i35,i2,i70,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i69,i2,i8,i5,i7,i1,i15,i6,i64,i2,i17,i3,i15,i3,i12,i7,i10,i1,i3,i15,i7,i6,i3,i22,i2,i8,i6,i3,i41,i2,i4,i6,i3,i24,i18,i6,i3,i10,i25,i6,i3,i8,i10,i6,i3,i21,i9,i6,i3,i16,i4,i22,i2,i13,i1,i3,i4,i41,i2,i12,i1,i3,i4,i27,i10,i1,i3,i4,i24,i4,i1,i3,i4,i13,i24,i1,i3,i4,i9,i9,i1,i3,i16,i13,i26,i0,i15,i29,i4,i3,i32,i12,i15,i1,i4,i38,i2,i14,i32,i2]

private theorem instructionsPart58_wf :
    instructionsPart58.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart58,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart59 : List Instr :=
  [i30,.push 2 832,i19,i5,i10,i6,i3,i17,i1,i3,i4,i37,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i4,i35,i2,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i70,i2,i8,i5,i7,i1,i15,i6,i69,i2,i17,i3,i15,i3,i12,i7,i10,i1,i3,i15,i7,i6,i3,i41,i2,i8,i6,i3,i24,i4,i6,i3,i10,i18,i6,i3,i8,i25,i6,i3,i21,i10,i6,i3,i16,i4,i41,i2,i13,i1,i3,i4,i27,i12,i1,i3,i4,i24,i10,i1,i3,i4,i13,i4,i1,i3,i4,i11,i24,i1,i3,i16,i13,i26,i0,i15,i29,i4,i3,i32,i12,i15,i1,i4,i37,i2,i14,i32,i2,i30]

private theorem instructionsPart59_wf :
    instructionsPart59.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart59,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart60 : List Instr :=
  [i34,i19,i5,i10,i6,i3,i17,i1,i3,i4,i35,i2,i72,i2,i17,i5,i10,i6,i3,i17,i1,i3,i39,i2,i71,i2,i8,i5,i7,i1,i15,i6,i70,i2,i17,i3,i15,i3,i12,i7,i10,i1,i3,i15,i7,i6,i3,i24,i8,i6,i3,i10,i4,i6,i3,i8,i18,i6,i3,i21,i25,i6,i3,i16,i4,i27,i13,i1,i3,i4,i24,i12,i1,i3,i4,i13,i10,i1,i3,i4,i11,i4,i1,i3,i16,i13,i26,i0,i38,i19,i4,i15,i29,i5,i3,i32,i1,i35,i2,i39,i2,i72,i2,i8,i5,i7,i1,i73,i40,i6,i32,i2,i8,i5,i18,i1,i28,i6,i7,i3,i3,i15,i3,.push 2 832,i2,i58,i3,i4]

private theorem instructionsPart60_wf :
    instructionsPart60.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart60,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart61 : List Instr :=
  [i7,i71,i2,i17,i5,i10,i6,i3,i17,i1,i3,i16,i10,i8,i6,i3,i8,i4,i6,i3,i21,i18,i6,i3,i16,i4,i24,i13,i1,i3,i4,i13,i12,i1,i3,i4,i11,i10,i1,i3,i16,i13,i26,i0,i37,i19,i4,i15,i29,i5,i3,i32,i1,i32,i2,i39,i2,i12,i5,i7,i1,i58,i40,i6,i72,i2,i52,i14,i3,i12,i18,i25,i1,i3,i15,i3,.push 2 800,i2,i52,i7,i6,i3,i8,i8,i6,i3,i21,i4,i6,i3,i16,i4,i13,i13,i1,i3,i4,i11,i12,i1,i3,i16,i13,i26,i0,i35,i19,i4,i15,i29,i5,i3,i32,i1,i32,i2,i4,i5,i18,i1,i12,i9,i21,i1,i15,i18,i6,i7]

private theorem instructionsPart61_wf :
    instructionsPart61.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart61,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart62 : List Instr :=
  [i3,i9,i21,i6,i3,i11,i26,i28,i3,i3,i5,i39,i19,i29,i25,i3,i32,i4,i28,i40,i1,.op (.Swap swap12),i25,i11,i51,i66,i36,i25,i11,i47,i80,i36,i24,i39,i2,i51,i66,i36,i24,i39,i2,i47,i80,i36,i5,i35,i2,i51,i66,i36,i5,i35,i2,i47,i80,i36,i10,i37,i2,i51,i66,i36,i10,i37,i2,i47,i80,i36,i14,i38,i2,i51,i66,i36,i14,i38,i2,i47,i80,i36,i13,i34,i2,i51,i66,i36,i13,i34,i2,i47,i80,i36,i0,i10,i51,i66,i36,i0,i10,i47,i80,i36,i85,i2,i18,i51,i66,i36,i85,i2,i18,i47,i80,i36,i87,i2,i48,i2,i51,i66,i36,i87,i2,i48,i2,i47,i40,i23]

private theorem instructionsPart62_wf :
    instructionsPart62.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart62,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart63 : List Instr :=
  [i66,i49,i40,.push 2 10537,i44,i23,i48,i2,i18,.push 1 240,i54,i60,.push 2 2336,i19,i7,i61,i43,i10,i41,i54,i60,.push 2 2304,i19,i18,i34,i43,i34,i2,.push 1 208,i54,i60,.push 2 2272,i19,i34,i2,.push 1 48,i43,i38,i2,i42,i54,i60,.push 2 2240,i19,i38,i2,i38,i43,i37,i2,.push 1 176,i54,i60,i88,i19,i37,i2,.push 1 80,i43,i35,i2,i39,i54,i60,.push 2 2176,i19,i35,i2,i37,i43,i39,i2,.push 1 144,i54,i60,.push 2 2144,i19,i39,i2,.push 1 112,i43,i11,i35,i54,i60,i46,i19,i86,i46,i74,i23,.push 2 7627,i49,i40,i23,i48,i2,i87,i2,i0,i14,i51,i15,i29,i13,i26,i48,i19,i85,i2,i3,i0,i10,i29,i13,i26,i30,i51,i5,i3,i0,i24,i29,i13,i26,i52,i51,i21]

private theorem instructionsPart63_wf :
    instructionsPart63.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart63,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart64 : List Instr :=
  [i3,i34,i2,i5,i5,i29,i21,i26,i34,i19,i51,i7,i3,i38,i2,i5,i5,i29,i21,i26,i38,i19,i51,i24,i3,i37,i2,i5,i5,i29,i21,i26,i37,i19,i51,i14,i3,i35,i2,i5,i5,i29,i21,i26,i35,i19,i51,i27,i3,i39,i2,i5,i5,i29,i21,i26,i39,i19,i51,i4,i3,i87,i82,i29,i81,i2,i49,i44,i23,i0,.push 32 21888242871839275222246405745257275088696311157297823662689037894645226208583,.op .EQ,i5,.push 32 115792089237316195423570985008687907853269984665640564039457584007908834671663,.op .EQ,i60,.push 2 4795,i36,.push 2 717,i44,i23,i35,i46,i55,i78,i55,i2,i0,i11,i43,i16,.push 2 1600,i2,i54,i46,i2,i9,i43,i3,i21,i0,i21,i18,i1,i14,.op .ADDMOD,i16,i29,i13,i6,i9,i5,i35,i43,i6,i5,i22,i2,i6,i46,i2,i29,i51,i16,i29,i23,i45,i15]

private theorem instructionsPart64_wf :
    instructionsPart64.all (fun instruction => decide (WellFormed .Osaka instruction)) = true := by
  simp (config := { maxSteps := 200000 }) [instructionsPart64,WellFormed,YulEvmCompiler.plainOp]
  all_goals (repeat' apply And.intro)
  all_goals decide

private def instructionsPart65 : List Instr :=
  [i11,i47,i14,i3,i60,i0,i27,i6,i14,i25,i7,i1,i5,i88,i19,i0,i14,i47,i16,i29,i29,i5,i27,i6,i7,i25,i18,i1,i0,i14,i47,i29,i5,i7,i3,.push 2 2176,i2,i5,i3,i0,.push 2 2176,i19,i5,i47,i17,i47,i29,i29,i3,i5,i24,i6,i7,i27,i18,i1,i0,i14,i47,i29,i5,i7,i3,.push 2 2144,i2,i5,i3,i0,.push 2 2144,i19,i5,i47,i17,i47,i29,i29,i3,i56,i2,i7,i7,i14,i6,i15,i18,i1,i0,i14,i47,i29,i5,i7,i3,i46,i2,i5,i3,i0,i46,i19,i5,i47,i17,i47,i29,i29,i3,i55,i2,i3,i29,i0,i23,i23,.push 2 3068,i36,i16,i40,i83,i3,i0,i14,i36,i40,i81,i44]

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

/-- Direct lookup in uniform 128-instruction chunks. -/
def instructionChunks : List (List Instr) :=
  [instructionsPart0,instructionsPart1,instructionsPart2,instructionsPart3,instructionsPart4,instructionsPart5,instructionsPart6,instructionsPart7,instructionsPart8,instructionsPart9,instructionsPart10,instructionsPart11,instructionsPart12,instructionsPart13,instructionsPart14,instructionsPart15,instructionsPart16,instructionsPart17,instructionsPart18,instructionsPart19,instructionsPart20,instructionsPart21,instructionsPart22,instructionsPart23,instructionsPart24,instructionsPart25,instructionsPart26,instructionsPart27,instructionsPart28,instructionsPart29,instructionsPart30,instructionsPart31,instructionsPart32,instructionsPart33,instructionsPart34,instructionsPart35,instructionsPart36,instructionsPart37,instructionsPart38,instructionsPart39,instructionsPart40,instructionsPart41,instructionsPart42,instructionsPart43,instructionsPart44,instructionsPart45,instructionsPart46,instructionsPart47,instructionsPart48,instructionsPart49,instructionsPart50,instructionsPart51,instructionsPart52,instructionsPart53,instructionsPart54,instructionsPart55,instructionsPart56,instructionsPart57,instructionsPart58,instructionsPart59,instructionsPart60,instructionsPart61,instructionsPart62,instructionsPart63,instructionsPart64,instructionsPart65]
theorem instructionChunks_valid : CycleSubmission.ChunkLookup.valid instructionChunks = true := by decide
theorem instructionChunks_flatten : instructionChunks.flatten = instructions := by
  simp only [instructionChunks, List.flatten_cons, List.flatten_nil, instructions, instructionsPart66,instructionsPart67, List.append_nil]
theorem instruction_get (i : Nat) : instructions[i]? = CycleSubmission.ChunkLookup.get? instructionChunks i := by
  rw [← instructionChunks_flatten]
  exact (CycleSubmission.ChunkLookup.get?_eq instructionChunks instructionChunks_valid i).symm

theorem instructionCount : instructions.length = 8446 := by decide
theorem assembly : assemble instructions = bytecode := by rfl
def artifact : ProgramArtifact where
  code := bytecode
  instructions := instructions
  assembly_eq := assembly
theorem wellFormed : AllWellFormed artifact .Osaka := by
  unfold AllWellFormed artifact instructions
  simp only [List.all_append,instructionsPart0_wf,instructionsPart1_wf,instructionsPart2_wf,instructionsPart3_wf,instructionsPart4_wf,instructionsPart5_wf,instructionsPart6_wf,instructionsPart7_wf,instructionsPart8_wf,instructionsPart9_wf,instructionsPart10_wf,instructionsPart11_wf,instructionsPart12_wf,instructionsPart13_wf,instructionsPart14_wf,instructionsPart15_wf,instructionsPart16_wf,instructionsPart17_wf,instructionsPart18_wf,instructionsPart19_wf,instructionsPart20_wf,instructionsPart21_wf,instructionsPart22_wf,instructionsPart23_wf,instructionsPart24_wf,instructionsPart25_wf,instructionsPart26_wf,instructionsPart27_wf,instructionsPart28_wf,instructionsPart29_wf,instructionsPart30_wf,instructionsPart31_wf,instructionsPart32_wf,instructionsPart33_wf,instructionsPart34_wf,instructionsPart35_wf,instructionsPart36_wf,instructionsPart37_wf,instructionsPart38_wf,instructionsPart39_wf,instructionsPart40_wf,instructionsPart41_wf,instructionsPart42_wf,instructionsPart43_wf,instructionsPart44_wf,instructionsPart45_wf,instructionsPart46_wf,instructionsPart47_wf,instructionsPart48_wf,instructionsPart49_wf,instructionsPart50_wf,instructionsPart51_wf,instructionsPart52_wf,instructionsPart53_wf,instructionsPart54_wf,instructionsPart55_wf,instructionsPart56_wf,instructionsPart57_wf,instructionsPart58_wf,instructionsPart59_wf,instructionsPart60_wf,instructionsPart61_wf,instructionsPart62_wf,instructionsPart63_wf,instructionsPart64_wf,instructionsPart65_wf,instructionsPart66_wf,instructionsPart67_wf,Bool.and_self]
theorem bytecodeSize : bytecode.size = 10979 := by
  simp only [bytecode,ByteArray.size_append]
  decide
end CycleSubmission.Artifact
