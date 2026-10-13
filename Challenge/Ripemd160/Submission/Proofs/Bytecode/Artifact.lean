import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Bytecode
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Structural certificate for the frozen RIPEMD-160 artifact

The exact candidate has 5227 bytes, 3606 executable instructions and 280 data bytes, and SHA-256
`a86b46edbe4aa1fd4970c65890e5dc1cf323020fb51c241533160f155537ac65`. PUSH rows carry their typed width and value.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

private def submissionInstructionsChunk0 : List Instr :=
[
  .push 5 71077102108,
  .push 0 0,
  op 0x35,
  op 0x16,
  .push 1 246,
  op 0x57,
  op 0x36,
  .push 2 1000,
  op 0x03,
  .push 2 4841,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 255,
  op 0x02,
  .push 1 97,
  op 0x01,
  .push 2 4601,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 2 960,
  .push 2 968,
  op 0x35,
  op 0x82,
  op 0x18,
  op 0x5b,
  .push 1 32,
  op 0x82,
  op 0x03,
  op 0x35,
  op 0x83,
  op 0x18,
  op 0x17,
  .push 1 64,
  op 0x82,
  op 0x03,
  op 0x35,
  op 0x83,
  op 0x18,
  op 0x17,
  .push 1 96,
  op 0x82,
  op 0x03,
  op 0x91,
  op 0x35,
  op 0x83,
  op 0x18,
  op 0x17,
  op 0x81,
  .push 1 44,
  op 0x57,
  .push 1 246,
  op 0x57,
  .push 20 972889429405991776604892044862621566948497025487,
  op 0x5b,
  .push 0 0,
  op 0x52,
  op 0x59,
  .push 0 0,
  op 0xf3,
  op 0x5b,
  .push 2 4784,
  op 0x9c,
  op 0x36,
  op 0x18,
  .push 1 165,
  op 0x53,
  op 0x84,
  .push 1 188,
  op 0x53,
  op 0x36,
  .push 1 32,
  op 0x14,
  .push 2 494,
  op 0x57,
  .push 1 190,
  op 0x56,
  op 0x5b,
  .push 2 1084,
  op 0x90,
  .push 1 28,
  op 0x37,
  .push 19 2854495385411919762116571938898990272765493376,
  op 0x36,
  .push 1 3,
  op 0x1b,
  op 0x80,
  op 0x58,
  op 0x52,
  op 0x80,
  .push 2 666,
  op 0x52,
  .push 1 144,
  op 0x52,
  .push 1 128,
  .push 2 522,
  op 0x52,
  .push 1 54,
  op 0x52,
  .push 2 4784,
  op 0x9b,
  op 0x9a,
  .push 2 824,
  op 0x56,
  op 0x5b,
  .push 0 0,
  .push 1 157,
  op 0x52,
  op 0x36,
  .push 2 968,
  op 0x01,
  .push 1 63,
  op 0x17,
  op 0x9c,
  op 0x50,
  .push 1 128,
  op 0x8c,
  op 0x36,
  op 0x01,
  op 0x53,
  op 0x36,
  .push 1 3,
  op 0x1b,
  .push 1 89,
  op 0x8e,
  op 0x01,
  op 0x5b,
  op 0x81,
  op 0x81,
  op 0x53,
  .push 1 1,
  op 0x01,
  op 0x90,
  .push 1 8,
  op 0x1c,
  op 0x90,
  op 0x81,
  .push 1 219,
  op 0x57,
  op 0x50,
  op 0x50,
  .push 2 4757,
  op 0x9c,
  op 0x50,
  .push 2 457,
  op 0x56,
  op 0x5b
]

@[simp] private theorem submissionInstructionsChunk0_length : submissionInstructionsChunk0.length = 148 := by rfl

private def submissionInstructionsChunk1 : List Instr :=
[
  .push 30 1766820105243087041267848467410591083712559083657179364930612997358944255,
  .push 31 450552876409790643671482431940419874915447411150352389258589821042463539455,
  .push 2 4768,
  .push 2 1056,
  op 0x36,
  .push 0 0,
  op 0x82,
  op 0x37,
  .push 4 1732584193,
  .push 4 4023233417,
  .push 4 2562383102,
  .push 4 271733878,
  .push 4 3285377520,
  .push 13 475368975196266490007815979009,
  .push 13 1109194275457955143345843994625,
  .push 27 822752278660603021099785336477205875632903651089438293180284928,
  .push 27 822752278660603021055183846080144629349832214544141570168324096,
  .push 4 4294967295,
  .push 13 158456325065422163343096938498,
  .push 1 192,
  op 0x19,
  op 0x36,
  op 0x16,
  .push 2 104,
  op 0x57,
  op 0x5b,
  op 0x8b,
  .push 2 32,
  op 0x01,
  op 0x51,
  op 0x80,
  .push 1 8,
  op 0x1c,
  op 0x81,
  op 0x18,
  op 0x8f,
  op 0x16,
  .push 2 257,
  op 0x02,
  op 0x18,
  op 0x8f,
  op 0x81,
  op 0x80,
  .push 1 16,
  op 0x1c,
  op 0x18,
  op 0x16,
  .push 3 65537,
  op 0x02,
  op 0x18,
  .push 1 162,
  op 0x52,
  op 0x5b,
  op 0x8b,
  op 0x51,
  op 0x80,
  .push 1 8,
  op 0x1c,
  op 0x81,
  op 0x18,
  op 0x8f,
  op 0x16
]

@[simp] private theorem submissionInstructionsChunk1_length : submissionInstructionsChunk1.length = 62 := by rfl

private def submissionInstructionsChunk2 : List Instr :=
[
  .push 2 257,
  op 0x02,
  op 0x18,
  op 0x8f,
  op 0x81,
  op 0x80,
  .push 2 16,
  op 0x1c,
  op 0x18,
  op 0x16,
  .push 3 65537,
  op 0x02,
  op 0x18,
  .push 1 252,
  op 0x52,
  .push 2 146,
  op 0x51,
  .push 1 128,
  op 0x52,
  .push 1 178,
  op 0x51,
  .push 1 196,
  op 0x52,
  .push 1 236,
  op 0x51,
  .push 1 218,
  op 0x52,
  .push 2 268,
  op 0x51,
  .push 2 286,
  op 0x52,
  .push 1 176,
  op 0x51,
  .push 1 168,
  op 0x51,
  .push 2 266,
  op 0x51,
  .push 2 270,
  op 0x51,
  .push 1 142,
  op 0x51,
  .push 1 172,
  op 0x51,
  .push 1 232,
  op 0x51,
  .push 2 258,
  op 0x51,
  .push 1 228,
  op 0x51,
  .push 1 180,
  op 0x51,
  .push 2 262,
  op 0x51,
  .push 1 146,
  op 0x51,
  .push 1 134,
  op 0x51,
  .push 1 236,
  op 0x51,
  .push 1 224,
  op 0x51,
  .push 1 138,
  op 0x51,
  op 0x80,
  .push 2 900,
  op 0x52,
  op 0x86,
  .push 2 1008,
  op 0x52,
  op 0x82,
  .push 2 882,
  op 0x52,
  op 0x84,
  .push 1 126,
  op 0x52,
  op 0x84,
  .push 2 864,
  op 0x52,
  op 0x82,
  .push 2 846,
  op 0x52,
  op 0x80,
  .push 2 828,
  op 0x52,
  op 0x83,
  .push 2 936,
  op 0x52,
  op 0x83,
  .push 2 558,
  op 0x52,
  op 0x87,
  .push 2 540,
  op 0x52,
  op 0x85,
  .push 1 108,
  op 0x52,
  op 0x8d,
  .push 2 684,
  op 0x52,
  op 0x8f,
  op 0x58,
  op 0x52,
  op 0x8d,
  .push 2 414,
  op 0x52,
  .push 2 756,
  op 0x52,
  op 0x80,
  .push 2 522,
  op 0x52,
  op 0x8d,
  .push 1 90,
  op 0x52,
  op 0x87,
  .push 1 72,
  op 0x52,
  .push 1 54,
  op 0x52,
  op 0x85,
  .push 2 504,
  op 0x52,
  op 0x83,
  .push 2 1080,
  op 0x52,
  op 0x83,
  .push 2 486,
  op 0x52,
  op 0x88,
  .push 2 1062,
  op 0x52,
  .push 2 972,
  op 0x52,
  op 0x88,
  .push 2 216,
  op 0x52,
  op 0x83,
  .push 2 648,
  op 0x52,
  op 0x88,
  .push 2 630,
  op 0x52,
  op 0x83,
  .push 3 612,
  op 0x52,
  op 0x58,
  op 0x52,
  op 0x88,
  .push 2 288,
  op 0x52
]

@[simp] private theorem submissionInstructionsChunk2_length : submissionInstructionsChunk2.length = 149 := by rfl

private def submissionInstructionsChunk3 : List Instr :=
[
  .push 22 95780971281817308448866066055358605703522837925462015,
  op 0x16,
  .push 2 594,
  op 0x52,
  op 0x88,
  .push 2 1044,
  op 0x52,
  .push 2 720,
  op 0x52,
  .push 2 270,
  op 0x52,
  op 0x81,
  .push 2 396,
  op 0x52,
  op 0x80,
  op 0x58,
  op 0x52,
  .push 2 468,
  op 0x52,
  .push 1 18,
  op 0x52,
  .push 2 360,
  op 0x52,
  .push 1 198,
  op 0x52,
  .push 2 324,
  op 0x52,
  .push 1 252,
  op 0x52,
  .push 0 0,
  op 0x52,
  .push 2 450,
  op 0x52,
  .push 1 162,
  op 0x52,
  op 0x5b,
  op 0x88,
  op 0x81,
  op 0x02,
  .push 1 23,
  op 0x1c,
  op 0x88,
  op 0x88,
  op 0x8d,
  .push 4 1352829926,
  op 0x01,
  .push 2 486,
  op 0x51,
  op 0x01,
  op 0x8d,
  op 0x8d,
  op 0x8d,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x84,
  op 0x02,
  .push 1 25,
  op 0x1c,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x84,
  op 0x84,
  op 0x86,
  op 0x8f,
  op 0x86,
  op 0x19,
  op 0x17,
  op 0x84,
  op 0x18,
  .push 1 162,
  op 0x51,
  op 0x8e,
  op 0x01,
  op 0x01,
  .push 4 1352829926,
  op 0x01,
  op 0x16,
  op 0x02,
  .push 1 24,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x16,
  .push 4 1352829926,
  op 0x8e,
  op 0x86,
  op 0x02,
  .push 1 23,
  op 0x1c,
  op 0x93,
  op 0x83,
  op 0x85,
  op 0x19,
  op 0x17,
  op 0x83,
  op 0x18,
  op 0x01,
  .push 1 252,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x85,
  op 0x02,
  .push 1 24,
  op 0x1c,
  op 0x84,
  op 0x01,
  op 0x86,
  op 0x16,
  .push 1 144,
  op 0x1b,
  op 0x8e,
  op 0x17,
  op 0x90,
  .push 1 144,
  op 0x1b,
  op 0x8d,
  op 0x17,
  op 0x93,
  .push 1 144,
  op 0x1b,
  op 0x8f,
  op 0x17,
  op 0x91,
  op 0x85,
  op 0x02,
  .push 1 23,
  op 0x1c,
  .push 1 144,
  op 0x1b,
  op 0x8c,
  op 0x17,
  op 0x92,
  .push 1 144,
  op 0x1b,
  op 0x8b,
  op 0x17,
  .push 22 95780971281817308448866066055358605703522833630494720
]

@[simp] private theorem submissionInstructionsChunk3_length : submissionInstructionsChunk3.length = 145 := by rfl

private def submissionInstructionsChunk4 : List Instr :=
[
  .push 22 95780971281817308448866066055358605703522837925462015,
  .push 2 360,
  op 0x51,
  .push 1 23,
  op 0x8c,
  op 0x8a,
  .push 22 30169115476673038213297653277143730720156734734729216,
  op 0x98,
  op 0x86,
  op 0x8c,
  op 0x81,
  op 0x16,
  op 0x8c,
  op 0x17,
  op 0x8d,
  op 0x18,
  op 0x18,
  op 0x89,
  op 0x18,
  op 0x01,
  .push 1 54,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x81,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x81,
  op 0x02,
  op 0x83,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x96,
  op 0x87,
  op 0x89,
  op 0x88,
  op 0x16,
  op 0x17,
  op 0x87,
  op 0x18,
  op 0x89,
  op 0x8d,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 774,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 19,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x81,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x8f,
  op 0x82,
  op 0x9a,
  op 0x89,
  op 0x8d,
  op 0x85,
  op 0x8a,
  op 0x82,
  op 0x16,
  op 0x17,
  op 0x8a,
  op 0x18,
  op 0x18,
  op 0x18,
  op 0x01,
  op 0x85,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 18,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x8d,
  op 0x02,
  op 0x84,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x97,
  op 0x89,
  op 0x88,
  op 0x8a,
  op 0x81,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x01,
  .push 2 882,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x81,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x8b,
  op 0x82,
  op 0x9a,
  op 0x89,
  op 0x8d,
  op 0x89,
  op 0x16,
  op 0x8d,
  op 0x17,
  op 0x89,
  op 0x18,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x01,
  .push 2 396,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x8d,
  op 0x02,
  op 0x84,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x97,
  op 0x89,
  op 0x88,
  op 0x8a,
  op 0x81,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x01,
  .push 2 1080,
  op 0x51
]

@[simp] private theorem submissionInstructionsChunk4_length : submissionInstructionsChunk4.length = 199 := by rfl

private def submissionInstructionsChunk5 : List Instr :=
[
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  .push 1 25,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x81,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x8b,
  op 0x82,
  op 0x9a,
  op 0x8c,
  op 0x88,
  op 0x16,
  op 0x8c,
  op 0x17,
  op 0x8d,
  op 0x89,
  op 0x8c,
  op 0x18,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 1044,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x81,
  op 0x02,
  .push 1 26,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x81,
  op 0x02,
  op 0x84,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x97,
  op 0x8c,
  op 0x8a,
  op 0x8a,
  op 0x81,
  op 0x8b,
  op 0x16,
  op 0x17,
  op 0x8a,
  op 0x18,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 288,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  .push 1 24,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x81,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x81,
  op 0x99,
  op 0x8b,
  op 0x8b,
  op 0x81,
  op 0x89,
  op 0x16,
  op 0x17,
  op 0x8a,
  op 0x89,
  op 0x18,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 936,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x83,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x96,
  op 0x87,
  op 0x87,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x8c,
  op 0x18,
  op 0x87,
  op 0x8a,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 810,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 158456325065422163338801971201,
  op 0x09,
  .push 1 19,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x81,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x99,
  op 0x88,
  op 0x8c,
  op 0x88,
  op 0x18,
  op 0x18,
  op 0x83,
  op 0x8d,
  op 0x89,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 2 324,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 19,
  op 0x1c,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x83,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x96,
  op 0x88,
  op 0x87,
  op 0x89,
  op 0x81,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x8c,
  op 0x18,
  op 0x01,
  .push 2 864,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x85,
  op 0x16
]

@[simp] private theorem submissionInstructionsChunk5_length : submissionInstructionsChunk5.length = 217 := by rfl

private def submissionInstructionsChunk6 : List Instr :=
[
  .push 13 1109194275457955143375908765704,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x81,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x97,
  op 0x89,
  op 0x85,
  op 0x16,
  op 0x89,
  op 0x17,
  op 0x8a,
  op 0x88,
  op 0x18,
  op 0x18,
  op 0x85,
  op 0x18,
  op 0x01,
  .push 2 450,
  op 0x51,
  op 0x01,
  op 0x90,
  op 0x96,
  op 0x01,
  op 0x82,
  op 0x16,
  op 0x89,
  op 0x02,
  .push 1 27,
  op 0x1c,
  op 0x84,
  op 0x01,
  op 0x82,
  op 0x16,
  op 0x97,
  op 0x89,
  op 0x02,
  op 0x86,
  op 0x1c,
  op 0x82,
  op 0x16,
  op 0x8b,
  op 0x8f,
  .push 22 34535016170389834383797866734609369064725060249452544,
  op 0x96,
  op 0x8b,
  op 0x89,
  op 0x8d,
  op 0x89,
  op 0x16,
  op 0x18,
  op 0x85,
  op 0x89,
  op 0x16,
  op 0x17,
  op 0x85,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 1062,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 25,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x97,
  op 0x84,
  op 0x87,
  op 0x16,
  op 0x8a,
  op 0x18,
  op 0x85,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x87,
  op 0x8a,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 1 144,
  op 0x51,
  op 0x01,
  op 0x85,
  op 0x01,
  op 0x8c,
  op 0x80,
  .push 13 2376844875981332450021900025857,
  op 0x81,
  op 0x93,
  op 0x87,
  op 0x16,
  op 0x09,
  op 0x89,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x8c,
  op 0x88,
  op 0x82,
  op 0x16,
  op 0x8b,
  op 0x82,
  op 0x8b,
  op 0x16,
  op 0x18,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 990,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 20123953283308614743486684463105,
  op 0x09,
  .push 1 24,
  op 0x1c,
  op 0x89,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x96,
  op 0x8b,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x84,
  op 0x16,
  op 0x95,
  .push 4 1518500249,
  op 0x01,
  op 0x98,
  op 0x86,
  op 0x8b,
  op 0x88,
  op 0x17,
  op 0x89,
  op 0x88,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8b,
  op 0x89,
  op 0x16,
  op 0x17
]

@[simp] private theorem submissionInstructionsChunk6_length : submissionInstructionsChunk6.length = 184 := by rfl

private def submissionInstructionsChunk7 : List Instr :=
[
  op 0x01,
  .push 1 252,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x8b,
  op 0x02,
  .push 1 26,
  op 0x1c,
  op 0x82,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x99,
  op 0x8b,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x84,
  op 0x16,
  op 0x91,
  op 0x82,
  op 0x8b,
  op 0x87,
  op 0x18,
  op 0x89,
  op 0x82,
  op 0x17,
  op 0x16,
  op 0x18,
  op 0x8b,
  op 0x89,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 1 72,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x84,
  op 0x16,
  .push 13 9982748479121596290078236213249,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x87,
  op 0x8c,
  op 0x81,
  op 0x17,
  op 0x8a,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 1 198,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 25,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x89,
  op 0x85,
  op 0x17,
  op 0x8d,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 504,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 2376844875981332450086324535312,
  op 0x09,
  op 0x88,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x87,
  op 0x8c,
  op 0x89,
  op 0x17,
  op 0x8a,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 324,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x89,
  op 0x85,
  op 0x17,
  op 0x8d,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 684,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 475368975196266490020700880900,
  op 0x09,
  .push 1 25,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87
]

@[simp] private theorem submissionInstructionsChunk7_length : submissionInstructionsChunk7.length = 207 := by rfl

private def submissionInstructionsChunk8 : List Instr :=
[
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x87,
  op 0x8c,
  op 0x89,
  op 0x17,
  op 0x8a,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 1008,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 26,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x89,
  op 0x85,
  op 0x17,
  op 0x8d,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 954,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 1109194275457955143375908765704,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x87,
  op 0x8c,
  op 0x89,
  op 0x17,
  op 0x8a,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 450,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 26,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x89,
  op 0x85,
  op 0x17,
  op 0x8d,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 1 36,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 9982748479121596290348819152960,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x94,
  op 0x86,
  op 0x8a,
  op 0x16,
  op 0x8a,
  op 0x87,
  op 0x17,
  op 0x88,
  op 0x87,
  op 0x18,
  op 0x16,
  op 0x87,
  op 0x18,
  op 0x17,
  op 0x01,
  .push 2 828,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 18,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x90,
  op 0x81,
  op 0x87,
  op 0x17,
  op 0x8a,
  op 0x86,
  op 0x18,
  op 0x16,
  op 0x82,
  op 0x18,
  op 0x8a,
  op 0x88,
  op 0x16,
  op 0x17,
  op 0x01,
  .push 2 486,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x8f,
  op 0x8d
]

@[simp] private theorem submissionInstructionsChunk8_length : submissionInstructionsChunk8.length = 212 := by rfl

private def submissionInstructionsChunk9 : List Instr :=
[
  .push 13 2376844875981332450021900025857,
  op 0x81,
  op 0x93,
  op 0x87,
  op 0x16,
  op 0x09,
  op 0x89,
  op 0x1c,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x97,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x96,
  op 0x87,
  op 0x8c,
  op 0x81,
  op 0x17,
  op 0x8a,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x16,
  op 0x17,
  op 0x01,
  op 0x84,
  op 0x01,
  .push 22 40945789247971450477386360121479348807026276516919705,
  op 0x9a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x87,
  op 0x8a,
  op 0x8e,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x8e,
  op 0x82,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 666,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 25,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x94,
  op 0x85,
  op 0x85,
  op 0x18,
  op 0x8a,
  op 0x88,
  op 0x88,
  op 0x16,
  op 0x18,
  op 0x88,
  op 0x87,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 1 126,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  .push 13 9982748479121596290348819152960,
  op 0x8e,
  op 0x91,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 25,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x97,
  op 0x86,
  op 0x8a,
  op 0x8a,
  op 0x16,
  op 0x18,
  op 0x8a,
  op 0x86,
  op 0x18,
  op 0x16,
  op 0x89,
  op 0x86,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 558,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x8d,
  op 0x8c,
  op 0x91,
  op 0x84,
  op 0x16,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x84,
  op 0x01,
  op 0x82,
  op 0x16,
  op 0x94,
  op 0x89,
  op 0x02,
  op 0x86,
  op 0x1c,
  op 0x82,
  op 0x16,
  op 0x8c,
  op 0x8a,
  op 0x81,
  .push 23 136726760529788758926252426176837954510549114783656865,
  op 0x97,
  op 0x84,
  op 0x8d,
  op 0x19,
  op 0x8b,
  op 0x17,
  op 0x18
]

@[simp] private theorem submissionInstructionsChunk9_length : submissionInstructionsChunk9.length = 180 := by rfl

private def submissionInstructionsChunk10 : List Instr :=
[
  op 0x01,
  .push 2 972,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x8d,
  op 0x02,
  op 0x8a,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x9a,
  op 0x8b,
  op 0x8d,
  op 0x8b,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 2 306,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  .push 13 4912146077028087063507156074528,
  op 0x09,
  .push 1 24,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x97,
  op 0x81,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x8c,
  op 0x19,
  op 0x8a,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 1 162,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x81,
  op 0x02,
  .push 1 27,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x81,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x8c,
  op 0x8a,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 1 18,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x8f,
  op 0x82,
  op 0x93,
  op 0x83,
  op 0x8d,
  op 0x19,
  op 0x8b,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 2 828,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 19,
  op 0x1c,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x8d,
  op 0x02,
  op 0x8a,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x8a,
  op 0x19,
  op 0x17,
  op 0x8c,
  op 0x18,
  op 0x01,
  .push 2 612,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  op 0x88,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x92,
  op 0x83,
  op 0x8c,
  op 0x19,
  op 0x8a,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 2 936,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 20,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x8c,
  op 0x8a,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 2 468,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16
]

@[simp] private theorem submissionInstructionsChunk10_length : submissionInstructionsChunk10.length = 220 := by rfl

private def submissionInstructionsChunk11 : List Instr :=
[
  .push 14 162100820541926873095598711505920,
  op 0x09,
  .push 1 27,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x81,
  op 0x92,
  op 0x83,
  op 0x8c,
  op 0x19,
  op 0x8a,
  op 0x17,
  op 0x18,
  op 0x01,
  op 0x84,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 19,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x8c,
  op 0x8a,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 1 234,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 4912146077028087063374012088321,
  op 0x09,
  .push 1 24,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x90,
  op 0x81,
  op 0x8a,
  op 0x19,
  op 0x88,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 1 54,
  op 0x51,
  op 0x01,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 20,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x97,
  op 0x88,
  op 0x8a,
  op 0x88,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 2 414,
  op 0x51,
  op 0x01,
  op 0x85,
  op 0x01,
  op 0x8e,
  op 0x8d,
  .push 13 158456325065422163338801971201,
  op 0x81,
  op 0x93,
  op 0x87,
  op 0x16,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x97,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x83,
  op 0x8c,
  op 0x19,
  op 0x8a,
  op 0x17,
  op 0x18,
  op 0x01,
  .push 1 198,
  op 0x51,
  op 0x01,
  .push 22 45805601672572416830120737830960963807809187239029665,
  op 0x97,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x8c,
  op 0x8f,
  op 0x18,
  op 0x8a,
  op 0x8e,
  op 0x8e,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x8f,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 576
]

@[simp] private theorem submissionInstructionsChunk11_length : submissionInstructionsChunk11.length = 185 := by rfl

private def submissionInstructionsChunk12 : List Instr :=
[
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x90,
  op 0x81,
  op 0x8c,
  op 0x81,
  op 0x89,
  op 0x16,
  op 0x8c,
  op 0x18,
  op 0x8e,
  op 0x8a,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 702,
  op 0x51,
  op 0x01,
  op 0x85,
  op 0x01,
  op 0x8e,
  op 0x8e,
  .push 13 475368975196266490020700880900,
  op 0x8f,
  op 0x93,
  op 0x87,
  op 0x16,
  op 0x09,
  .push 1 27,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x8c,
  op 0x8f,
  op 0x18,
  op 0x8a,
  op 0x8e,
  op 0x8e,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x8f,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 1 90,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 27,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x94,
  .push 4 541184315,
  op 0x01,
  op 0x90,
  op 0x86,
  op 0x8a,
  op 0x86,
  op 0x17,
  op 0x18,
  op 0x8a,
  op 0x86,
  op 0x16,
  op 0x87,
  op 0x18,
  op 0x16,
  op 0x8a,
  op 0x18,
  op 0x01,
  .push 2 792,
  op 0x51,
  op 0x01,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x97,
  op 0x84,
  op 0x87,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x85,
  op 0x88,
  op 0x17,
  op 0x8b,
  op 0x18,
  op 0x16,
  op 0x87,
  op 0x18,
  op 0x01,
  .push 2 900,
  op 0x51,
  op 0x01,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8f,
  op 0x8d,
  op 0x91,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x87,
  op 0x87,
  op 0x8d,
  op 0x16,
  op 0x18,
  op 0x87,
  op 0x8d,
  op 0x17,
  op 0x8a,
  op 0x18,
  op 0x16,
  op 0x8c,
  op 0x18,
  op 0x01,
  .push 2 594,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 19,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x87,
  op 0x8a,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x89,
  op 0x17,
  op 0x18,
  op 0x16,
  op 0x89
]

@[simp] private theorem submissionInstructionsChunk12_length : submissionInstructionsChunk12.length = 228 := by rfl

private def submissionInstructionsChunk13 : List Instr :=
[
  op 0x18,
  op 0x01,
  .push 2 630,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 14 80971182108430725466132102251008,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x88,
  op 0x8c,
  op 0x88,
  op 0x17,
  op 0x18,
  op 0x8c,
  op 0x88,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x8c,
  op 0x18,
  op 0x01,
  .push 1 54,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 19,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x88,
  op 0x8c,
  op 0x81,
  op 0x89,
  op 0x17,
  op 0x18,
  op 0x8c,
  op 0x89,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 2 738,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 14 80971182108430725466132102251008,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x81,
  op 0x96,
  op 0x8b,
  op 0x87,
  op 0x81,
  op 0x17,
  op 0x8a,
  op 0x18,
  op 0x89,
  op 0x89,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 2 450,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 24,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x8a,
  op 0x87,
  op 0x8a,
  op 0x16,
  op 0x18,
  op 0x8c,
  op 0x8a,
  op 0x89,
  op 0x17,
  op 0x18,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x01,
  .push 2 378,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 2376844875981332450021900025857,
  op 0x09,
  .push 1 24,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x88,
  op 0x8c,
  op 0x88,
  op 0x17,
  op 0x18,
  op 0x8c,
  op 0x88,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x16,
  op 0x8c,
  op 0x18,
  op 0x01,
  .push 1 198,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 24,
  op 0x1c,
  op 0x8a,
  op 0x01
]

@[simp] private theorem submissionInstructionsChunk13_length : submissionInstructionsChunk13.length = 203 := by rfl

private def submissionInstructionsChunk14 : List Instr :=
[
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x88,
  op 0x8c,
  op 0x81,
  op 0x89,
  op 0x17,
  op 0x18,
  op 0x8c,
  op 0x89,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 2 846,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 475368975196266490020700880900,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x81,
  op 0x96,
  op 0x8b,
  op 0x87,
  op 0x81,
  op 0x17,
  op 0x8a,
  op 0x18,
  op 0x89,
  op 0x89,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 1 252,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x99,
  op 0x88,
  op 0x8c,
  op 0x8a,
  op 0x89,
  op 0x17,
  op 0x18,
  op 0x8c,
  op 0x89,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 2 648,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 14 80971182108430725463937373962241,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x94,
  op 0x86,
  op 0x8a,
  op 0x86,
  op 0x17,
  op 0x18,
  op 0x8a,
  op 0x86,
  op 0x16,
  op 0x87,
  op 0x18,
  op 0x16,
  op 0x8a,
  op 0x18,
  op 0x01,
  .push 1 162,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x82,
  op 0x16,
  op 0x89,
  op 0x02,
  .push 1 25,
  op 0x1c,
  op 0x87,
  op 0x01,
  op 0x82,
  op 0x16,
  op 0x97,
  op 0x89,
  op 0x02,
  op 0x86,
  op 0x1c,
  op 0x82,
  op 0x16,
  op 0x8b,
  op 0x8f,
  .push 4 2400959708,
  op 0x99,
  op 0x86,
  op 0x8c,
  op 0x8a,
  op 0x18,
  op 0x17,
  op 0x84,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x8c,
  op 0x88,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 1 108,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x94,
  op 0x85,
  op 0x8a,
  op 0x88,
  op 0x18,
  op 0x86,
  op 0x17,
  op 0x16,
  op 0x85,
  op 0x88,
  op 0x16,
  op 0x18,
  op 0x8a,
  op 0x18,
  op 0x01,
  .push 2 1026,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01
]

@[simp] private theorem submissionInstructionsChunk14_length : submissionInstructionsChunk14.length = 215 := by rfl

private def submissionInstructionsChunk15 : List Instr :=
[
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x90,
  op 0x84,
  op 0x8a,
  op 0x16,
  op 0x87,
  op 0x18,
  op 0x82,
  op 0x88,
  op 0x8c,
  op 0x18,
  op 0x87,
  op 0x17,
  op 0x16,
  op 0x18,
  op 0x01,
  .push 2 342,
  op 0x51,
  op 0x01,
  .push 4 2840853838,
  op 0x98,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 21,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x8f,
  op 0x8f,
  op 0x85,
  op 0x93,
  op 0x98,
  op 0x8f,
  op 0x8a,
  op 0x8f,
  op 0x82,
  op 0x16,
  op 0x17,
  op 0x8c,
  op 0x18,
  op 0x8f,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 396,
  op 0x51,
  op 0x01,
  op 0x8c,
  op 0x01,
  op 0x87,
  op 0x16,
  op 0x8e,
  op 0x02,
  .push 1 24,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x87,
  op 0x16,
  op 0x9c,
  op 0x8e,
  op 0x02,
  op 0x8b,
  op 0x1c,
  op 0x87,
  op 0x16,
  op 0x94,
  op 0x8f,
  op 0x80,
  op 0x8c,
  op 0x16,
  op 0x87,
  op 0x17,
  op 0x18,
  op 0x8b,
  op 0x18,
  op 0x8e,
  op 0x18,
  op 0x01,
  .push 2 522,
  op 0x51,
  op 0x01,
  op 0x8c,
  op 0x01,
  op 0x87,
  op 0x16,
  .push 13 1109194275457955143375908765704,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x88,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x98,
  op 0x8d,
  op 0x02,
  op 0x8a,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x97,
  op 0x8e,
  op 0x8d,
  op 0x8a,
  op 0x82,
  op 0x82,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x8b,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 720,
  op 0x51,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x84,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x8d,
  op 0x02,
  op 0x8a,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x93,
  op 0x8e,
  op 0x8a,
  op 0x86,
  op 0x82,
  op 0x82,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x01,
  .push 2 756,
  op 0x51,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  .push 1 21,
  op 0x1c,
  op 0x86,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x96,
  op 0x8b,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x84,
  op 0x16,
  op 0x95,
  op 0x86,
  op 0x8b,
  op 0x8e,
  op 0x16,
  op 0x17,
  op 0x8b,
  op 0x8e,
  op 0x18,
  op 0x89,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 1 252,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x8b,
  op 0x02,
  .push 1 27,
  op 0x1c,
  op 0x82,
  op 0x01
]

@[simp] private theorem submissionInstructionsChunk15_length : submissionInstructionsChunk15.length = 225 := by rfl

private def submissionInstructionsChunk16 : List Instr :=
[
  op 0x84,
  op 0x16,
  op 0x99,
  op 0x8b,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x84,
  op 0x16,
  op 0x91,
  op 0x8c,
  op 0x88,
  op 0x84,
  op 0x82,
  op 0x8b,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x8c,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 432,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x8b,
  op 0x02,
  .push 1 25,
  op 0x1c,
  op 0x86,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x96,
  op 0x8b,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x84,
  op 0x16,
  op 0x95,
  op 0x8c,
  op 0x8b,
  op 0x81,
  op 0x81,
  op 0x16,
  op 0x89,
  op 0x17,
  op 0x18,
  op 0x89,
  op 0x18,
  op 0x18,
  op 0x01,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 20,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x90,
  op 0x8b,
  op 0x82,
  op 0x88,
  op 0x8e,
  op 0x16,
  op 0x17,
  op 0x88,
  op 0x18,
  op 0x8b,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 1 216,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  .push 13 9982748479121596290348819152960,
  op 0x8e,
  op 0x91,
  op 0x85,
  op 0x16,
  op 0x09,
  .push 1 26,
  op 0x1c,
  op 0x85,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8c,
  op 0x8f,
  op 0x82,
  op 0x97,
  op 0x8c,
  op 0x8f,
  op 0x18,
  op 0x8f,
  op 0x8e,
  op 0x16,
  op 0x85,
  op 0x17,
  op 0x8b,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 1 162,
  op 0x51,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x84,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9b,
  op 0x8d,
  op 0x02,
  op 0x8a,
  op 0x1c,
  op 0x86,
  op 0x16,
  op 0x93,
  op 0x8e,
  op 0x8a,
  op 0x16,
  op 0x85,
  op 0x17,
  op 0x8a,
  op 0x18,
  op 0x8f,
  op 0x8e,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 540,
  op 0x51,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  .push 1 20,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x83,
  op 0x16,
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x8d,
  op 0x8c,
  op 0x81,
  op 0x81,
  op 0x16,
  op 0x8a,
  op 0x17,
  op 0x18,
  op 0x8a,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 972,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 20,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x9a,
  op 0x8c,
  op 0x02,
  op 0x89,
  op 0x1c,
  op 0x85,
  op 0x16,
  op 0x92,
  op 0x8d,
  op 0x89,
  op 0x81,
  op 0x81,
  op 0x16,
  op 0x86,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x8c
]

@[simp] private theorem submissionInstructionsChunk16_length : submissionInstructionsChunk16.length = 233 := by rfl

private def submissionInstructionsChunk17 : List Instr :=
[
  op 0x18,
  op 0x01,
  .push 2 918,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 13 1109194275457955143375908765704,
  op 0x09,
  .push 1 21,
  op 0x1c,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x95,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x94,
  op 0x8b,
  op 0x8a,
  op 0x81,
  op 0x81,
  op 0x16,
  op 0x88,
  op 0x17,
  op 0x18,
  op 0x88,
  op 0x18,
  op 0x18,
  op 0x01,
  .push 2 594,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 22,
  op 0x1c,
  op 0x81,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x98,
  op 0x8a,
  op 0x02,
  op 0x87,
  op 0x1c,
  op 0x8a,
  op 0x87,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x8c,
  op 0x8b,
  op 0x83,
  op 0x19,
  op 0x8a,
  op 0x17,
  op 0x18,
  .push 0 0,
  op 0x51,
  op 0x85,
  op 0x01,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 25,
  op 0x1c,
  op 0x87,
  op 0x01,
  op 0x8d,
  op 0x16,
  .push 2 612,
  op 0x51,
  op 0x8b,
  op 0x82,
  op 0x8e,
  op 0x85,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x01,
  op 0x01,
  op 0x88,
  op 0x01,
  op 0x8e,
  op 0x16,
  op 0x8d,
  op 0x02,
  .push 1 28,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x8c,
  op 0x8e,
  op 0x02,
  op 0x8b,
  op 0x1c,
  op 0x9b,
  op 0x81,
  op 0x83,
  op 0x8e,
  op 0x19,
  op 0x17,
  op 0x18,
  op 0x85,
  op 0x01,
  .push 1 198,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x8f,
  op 0x16,
  op 0x8e,
  op 0x02,
  .push 1 27,
  op 0x1c,
  op 0x83,
  op 0x01,
  op 0x93,
  .push 2 144,
  op 0x1c,
  op 0x01,
  op 0x96,
  op 0x50,
  op 0x8c,
  op 0x02,
  op 0x93,
  op 0x50,
  op 0x96,
  .push 2 144,
  op 0x1c,
  op 0x01,
  op 0x94,
  .push 2 144,
  op 0x1c,
  op 0x92,
  op 0x50,
  .push 1 144,
  op 0x1c,
  op 0x97,
  .push 1 144,
  op 0x1c,
  op 0x95,
  op 0x1c,
  op 0x01,
  op 0x8f,
  op 0x01,
  op 0x88,
  op 0x16,
  op 0x9f,
  op 0x01,
  op 0x87,
  op 0x16,
  op 0x9f,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x9a,
  op 0x01,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x99,
  op 0x01,
  op 0x01,
  op 0x82,
  op 0x16,
  op 0x98,
  op 0x50,
  op 0x8c,
  op 0x56,
  op 0x5b,
  op 0x91,
  op 0x85,
  .push 1 2,
  op 0x1b,
  op 0x81,
  op 0x81,
  op 0x17,
  .push 1 9,
  op 0x81,
  op 0x92,
  op 0x05,
  op 0x01,
  op 0x18,
  op 0x18,
  op 0x91,
  .push 1 251,
  op 0x87,
  op 0x01,
  op 0x80,
  op 0x36,
  op 0x03,
  op 0x80,
  op 0x36,
  op 0x1d,
  op 0x16,
  op 0x01,
  .push 1 32,
  op 0x81,
  op 0x03,
  op 0x94,
  op 0x50,
  op 0x96,
  op 0x91,
  op 0x84,
  op 0x11,
  .push 2 4687,
  op 0x57
]

@[simp] private theorem submissionInstructionsChunk17_length : submissionInstructionsChunk17.length = 220 := by rfl

private def submissionInstructionsChunk18 : List Instr :=
[
  .push 2 4713,
  op 0x56,
  op 0x5b,
  .push 1 251,
  op 0x5b,
  .push 32 43592315948166097100638488473858977074172229521182329991325208097096707629152,
  op 0x80,
  op 0x19,
  .push 1 32,
  op 0x83,
  op 0x03,
  .push 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
  .push 0 0,
  .push 0 0,
  .push 1 33,
  op 0x36,
  op 0x10,
  .push 2 4713,
  op 0x57,
  op 0x5b,
  op 0x81,
  .push 1 32,
  op 0x01,
  op 0x91,
  op 0x35,
  op 0x85,
  op 0x84,
  op 0x17,
  op 0x87,
  op 0x81,
  op 0x03,
  op 0x18,
  op 0x84,
  op 0x18,
  op 0x93,
  op 0x18,
  op 0x17,
  op 0x83,
  op 0x82,
  op 0x10,
  .push 2 4687,
  op 0x57,
  op 0x5b,
  op 0x81,
  op 0x35,
  op 0x83,
  op 0x18,
  op 0x84,
  op 0x83,
  op 0x03,
  .push 1 3,
  op 0x1b,
  op 0x1c,
  op 0x17,
  op 0x36,
  op 0x87,
  op 0x03,
  .push 2 4553,
  op 0x57,
  .push 1 246,
  op 0x57,
  .push 1 20,
  .push 1 15,
  op 0x36,
  .push 3 14357627,
  op 0x04,
  op 0x16,
  op 0x81,
  op 0x02,
  op 0x38,
  op 0x03,
  .push 1 12,
  op 0x39,
  op 0x59,
  .push 0 0,
  op 0xf3,
  op 0x5b,
  op 0x8b,
  .push 1 128,
  op 0x01,
  op 0x59,
  op 0x10,
  .push 2 4784,
  op 0x57,
  op 0x5b,
  op 0x9a,
  .push 1 64,
  op 0x01,
  op 0x59,
  op 0x81,
  op 0x14,
  .push 1 129,
  op 0x57,
  op 0x9a,
  .push 2 457,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  .push 1 16,
  op 0x52,
  .push 1 12,
  op 0x52,
  .push 1 8,
  op 0x52,
  .push 1 4,
  op 0x52,
  .push 0 0,
  op 0x52,
  .push 1 16,
  op 0x51,
  .push 2 257,
  op 0x81,
  op 0x80,
  .push 1 8,
  op 0x1c,
  op 0x18,
  op 0x85,
  op 0x16,
  op 0x02,
  op 0x18,
  op 0x80,
  op 0x81,
  .push 1 16,
  op 0x1c,
  op 0x18,
  op 0x85,
  op 0x16,
  .push 3 65537,
  op 0x02,
  op 0x18,
  .push 0 0,
  op 0x52,
  .push 1 32,
  .push 0 0,
  op 0xf3,
  op 0x5b,
  op 0x36,
  .push 1 1
]

@[simp] private theorem submissionInstructionsChunk18_length : submissionInstructionsChunk18.length = 143 := by rfl

private def submissionInstructionsChunk19 : List Instr :=
[
  .push 17 342276208914615837337402008677671501826,
  op 0x36,
  op 0x1c,
  op 0x16,
  .push 2 4604,
  op 0x57,
  .push 2 256,
  op 0x14,
  .push 2 376,
  op 0x36,
  op 0x14,
  op 0x01,
  .push 2 4601,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 232,
  op 0x1d,
  op 0x36,
  .push 3 2127393,
  op 0x02,
  op 0x18,
  .push 1 246,
  op 0x57,
  .push 20 95383801997447390147238369573240532004699299169,
  op 0x36,
  op 0x1c,
  .push 20 802931186561056611446976448233794645126013734992,
  op 0x18,
  .push 1 98,
  op 0x56
]

@[simp] private theorem submissionInstructionsChunk19_length : submissionInstructionsChunk19.length = 31 := by rfl

def submissionInstructions : List Instr :=
submissionInstructionsChunk0
 ++ submissionInstructionsChunk1
 ++ submissionInstructionsChunk2
 ++ submissionInstructionsChunk3
 ++ submissionInstructionsChunk4
 ++ submissionInstructionsChunk5
 ++ submissionInstructionsChunk6
 ++ submissionInstructionsChunk7
 ++ submissionInstructionsChunk8
 ++ submissionInstructionsChunk9
 ++ submissionInstructionsChunk10
 ++ submissionInstructionsChunk11
 ++ submissionInstructionsChunk12
 ++ submissionInstructionsChunk13
 ++ submissionInstructionsChunk14
 ++ submissionInstructionsChunk15
 ++ submissionInstructionsChunk16
 ++ submissionInstructionsChunk17
 ++ submissionInstructionsChunk18
 ++ submissionInstructionsChunk19

theorem referenceInstructions_count : submissionInstructions.length = 3606 := by
  simp only [submissionInstructions, List.length_append, submissionInstructionsChunk0_length, submissionInstructionsChunk1_length, submissionInstructionsChunk2_length, submissionInstructionsChunk3_length, submissionInstructionsChunk4_length, submissionInstructionsChunk5_length, submissionInstructionsChunk6_length, submissionInstructionsChunk7_length, submissionInstructionsChunk8_length, submissionInstructionsChunk9_length, submissionInstructionsChunk10_length, submissionInstructionsChunk11_length, submissionInstructionsChunk12_length, submissionInstructionsChunk13_length, submissionInstructionsChunk14_length, submissionInstructionsChunk15_length, submissionInstructionsChunk16_length, submissionInstructionsChunk17_length, submissionInstructionsChunk18_length, submissionInstructionsChunk19_length]

private theorem submissionInstructionsChunk0_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk0 = [
  100, 16, 140, 134, 130, 28, 95, 53, 22, 96, 246, 87, 54, 97, 3, 232, 3, 97, 18, 233, 87, 95, 53, 96, 255, 2, 96, 97, 1, 97, 17, 249, 87, 95, 53, 97, 3, 192, 97, 3, 200, 53, 130, 24, 91, 96, 32, 130,
  3, 53, 131, 24, 23, 96, 64, 130, 3, 53, 131, 24, 23, 96, 96, 130, 3, 145, 53, 131, 24, 23, 129, 96, 44, 87, 96, 246, 87, 115, 170, 105, 222, 238, 154, 137, 34, 233, 47, 129, 5, 224, 7, 247, 97, 16, 243, 129,
  233, 207, 91, 95, 82, 89, 95, 243, 91, 97, 18, 176, 156, 54, 24, 96, 165, 83, 132, 96, 188, 83, 54, 96, 32, 20, 97, 1, 238, 87, 96, 190, 86, 91, 97, 4, 60, 144, 96, 28, 55, 114, 128, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 54, 96, 3, 27, 128, 88, 82, 128, 97, 2, 154, 82, 96, 144, 82, 96, 128, 97, 2, 10, 82, 96, 54, 82, 97, 18, 176, 155, 154, 97, 3, 56, 86, 91, 95,
  96, 157, 82, 54, 97, 3, 200, 1, 96, 63, 23, 156, 80, 96, 128, 140, 54, 1, 83, 54, 96, 3, 27, 96, 89, 142, 1, 91, 129, 129, 83, 96, 1, 1, 144, 96, 8, 28, 144, 129, 96, 219, 87, 80, 80, 97, 18, 149,
  156, 80, 97, 1, 201, 86, 91,
] := by decide

private theorem submissionInstructionsChunk1_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk1 = [
  125, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 126, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0,
  255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 97, 18, 160, 97, 4, 32, 54, 95, 130, 55, 99, 103, 69, 35, 1, 99, 239, 205, 171, 137, 99, 152, 186, 220, 254, 99, 16, 50, 84, 118, 99, 195, 210,
  225, 240, 108, 6, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 1, 108, 14, 0, 0, 0, 14, 0, 0, 0, 1, 0, 0, 0, 1, 122, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 122, 1, 255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 255, 255, 255, 255, 108, 2, 0, 0, 0,
  2, 0, 0, 0, 2, 0, 0, 0, 2, 96, 192, 25, 54, 22, 97, 0, 104, 87, 91, 139, 97, 0, 32, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1,
  0, 1, 2, 24, 96, 162, 82, 91, 139, 81, 128, 96, 8, 28, 129, 24, 143, 22,
] := by decide

private theorem submissionInstructionsChunk2_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk2 = [
  97, 1, 1, 2, 24, 143, 129, 128, 97, 0, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24, 96, 252, 82, 97, 0, 146, 81, 96, 128, 82, 96, 178, 81, 96, 196, 82, 96, 236, 81, 96, 218, 82, 97, 1, 12, 81, 97, 1,
  30, 82, 96, 176, 81, 96, 168, 81, 97, 1, 10, 81, 97, 1, 14, 81, 96, 142, 81, 96, 172, 81, 96, 232, 81, 97, 1, 2, 81, 96, 228, 81, 96, 180, 81, 97, 1, 6, 81, 96, 146, 81, 96, 134, 81, 96, 236, 81,
  96, 224, 81, 96, 138, 81, 128, 97, 3, 132, 82, 134, 97, 3, 240, 82, 130, 97, 3, 114, 82, 132, 96, 126, 82, 132, 97, 3, 96, 82, 130, 97, 3, 78, 82, 128, 97, 3, 60, 82, 131, 97, 3, 168, 82, 131, 97, 2,
  46, 82, 135, 97, 2, 28, 82, 133, 96, 108, 82, 141, 97, 2, 172, 82, 143, 88, 82, 141, 97, 1, 158, 82, 97, 2, 244, 82, 128, 97, 2, 10, 82, 141, 96, 90, 82, 135, 96, 72, 82, 96, 54, 82, 133, 97, 1, 248,
  82, 131, 97, 4, 56, 82, 131, 97, 1, 230, 82, 136, 97, 4, 38, 82, 97, 3, 204, 82, 136, 97, 0, 216, 82, 131, 97, 2, 136, 82, 136, 97, 2, 118, 82, 131, 98, 0, 2, 100, 82, 88, 82, 136, 97, 1, 32, 82,
] := by decide

private theorem submissionInstructionsChunk3_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk3 = [
  117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 22, 97, 2, 82, 82, 136, 97, 4, 20, 82, 97, 2, 208, 82, 97, 1, 14, 82, 129, 97, 1, 140, 82, 128, 88,
  82, 97, 1, 212, 82, 96, 18, 82, 97, 1, 104, 82, 96, 198, 82, 97, 1, 68, 82, 96, 252, 82, 95, 82, 97, 1, 194, 82, 96, 162, 82, 91, 136, 129, 2, 96, 23, 28, 136, 136, 141, 99, 80, 162, 139, 230, 1, 97,
  1, 230, 81, 1, 141, 141, 141, 25, 23, 24, 1, 133, 22, 132, 2, 96, 25, 28, 1, 132, 22, 132, 132, 134, 143, 134, 25, 23, 132, 24, 96, 162, 81, 142, 1, 1, 99, 80, 162, 139, 230, 1, 22, 2, 96, 24, 28, 131,
  1, 22, 99, 80, 162, 139, 230, 142, 134, 2, 96, 23, 28, 147, 131, 133, 25, 23, 131, 24, 1, 96, 252, 81, 1, 1, 134, 22, 133, 2, 96, 24, 28, 132, 1, 134, 22, 96, 144, 27, 142, 23, 144, 96, 144, 27, 141, 23,
  147, 96, 144, 27, 143, 23, 145, 133, 2, 96, 23, 28, 96, 144, 27, 140, 23, 146, 96, 144, 27, 139, 23, 117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
] := by decide

private theorem submissionInstructionsChunk4_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk4 = [
  117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 97, 1, 104, 81, 96, 23, 140, 138, 117, 80, 162, 139, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 152, 134, 140, 129, 22, 140, 23, 141, 24, 24, 137, 24, 1, 96, 54, 81, 1, 137, 1, 133, 22, 129, 2, 96, 22, 28, 135, 1, 133, 22, 154, 129, 2, 131, 28, 133, 22, 150, 135, 137, 136, 22,
  23, 135, 24, 137, 141, 24, 24, 1, 97, 3, 6, 81, 1, 137, 1, 133, 22, 9, 96, 19, 28, 136, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 140, 143, 130, 154, 137, 141, 133, 138, 130, 22, 23, 138, 24, 24, 24, 1,
  133, 1, 138, 1, 134, 22, 141, 2, 96, 18, 28, 136, 1, 134, 22, 155, 141, 2, 132, 28, 134, 22, 151, 137, 136, 138, 129, 131, 22, 23, 24, 24, 141, 24, 1, 97, 3, 114, 81, 1, 138, 1, 134, 22, 9, 96, 20, 28,
  1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 141, 139, 130, 154, 137, 141, 137, 22, 141, 23, 137, 24, 24, 141, 24, 1, 97, 1, 140, 81, 1, 138, 1, 134, 22, 141, 2, 96, 28, 28, 136, 1, 134, 22, 155, 141, 2, 132,
  28, 134, 22, 151, 137, 136, 138, 129, 131, 22, 23, 24, 24, 141, 24, 1, 97, 4, 56, 81,
] := by decide

private theorem submissionInstructionsChunk5_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk5 = [
  1, 138, 1, 134, 22, 9, 96, 25, 28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 141, 139, 130, 154, 140, 136, 22, 140, 23, 141, 137, 140, 24, 24, 24, 1, 97, 4, 20, 81, 1, 138, 1, 134, 22, 129, 2, 96, 26,
  28, 136, 1, 134, 22, 155, 129, 2, 132, 28, 134, 22, 151, 140, 138, 138, 129, 139, 22, 23, 138, 24, 24, 24, 1, 97, 1, 32, 81, 1, 138, 1, 134, 22, 9, 96, 24, 28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22,
  140, 129, 153, 139, 139, 129, 137, 22, 23, 138, 137, 24, 24, 24, 1, 97, 3, 168, 81, 1, 137, 1, 133, 22, 140, 2, 96, 22, 28, 135, 1, 133, 22, 154, 140, 2, 131, 28, 133, 22, 150, 135, 135, 138, 22, 23, 140, 24,
  135, 138, 24, 24, 1, 97, 3, 42, 81, 1, 137, 1, 133, 22, 108, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 19, 28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 141, 129, 153, 136, 140, 136,
  24, 24, 131, 141, 137, 22, 23, 24, 1, 97, 1, 68, 81, 1, 137, 1, 133, 22, 140, 2, 96, 19, 28, 135, 1, 133, 22, 154, 140, 2, 131, 28, 133, 22, 150, 136, 135, 137, 129, 131, 22, 23, 24, 24, 140, 24, 1, 97,
  3, 96, 81, 1, 137, 1, 133, 22,
] := by decide

private theorem submissionInstructionsChunk6_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk6 = [
  108, 14, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 20, 28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 151, 137, 133, 22, 137, 23, 138, 136, 24, 24, 133, 24, 1, 97, 1, 194, 81, 1, 144, 150,
  1, 130, 22, 137, 2, 96, 27, 28, 132, 1, 130, 22, 151, 137, 2, 134, 28, 130, 22, 139, 143, 117, 92, 77, 209, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 139, 137, 141,
  137, 22, 24, 133, 137, 22, 23, 133, 24, 24, 1, 97, 4, 38, 81, 1, 135, 1, 133, 22, 9, 96, 25, 28, 136, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 151, 132, 135, 22, 138, 24, 133, 138, 22, 23, 135, 138, 24,
  24, 1, 96, 144, 81, 1, 133, 1, 140, 128, 108, 30, 0, 0, 0, 30, 0, 0, 0, 1, 0, 0, 0, 1, 129, 147, 135, 22, 9, 137, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 140, 136, 130, 22,
  139, 130, 139, 22, 24, 23, 24, 24, 1, 97, 3, 222, 81, 1, 135, 1, 133, 22, 108, 254, 0, 0, 0, 254, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 24, 28, 137, 1, 132, 22, 150, 139, 2, 136, 28, 132, 22, 149,
  99, 90, 130, 121, 153, 1, 152, 134, 139, 136, 23, 137, 136, 24, 22, 24, 139, 137, 22, 23,
] := by decide

private theorem submissionInstructionsChunk7_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk7 = [
  1, 96, 252, 81, 1, 137, 1, 132, 22, 139, 2, 96, 26, 28, 130, 1, 132, 22, 153, 139, 2, 136, 28, 132, 22, 145, 130, 139, 135, 24, 137, 130, 23, 22, 24, 139, 137, 22, 23, 1, 96, 72, 81, 1, 137, 1, 132, 22,
  108, 126, 0, 0, 0, 126, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 26, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 140, 129, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1, 96, 198,
  81, 1, 138, 1, 133, 22, 140, 2, 96, 25, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 137, 133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 1, 248, 81, 1, 138, 1, 133, 22, 108, 30,
  0, 0, 0, 30, 0, 0, 0, 16, 0, 0, 0, 16, 9, 136, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 1, 68, 81, 1, 138,
  1, 133, 22, 140, 2, 96, 22, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 137, 133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 2, 172, 81, 1, 138, 1, 133, 22, 108, 6, 0, 0, 0,
  6, 0, 0, 0, 4, 0, 0, 0, 4, 9, 96, 25, 28, 1, 131, 22, 149, 138, 2, 135,
] := by decide

private theorem submissionInstructionsChunk8_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk8 = [
  28, 131, 22, 141, 129, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 3, 240, 81, 1, 138, 1, 133, 22, 140, 2, 96, 26, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 137,
  133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 3, 186, 81, 1, 138, 1, 133, 22, 108, 14, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 20, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131,
  22, 141, 129, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 1, 194, 81, 1, 138, 1, 133, 22, 140, 2, 96, 26, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 137, 133, 23,
  141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 96, 36, 81, 1, 138, 1, 133, 22, 108, 126, 0, 0, 0, 126, 0, 0, 0, 64, 0, 0, 0, 64, 9, 96, 26, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 134,
  138, 22, 138, 135, 23, 136, 135, 24, 22, 135, 24, 23, 1, 97, 3, 60, 81, 1, 136, 1, 131, 22, 138, 2, 96, 18, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 144, 129, 135, 23, 138, 134, 24, 22, 130, 24,
  138, 136, 22, 23, 1, 97, 1, 230, 81, 1, 136, 1, 143, 141,
] := by decide

private theorem submissionInstructionsChunk9_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk9 = [
  108, 30, 0, 0, 0, 30, 0, 0, 0, 1, 0, 0, 0, 1, 129, 147, 135, 22, 9, 137, 28, 135, 1, 133, 22, 151, 140, 2, 137, 28, 133, 22, 150, 135, 140, 129, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1, 132,
  1, 117, 109, 112, 62, 243, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 130, 121, 153, 154, 1, 133, 22, 140, 2, 96, 22, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 135, 138,
  142, 131, 22, 24, 142, 130, 24, 22, 24, 24, 1, 97, 2, 154, 81, 1, 138, 1, 133, 22, 9, 96, 25, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 133, 133, 24, 138, 136, 136, 22, 24, 136, 135, 24, 22,
  24, 1, 96, 126, 81, 1, 136, 1, 108, 126, 0, 0, 0, 126, 0, 0, 0, 64, 0, 0, 0, 64, 142, 145, 133, 22, 9, 96, 25, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 151, 134, 138, 138, 22, 24, 138,
  134, 24, 22, 137, 134, 24, 24, 1, 97, 2, 46, 81, 1, 1, 141, 140, 145, 132, 22, 9, 96, 20, 28, 132, 1, 130, 22, 148, 137, 2, 134, 28, 130, 22, 140, 138, 129, 118, 1, 109, 112, 62, 242, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 1, 110, 217, 235, 161, 151, 132, 141, 25, 139, 23, 24,
] := by decide

private theorem submissionInstructionsChunk10_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk10 = [
  1, 97, 3, 204, 81, 1, 136, 1, 134, 22, 141, 2, 96, 22, 28, 139, 1, 134, 22, 155, 141, 2, 138, 28, 134, 22, 154, 139, 141, 139, 25, 23, 24, 1, 97, 1, 50, 81, 1, 136, 1, 134, 22, 108, 62, 0, 0, 0,
  62, 0, 0, 0, 32, 0, 0, 0, 32, 9, 96, 24, 28, 131, 1, 133, 22, 151, 129, 2, 137, 28, 133, 22, 146, 131, 140, 25, 138, 23, 24, 1, 96, 162, 81, 1, 135, 1, 133, 22, 129, 2, 96, 27, 28, 138, 1, 133,
  22, 154, 129, 2, 137, 28, 133, 22, 153, 138, 140, 138, 25, 23, 24, 1, 96, 18, 81, 1, 135, 1, 133, 22, 9, 96, 26, 28, 129, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 143, 130, 147, 131, 141, 25, 139, 23,
  24, 1, 97, 3, 60, 81, 1, 136, 1, 134, 22, 141, 2, 96, 19, 28, 139, 1, 134, 22, 155, 141, 2, 138, 28, 134, 22, 154, 140, 138, 25, 23, 140, 24, 1, 97, 2, 100, 81, 1, 136, 1, 134, 22, 9, 136, 28, 1,
  131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 146, 131, 140, 25, 138, 23, 24, 1, 97, 3, 168, 81, 1, 135, 1, 133, 22, 140, 2, 96, 20, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 140, 138,
  25, 23, 24, 1, 97, 1, 212, 81, 1, 135, 1, 133, 22,
] := by decide

private theorem submissionInstructionsChunk11_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk11 = [
  109, 7, 254, 0, 0, 7, 254, 0, 0, 4, 0, 0, 0, 4, 0, 9, 96, 27, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 129, 146, 131, 140, 25, 138, 23, 24, 1, 132, 1, 135, 1, 133, 22, 140, 2, 96,
  19, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 140, 138, 25, 23, 24, 1, 96, 234, 81, 1, 135, 1, 133, 22, 108, 62, 0, 0, 0, 62, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 24, 28, 1,
  131, 22, 149, 138, 2, 135, 28, 131, 22, 144, 129, 138, 25, 136, 23, 24, 1, 96, 54, 81, 1, 133, 1, 131, 22, 138, 2, 96, 20, 28, 136, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 151, 136, 138, 136, 25, 23, 24,
  1, 97, 1, 158, 81, 1, 133, 1, 142, 141, 108, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 129, 147, 135, 22, 9, 96, 26, 28, 131, 1, 133, 22, 151, 140, 2, 137, 28, 133, 22, 146, 131, 140, 25, 138,
  23, 24, 1, 96, 198, 81, 1, 117, 122, 109, 118, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 217, 235, 161, 151, 1, 133, 22, 140, 2, 96, 28, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28,
  133, 22, 153, 138, 140, 143, 24, 138, 142, 142, 22, 24, 22, 143, 24, 24, 1, 97, 2, 64,
] := by decide

private theorem submissionInstructionsChunk12_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk12 = [
  81, 1, 135, 1, 133, 22, 9, 96, 20, 28, 129, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 144, 129, 140, 129, 137, 22, 140, 24, 142, 138, 24, 22, 24, 24, 1, 97, 2, 190, 81, 1, 133, 1, 142, 142, 108, 6, 0,
  0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 143, 147, 135, 22, 9, 96, 27, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 140, 143, 24, 138, 142, 142, 22, 24, 22, 143, 24, 24, 1, 96, 90, 81,
  1, 135, 1, 133, 22, 9, 96, 27, 28, 129, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 99, 32, 65, 209, 59, 1, 144, 134, 138, 134, 23, 24, 138, 134, 22, 135, 24, 22, 138, 24, 1, 97, 3, 24, 81, 1, 129,
  1, 131, 22, 138, 2, 96, 22, 28, 136, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 151, 132, 135, 22, 137, 24, 133, 136, 23, 139, 24, 22, 135, 24, 1, 97, 3, 132, 81, 1, 129, 1, 131, 22, 143, 141, 145, 9, 96,
  20, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 135, 141, 22, 24, 135, 141, 23, 138, 24, 22, 140, 24, 1, 97, 2, 82, 81, 1, 131, 1, 133, 22, 140, 2, 96, 19, 28, 138, 1, 133, 22,
  154, 140, 2, 137, 28, 133, 22, 153, 138, 135, 138, 22, 24, 140, 138, 137, 23, 24, 22, 137,
] := by decide

private theorem submissionInstructionsChunk13_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk13 = [
  24, 1, 97, 2, 118, 81, 1, 131, 1, 133, 22, 109, 3, 254, 0, 0, 3, 254, 0, 0, 2, 0, 0, 0, 2, 0, 9, 96, 26, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 136, 140, 136, 23, 24,
  140, 136, 22, 137, 24, 22, 140, 24, 1, 96, 54, 81, 1, 131, 1, 133, 22, 140, 2, 96, 19, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 136, 140, 129, 137, 23, 24, 140, 137, 131, 22, 24, 22, 24, 1,
  97, 2, 226, 81, 1, 131, 1, 133, 22, 109, 3, 254, 0, 0, 3, 254, 0, 0, 2, 0, 0, 0, 2, 0, 9, 96, 26, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 129, 150, 139, 135, 129, 23, 138, 24, 137,
  137, 131, 22, 24, 22, 24, 1, 97, 1, 194, 81, 1, 131, 1, 133, 22, 140, 2, 96, 24, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 135, 138, 22, 24, 140, 138, 137, 23, 24, 22, 137, 24, 1, 97,
  1, 122, 81, 1, 131, 1, 133, 22, 108, 30, 0, 0, 0, 30, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 24, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 136, 140, 136, 23, 24, 140, 136, 22, 137,
  24, 22, 140, 24, 1, 96, 198, 81, 1, 131, 1, 133, 22, 140, 2, 96, 24, 28, 138, 1,
] := by decide

private theorem submissionInstructionsChunk14_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk14 = [
  133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 136, 140, 129, 137, 23, 24, 140, 137, 131, 22, 24, 22, 24, 1, 97, 3, 78, 81, 1, 131, 1, 133, 22, 108, 6, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 9,
  96, 20, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 129, 150, 139, 135, 129, 23, 138, 24, 137, 137, 131, 22, 24, 22, 24, 1, 96, 252, 81, 1, 131, 1, 133, 22, 140, 2, 96, 28, 28, 138, 1, 133, 22, 154,
  140, 2, 137, 28, 133, 22, 153, 136, 140, 138, 137, 23, 24, 140, 137, 131, 22, 24, 22, 24, 1, 97, 2, 136, 81, 1, 131, 1, 133, 22, 109, 3, 254, 0, 0, 3, 254, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 26,
  28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 134, 138, 134, 23, 24, 138, 134, 22, 135, 24, 22, 138, 24, 1, 96, 162, 81, 1, 1, 130, 22, 137, 2, 96, 25, 28, 135, 1, 130, 22, 151, 137, 2, 134, 28, 130,
  22, 139, 143, 99, 143, 27, 188, 220, 153, 134, 140, 138, 24, 23, 132, 22, 137, 24, 140, 136, 22, 24, 1, 96, 108, 81, 1, 138, 1, 133, 22, 9, 96, 26, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 133,
  138, 136, 24, 134, 23, 22, 133, 136, 22, 24, 138, 24, 1, 97, 4, 2, 81, 1, 136, 1,
] := by decide

private theorem submissionInstructionsChunk15_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk15 = [
  131, 22, 138, 2, 96, 28, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 144, 132, 138, 22, 135, 24, 130, 136, 140, 24, 135, 23, 22, 24, 1, 97, 1, 86, 81, 1, 99, 169, 83, 253, 78, 152, 1, 131, 22, 138,
  2, 96, 21, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 143, 143, 133, 147, 152, 143, 138, 143, 130, 22, 23, 140, 24, 143, 24, 24, 1, 97, 1, 140, 81, 1, 140, 1, 135, 22, 142, 2, 96, 24, 28, 133,
  1, 135, 22, 156, 142, 2, 139, 28, 135, 22, 148, 143, 128, 140, 22, 135, 23, 24, 139, 24, 142, 24, 1, 97, 2, 10, 81, 1, 140, 1, 135, 22, 108, 14, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96,
  20, 28, 136, 1, 134, 22, 152, 141, 2, 138, 28, 134, 22, 151, 142, 141, 138, 130, 130, 22, 23, 24, 139, 24, 24, 1, 97, 2, 208, 81, 1, 139, 1, 134, 22, 141, 2, 96, 28, 28, 132, 1, 134, 22, 155, 141, 2, 138,
  28, 134, 22, 147, 142, 138, 134, 130, 130, 22, 23, 24, 24, 141, 24, 1, 97, 2, 244, 81, 1, 139, 1, 134, 22, 9, 96, 21, 28, 134, 1, 132, 22, 150, 139, 2, 136, 28, 132, 22, 149, 134, 139, 142, 22, 23, 139, 142,
  24, 137, 24, 24, 1, 96, 252, 81, 1, 137, 1, 132, 22, 139, 2, 96, 27, 28, 130, 1,
] := by decide

private theorem submissionInstructionsChunk16_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk16 = [
  132, 22, 153, 139, 2, 136, 28, 132, 22, 145, 140, 136, 132, 130, 139, 22, 23, 24, 140, 24, 24, 1, 97, 1, 176, 81, 1, 137, 1, 132, 22, 139, 2, 96, 25, 28, 134, 1, 132, 22, 150, 139, 2, 136, 28, 132, 22, 149,
  140, 139, 129, 129, 22, 137, 23, 24, 137, 24, 24, 1, 1, 136, 1, 131, 22, 138, 2, 96, 20, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 144, 139, 130, 136, 142, 22, 23, 136, 24, 139, 24, 24, 1, 96, 216,
  81, 1, 136, 1, 108, 126, 0, 0, 0, 126, 0, 0, 0, 64, 0, 0, 0, 64, 142, 145, 133, 22, 9, 96, 26, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 143, 130, 151, 140, 143, 24, 143, 142, 22, 133,
  23, 139, 24, 24, 1, 96, 162, 81, 1, 139, 1, 134, 22, 141, 2, 96, 28, 28, 132, 1, 134, 22, 155, 141, 2, 138, 28, 134, 22, 147, 142, 138, 22, 133, 23, 138, 24, 143, 142, 24, 24, 1, 97, 2, 28, 81, 1, 139,
  1, 134, 22, 9, 96, 20, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 141, 140, 129, 129, 22, 138, 23, 24, 138, 24, 24, 1, 97, 3, 204, 81, 1, 138, 1, 133, 22, 140, 2, 96, 20, 28, 131, 1,
  133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 141, 137, 129, 129, 22, 134, 23, 24, 24, 140,
] := by decide

private theorem submissionInstructionsChunk17_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk17 = [
  24, 1, 97, 3, 150, 81, 1, 138, 1, 133, 22, 108, 14, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 21, 28, 1, 131, 22, 149, 138, 2, 135, 28, 148, 139, 138, 129, 129, 22, 136, 23, 24, 136, 24,
  24, 1, 97, 2, 82, 81, 1, 136, 1, 131, 22, 138, 2, 96, 22, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 138, 135, 2, 136, 28, 140, 139, 131, 25, 138, 23, 24, 95, 81, 133, 1, 1, 139, 1, 22, 140, 2, 96,
  25, 28, 135, 1, 141, 22, 97, 2, 100, 81, 139, 130, 142, 133, 25, 23, 24, 1, 1, 136, 1, 142, 22, 141, 2, 96, 28, 28, 131, 1, 140, 142, 2, 139, 28, 155, 129, 131, 142, 25, 23, 24, 133, 1, 96, 198, 81, 1,
  1, 143, 22, 142, 2, 96, 27, 28, 131, 1, 147, 97, 0, 144, 28, 1, 150, 80, 140, 2, 147, 80, 150, 97, 0, 144, 28, 1, 148, 97, 0, 144, 28, 146, 80, 96, 144, 28, 151, 96, 144, 28, 149, 28, 1, 143, 1, 136,
  22, 159, 1, 135, 22, 159, 1, 134, 22, 154, 1, 1, 132, 22, 153, 1, 1, 130, 22, 152, 80, 140, 86, 91, 145, 133, 96, 2, 27, 129, 129, 23, 96, 9, 129, 146, 5, 1, 24, 24, 145, 96, 251, 135, 1, 128, 54, 3,
  128, 54, 29, 22, 1, 96, 32, 129, 3, 148, 80, 150, 145, 132, 17, 97, 18, 79, 87,
] := by decide

private theorem submissionInstructionsChunk18_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk18 = [
  97, 18, 105, 86, 91, 96, 251, 91, 127, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 128, 25, 96, 32, 131, 3, 127,
  7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 95, 95, 96, 33, 54, 16, 97, 18, 105, 87, 91, 129, 96, 32, 1, 145,
  53, 133, 132, 23, 135, 129, 3, 24, 132, 24, 147, 24, 23, 131, 130, 16, 97, 18, 79, 87, 91, 129, 53, 131, 24, 132, 131, 3, 96, 3, 27, 28, 23, 54, 135, 3, 97, 17, 201, 87, 96, 246, 87, 96, 20, 96, 15, 54,
  98, 219, 20, 123, 4, 22, 129, 2, 56, 3, 96, 12, 57, 89, 95, 243, 91, 139, 96, 128, 1, 89, 16, 97, 18, 176, 87, 91, 154, 96, 64, 1, 89, 129, 20, 96, 129, 87, 154, 97, 1, 201, 86, 91, 80, 80, 80, 80,
  80, 80, 96, 16, 82, 96, 12, 82, 96, 8, 82, 96, 4, 82, 95, 82, 96, 16, 81, 97, 1, 1, 129, 128, 96, 8, 28, 24, 133, 22, 2, 24, 128, 129, 96, 16, 28, 24, 133, 22, 98, 1, 0, 1, 2, 24, 95, 82,
  96, 32, 95, 243, 91, 54, 96, 1,
] := by decide

private theorem submissionInstructionsChunk19_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk19 = [
  112, 1, 1, 128, 0, 0, 0, 0, 0, 3, 129, 128, 0, 1, 128, 0, 0, 2, 54, 28, 22, 97, 17, 252, 87, 97, 1, 0, 20, 97, 1, 120, 54, 20, 1, 97, 17, 249, 87, 95, 53, 96, 232, 29, 54, 98, 32, 118,
  33, 2, 24, 96, 246, 87, 115, 16, 181, 40, 89, 5, 22, 178, 98, 175, 214, 144, 26, 176, 43, 33, 241, 110, 170, 221, 97, 54, 28, 115, 140, 164, 173, 252, 192, 255, 78, 54, 206, 254, 152, 141, 206, 195, 212, 185, 220, 143,
  80, 80, 24, 96, 98, 86,
] := by decide

private theorem assemble_chunk0 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk0 = submissionByteChunk0 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk0_assemble]

private theorem assemble_chunk1 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk1 = submissionByteChunk1 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk1_assemble]

private theorem assemble_chunk2 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk2 = submissionByteChunk2 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk2_assemble]

private theorem assemble_chunk3 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk3 = submissionByteChunk3 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk3_assemble]

private theorem assemble_chunk4 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk4 = submissionByteChunk4 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk4_assemble]

private theorem assemble_chunk5 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk5 = submissionByteChunk5 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk5_assemble]

private theorem assemble_chunk6 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk6 = submissionByteChunk6 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk6_assemble]

private theorem assemble_chunk7 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk7 = submissionByteChunk7 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk7_assemble]

private theorem assemble_chunk8 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk8 = submissionByteChunk8 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk8_assemble]

private theorem assemble_chunk9 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk9 = submissionByteChunk9 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk9_assemble]

private theorem assemble_chunk10 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk10 = submissionByteChunk10 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk10_assemble]

private theorem assemble_chunk11 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk11 = submissionByteChunk11 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk11_assemble]

private theorem assemble_chunk12 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk12 = submissionByteChunk12 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk12_assemble]

private theorem assemble_chunk13 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk13 = submissionByteChunk13 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk13_assemble]

private theorem assemble_chunk14 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk14 = submissionByteChunk14 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk14_assemble]

private theorem assemble_chunk15 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk15 = submissionByteChunk15 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk15_assemble]

private theorem assemble_chunk16 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk16 = submissionByteChunk16 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk16_assemble]

private theorem assemble_chunk17 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk17 = submissionByteChunk17 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk17_assemble]

private theorem assemble_chunk18 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk18 = submissionByteChunk18 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk18_assemble]

private def submissionData : List UInt8 := [
  0x4d, 0xe2, 0x0b, 0x6b, 0x1f, 0xb2, 0xaf, 0x44, 0x23, 0x70, 0xc4, 0x0e,
  0x53, 0xa5, 0x0a, 0xca, 0x36, 0x0f, 0xc3, 0xbc, 0xdb, 0x4d, 0x90, 0xb3,
  0xbe, 0x82, 0x8e, 0xa7, 0xce, 0xd8, 0xd8, 0x79, 0xdb, 0xce, 0xa2, 0xc1,
  0xd5, 0xfe, 0x20, 0x7f, 0x2b, 0x95, 0x67, 0xd6, 0x84, 0xdc, 0x89, 0xcd,
  0x54, 0x62, 0x0e, 0x46, 0x02, 0x9f, 0x5b, 0xda, 0x0e, 0xca, 0xb7, 0x87,
  0x5b, 0xe9, 0x25, 0x9e, 0x94, 0x78, 0x20, 0x2d, 0xd0, 0xc1, 0xf4, 0xeb,
  0x0c, 0x4e, 0xd0, 0x44, 0x2d, 0xbe, 0xb2, 0xcd, 0x37, 0x88, 0x0e, 0xe5,
  0xe2, 0xe8, 0x21, 0xe0, 0x54, 0x0b, 0xb1, 0x46, 0xe3, 0x3b, 0x37, 0x34,
  0x23, 0x16, 0xe7, 0xed, 0xf6, 0xce, 0xa8, 0xd2, 0xa4, 0x91, 0xf5, 0xdc,
  0x27, 0x6a, 0xa1, 0xf7, 0x61, 0x8b, 0x4d, 0x7a, 0x55, 0x2e, 0xc4, 0xad,
  0x28, 0xdf, 0xaf, 0x14, 0xed, 0x99, 0x53, 0xf4, 0x9c, 0x7a, 0xbb, 0x56,
  0x13, 0x08, 0xd0, 0xc6, 0x4b, 0xc4, 0xc1, 0x79, 0x09, 0x06, 0xf7, 0x77,
  0x41, 0x05, 0xd3, 0x64, 0x06, 0x50, 0x54, 0x1c, 0x2e, 0x7b, 0xc1, 0x9b,
  0xfe, 0x9b, 0x51, 0x49, 0x47, 0x52, 0x72, 0xba, 0x46, 0x7c, 0xa6, 0x71,
  0x6d, 0xbb, 0x1c, 0x19, 0xa8, 0x4d, 0xe3, 0x55, 0xf0, 0x65, 0x82, 0x9a,
  0x86, 0x3c, 0x59, 0x85, 0x88, 0xbd, 0x72, 0xa4, 0xba, 0xbf, 0x36, 0xc6,
  0xbb, 0x01, 0xf2, 0x7b, 0xbd, 0xc0, 0xec, 0xd4, 0xc6, 0xc5, 0x3c, 0x46,
  0xcf, 0x08, 0xde, 0x1c, 0x53, 0x75, 0xb1, 0x5a, 0xf8, 0x67, 0x6a, 0x2d,
  0x32, 0xef, 0x52, 0x8a, 0x1a, 0xcf, 0x41, 0xb0, 0x9f, 0x87, 0xac, 0xc9,
  0x83, 0xc2, 0xa0, 0x43, 0xf5, 0x04, 0x4c, 0x8f, 0x71, 0xc5, 0x2d, 0xbd,
  0xd8, 0xe2, 0xe8, 0x4b, 0xad, 0x19, 0xfc, 0x85, 0xdb, 0xad, 0xb5, 0x5f,
  0xa5, 0x46, 0x76, 0x31, 0xce, 0x14, 0x15, 0x03, 0x8a, 0x14, 0xb0, 0xc8,
  0x92, 0x87, 0xb3, 0x9b, 0x1a, 0x2f, 0x73, 0xaa, 0x79, 0xa1, 0xce, 0x95,
  0xb0, 0x4e, 0x78, 0x17
]

private theorem assemble_chunk19 :
    Challenge.EvmProof.PcEncoding.assemble submissionInstructionsChunk19 ++ mkCode submissionData = submissionByteChunk19 := by
  rw [Challenge.EvmProof.PcEncoding.assemble, submissionInstructionsChunk19_assemble]
  rfl

theorem assemble_referenceInstructions :
    mkCode (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructions ++ submissionData) = submissionBytecode := by
  rw [ArtifactSegment.mkCode_append]
  change Challenge.EvmProof.PcEncoding.assemble submissionInstructions ++ mkCode submissionData = submissionBytecode
  simp only [submissionInstructions, ArtifactSegment.assemble_append, ByteArray.append_assoc,
    assemble_chunk0, assemble_chunk1, assemble_chunk2, assemble_chunk3, assemble_chunk4, assemble_chunk5, assemble_chunk6, assemble_chunk7, assemble_chunk8, assemble_chunk9, assemble_chunk10, assemble_chunk11, assemble_chunk12, assemble_chunk13, assemble_chunk14, assemble_chunk15, assemble_chunk16, assemble_chunk17, assemble_chunk18, assemble_chunk19, submissionBytecode, submissionBytes]

def submissionArtifact : Challenge.EvmProof.DataProgramArtifact where
  code := submissionBytecode
  instructions := submissionInstructions
  data := submissionData
  assembly_eq := assemble_referenceInstructions

private theorem chunk0_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk0).length = 247 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk1_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk1).length = 258 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk2_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk2).length = 240 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk3_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk3).length = 238 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk4_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk4).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk5_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk5).length = 248 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk6_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk6).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk7_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk7).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk8_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk8).length = 254 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk9_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk9).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk10_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk10).length = 253 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk11_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk11).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk12_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk12).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk13_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk13).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk14_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk14).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk15_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk15).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk16_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk16).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk17_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk17).length = 259 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk18_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk18).length = 248 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private def tailPrefix : List Instr :=
  submissionInstructionsChunk0 ++
  submissionInstructionsChunk1 ++
  submissionInstructionsChunk2 ++
  submissionInstructionsChunk3 ++
  submissionInstructionsChunk4 ++
  submissionInstructionsChunk5 ++
  submissionInstructionsChunk6 ++
  submissionInstructionsChunk7 ++
  submissionInstructionsChunk8 ++
  submissionInstructionsChunk9 ++
  submissionInstructionsChunk10 ++
  submissionInstructionsChunk11 ++
  submissionInstructionsChunk12 ++
  submissionInstructionsChunk13 ++
  submissionInstructionsChunk14 ++
  submissionInstructionsChunk15 ++
  submissionInstructionsChunk16 ++
  submissionInstructionsChunk17 ++
  submissionInstructionsChunk18

private theorem tailPrefix_length : tailPrefix.length = 3575 := by
  simp only [tailPrefix, List.length_append, submissionInstructionsChunk0_length, submissionInstructionsChunk1_length, submissionInstructionsChunk2_length, submissionInstructionsChunk3_length, submissionInstructionsChunk4_length, submissionInstructionsChunk5_length, submissionInstructionsChunk6_length, submissionInstructionsChunk7_length, submissionInstructionsChunk8_length, submissionInstructionsChunk9_length, submissionInstructionsChunk10_length, submissionInstructionsChunk11_length, submissionInstructionsChunk12_length, submissionInstructionsChunk13_length, submissionInstructionsChunk14_length, submissionInstructionsChunk15_length, submissionInstructionsChunk16_length, submissionInstructionsChunk17_length, submissionInstructionsChunk18_length]

private theorem tailPrefix_bytes_length : (Challenge.EvmProof.PcEncoding.assembleBytes tailPrefix).length = 4845 := by
  simp only [tailPrefix, Challenge.EvmProof.PcEncoding.assembleBytes_append, List.length_append, chunk0_byteLength, chunk1_byteLength, chunk2_byteLength, chunk3_byteLength, chunk4_byteLength, chunk5_byteLength, chunk6_byteLength, chunk7_byteLength, chunk8_byteLength, chunk9_byteLength, chunk10_byteLength, chunk11_byteLength, chunk12_byteLength, chunk13_byteLength, chunk14_byteLength, chunk15_byteLength, chunk16_byteLength, chunk17_byteLength, chunk18_byteLength]

private theorem instructionPC_tail (i : Nat) (hi : i ≤ 31) :
    submissionArtifact.instructionPC (3575 + i) =
      4845 + (Challenge.EvmProof.PcEncoding.assembleBytes (submissionInstructionsChunk19.take i)).length := by
  apply ArtifactSegment.instructionPC_segment_of_bounds submissionArtifact
    tailPrefix submissionInstructionsChunk19 [] 3575 4845
  · simp only [submissionArtifact, submissionInstructions, tailPrefix, List.append_nil]
  · exact tailPrefix_length
  · exact tailPrefix_bytes_length
  · simpa only [submissionInstructionsChunk19_length] using hi

def instructionPC (index : Nat) : Nat :=
  submissionArtifact.instructionPC index


/-- One of the straight-line stores which initializes RIPEMD's lookup tables,
round constants, and five-word initial chaining value. -/
structure InitStore where
  index : Nat
  valueWidth : Fin 33
  value : UInt256
  offsetWidth : Fin 33
  offset : UInt256
  useMsize : Bool

def initStores : List InitStore := []

@[simp] theorem referenceArtifact_pc_0 :
    submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc0 :
    submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc0 :
    instructionPC 11 = 21 := by
  change submissionArtifact.instructionPC 11 = 21
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_1 :
    submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc1 :
    submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc1 :
    instructionPC 11 = 21 := by
  change submissionArtifact.instructionPC 11 = 21
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_405 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc405 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc405 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_406 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc406 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc406 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_407 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc407 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc407 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_408 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc408 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc408 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_409 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc409 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc409 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_410 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc410 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc410 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_412 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc412 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc412 :
    instructionPC 153 = 317 := by
  change submissionArtifact.instructionPC 153 = 317
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_417 :
    submissionArtifact.instructionPC 155 = 319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc417 :
    submissionArtifact.instructionPC 155 = 319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc417 :
    instructionPC 155 = 319 := by
  change submissionArtifact.instructionPC 155 = 319
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_420 :
    submissionArtifact.instructionPC 147 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc420 :
    submissionArtifact.instructionPC 147 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc420 :
    instructionPC 147 = 246 := by
  change submissionArtifact.instructionPC 147 = 246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_421 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc421 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc421 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_422 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc422 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc422 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_423 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc423 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc423 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_424 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc424 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc424 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_426 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc426 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc426 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_427 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc427 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc427 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_428 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc428 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc428 :
    instructionPC 153 = 317 := by
  change submissionArtifact.instructionPC 153 = 317
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_430 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc430 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc430 :
    instructionPC 153 = 317 := by
  change submissionArtifact.instructionPC 153 = 317
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_431 :
    submissionArtifact.instructionPC 155 = 319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc431 :
    submissionArtifact.instructionPC 155 = 319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc431 :
    instructionPC 155 = 319 := by
  change submissionArtifact.instructionPC 155 = 319
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_439 :
    submissionArtifact.instructionPC 156 = 320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc439 :
    submissionArtifact.instructionPC 156 = 320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc439 :
    instructionPC 156 = 320 := by
  change submissionArtifact.instructionPC 156 = 320
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_440 :
    submissionArtifact.instructionPC 157 = 325 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc440 :
    submissionArtifact.instructionPC 157 = 325 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc440 :
    instructionPC 157 = 325 := by
  change submissionArtifact.instructionPC 157 = 325
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_441 :
    submissionArtifact.instructionPC 158 = 330 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc441 :
    submissionArtifact.instructionPC 158 = 330 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc441 :
    instructionPC 158 = 330 := by
  change submissionArtifact.instructionPC 158 = 330
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_442 :
    submissionArtifact.instructionPC 159 = 335 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc442 :
    submissionArtifact.instructionPC 159 = 335 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc442 :
    instructionPC 159 = 335 := by
  change submissionArtifact.instructionPC 159 = 335
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_443 :
    submissionArtifact.instructionPC 160 = 340 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc443 :
    submissionArtifact.instructionPC 160 = 340 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc443 :
    instructionPC 160 = 340 := by
  change submissionArtifact.instructionPC 160 = 340
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_444 :
    submissionArtifact.instructionPC 161 = 345 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc444 :
    submissionArtifact.instructionPC 161 = 345 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc444 :
    instructionPC 161 = 345 := by
  change submissionArtifact.instructionPC 161 = 345
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_445 :
    submissionArtifact.instructionPC 162 = 359 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc445 :
    submissionArtifact.instructionPC 162 = 359 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc445 :
    instructionPC 162 = 359 := by
  change submissionArtifact.instructionPC 162 = 359
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_446 :
    submissionArtifact.instructionPC 163 = 373 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc446 :
    submissionArtifact.instructionPC 163 = 373 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc446 :
    instructionPC 163 = 373 := by
  change submissionArtifact.instructionPC 163 = 373
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_448 :
    submissionArtifact.instructionPC 165 = 429 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc448 :
    submissionArtifact.instructionPC 165 = 429 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc448 :
    instructionPC 165 = 429 := by
  change submissionArtifact.instructionPC 165 = 429
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_449 :
    submissionArtifact.instructionPC 166 = 434 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc449 :
    submissionArtifact.instructionPC 166 = 434 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc449 :
    instructionPC 166 = 434 := by
  change submissionArtifact.instructionPC 166 = 434
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_450 :
    submissionArtifact.instructionPC 167 = 448 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc450 :
    submissionArtifact.instructionPC 167 = 448 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc450 :
    instructionPC 167 = 448 := by
  change submissionArtifact.instructionPC 167 = 448
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_451 :
    submissionArtifact.instructionPC 168 = 450 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc451 :
    submissionArtifact.instructionPC 168 = 450 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc451 :
    instructionPC 168 = 450 := by
  change submissionArtifact.instructionPC 168 = 450
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_452 :
    submissionArtifact.instructionPC 169 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc452 :
    submissionArtifact.instructionPC 169 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc452 :
    instructionPC 169 = 451 := by
  change submissionArtifact.instructionPC 169 = 451
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_454 :
    submissionArtifact.instructionPC 125 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc454 :
    submissionArtifact.instructionPC 125 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc454 :
    instructionPC 125 = 217 := by
  change submissionArtifact.instructionPC 125 = 217
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_455 :
    submissionArtifact.instructionPC 126 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc455 :
    submissionArtifact.instructionPC 126 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc455 :
    instructionPC 126 = 218 := by
  change submissionArtifact.instructionPC 126 = 218
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_843 :
    submissionArtifact.instructionPC 147 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc843 :
    submissionArtifact.instructionPC 147 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc843 :
    instructionPC 147 = 246 := by
  change submissionArtifact.instructionPC 147 = 246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_844 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc844 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc844 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_859 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc859 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc859 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_860 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc860 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc860 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_861 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc861 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc861 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_862 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc862 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc862 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_265 :
    submissionArtifact.instructionPC 170 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_265 :
    instructionPC 170 = 452 := by
  change submissionArtifact.instructionPC 170 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_266 :
    submissionArtifact.instructionPC 170 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_266 :
    instructionPC 170 = 452 := by
  change submissionArtifact.instructionPC 170 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_267 :
    submissionArtifact.instructionPC 171 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_267 :
    instructionPC 171 = 453 := by
  change submissionArtifact.instructionPC 171 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_268 :
    submissionArtifact.instructionPC 116 = 205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_268 :
    instructionPC 116 = 205 := by
  change submissionArtifact.instructionPC 116 = 205
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_270 :
    submissionArtifact.instructionPC 118 = 208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_270 :
    instructionPC 118 = 208 := by
  change submissionArtifact.instructionPC 118 = 208
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_271 :
    submissionArtifact.instructionPC 119 = 209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_271 :
    instructionPC 119 = 209 := by
  change submissionArtifact.instructionPC 119 = 209
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_272 :
    submissionArtifact.instructionPC 120 = 210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_272 :
    instructionPC 120 = 210 := by
  change submissionArtifact.instructionPC 120 = 210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_273 :
    submissionArtifact.instructionPC 121 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_273 :
    instructionPC 121 = 211 := by
  change submissionArtifact.instructionPC 121 = 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_274 :
    submissionArtifact.instructionPC 122 = 212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_274 :
    instructionPC 122 = 212 := by
  change submissionArtifact.instructionPC 122 = 212
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_275 :
    submissionArtifact.instructionPC 123 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_275 :
    instructionPC 123 = 214 := by
  change submissionArtifact.instructionPC 123 = 214
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_276 :
    submissionArtifact.instructionPC 124 = 215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_276 :
    instructionPC 124 = 215 := by
  change submissionArtifact.instructionPC 124 = 215
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_279 :
    submissionArtifact.instructionPC 127 = 219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_279 :
    instructionPC 127 = 219 := by
  change submissionArtifact.instructionPC 127 = 219
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_280 :
    submissionArtifact.instructionPC 128 = 220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_280 :
    instructionPC 128 = 220 := by
  change submissionArtifact.instructionPC 128 = 220
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_281 :
    submissionArtifact.instructionPC 129 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_281 :
    instructionPC 129 = 221 := by
  change submissionArtifact.instructionPC 129 = 221
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_282 :
    submissionArtifact.instructionPC 130 = 222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_282 :
    instructionPC 130 = 222 := by
  change submissionArtifact.instructionPC 130 = 222
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_283 :
    submissionArtifact.instructionPC 131 = 223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_283 :
    instructionPC 131 = 223 := by
  change submissionArtifact.instructionPC 131 = 223
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_284 :
    submissionArtifact.instructionPC 132 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_284 :
    instructionPC 132 = 225 := by
  change submissionArtifact.instructionPC 132 = 225
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_285 :
    submissionArtifact.instructionPC 133 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_285 :
    instructionPC 133 = 226 := by
  change submissionArtifact.instructionPC 133 = 226
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_286 :
    submissionArtifact.instructionPC 134 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_286 :
    instructionPC 134 = 227 := by
  change submissionArtifact.instructionPC 134 = 227
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_287 :
    submissionArtifact.instructionPC 135 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_287 :
    instructionPC 135 = 229 := by
  change submissionArtifact.instructionPC 135 = 229
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_288 :
    submissionArtifact.instructionPC 136 = 230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_288 :
    instructionPC 136 = 230 := by
  change submissionArtifact.instructionPC 136 = 230
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_289 :
    submissionArtifact.instructionPC 137 = 231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_289 :
    instructionPC 137 = 231 := by
  change submissionArtifact.instructionPC 137 = 231
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_290 :
    submissionArtifact.instructionPC 138 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_290 :
    instructionPC 138 = 232 := by
  change submissionArtifact.instructionPC 138 = 232
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_291 :
    submissionArtifact.instructionPC 139 = 234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_291 :
    instructionPC 139 = 234 := by
  change submissionArtifact.instructionPC 139 = 234
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_292 :
    submissionArtifact.instructionPC 140 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_292 :
    instructionPC 140 = 235 := by
  change submissionArtifact.instructionPC 140 = 235
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_293 :
    submissionArtifact.instructionPC 141 = 236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_293 :
    instructionPC 141 = 236 := by
  change submissionArtifact.instructionPC 141 = 236
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_294 :
    submissionArtifact.instructionPC 145 = 242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_294 :
    instructionPC 145 = 242 := by
  change submissionArtifact.instructionPC 145 = 242
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_295 :
    submissionArtifact.instructionPC 146 = 245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_295 :
    instructionPC 146 = 245 := by
  change submissionArtifact.instructionPC 146 = 245
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem validJumpDest_210 :
    Decode.isValidJumpDest submissionBytecode 219 = true := by
  have hp : submissionArtifact.instructionPC 127 = 219 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 127 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem pcU2_345 :
    submissionArtifact.instructionPC 172 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_345 :
    instructionPC 172 = 456 := by
  change submissionArtifact.instructionPC 172 = 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem validJumpDest_loop :
    Decode.isValidJumpDest submissionBytecode 457 = true := by
  have hp : submissionArtifact.instructionPC 173 = 457 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 173 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_partialEntry :
    Decode.isValidJumpDest submissionBytecode 104 = true := by
  have hp : submissionArtifact.instructionPC 61 = 104 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 61 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest submissionBytecode 246 = true := by
  have hp : submissionArtifact.instructionPC 147 = 246 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 147 (by rfl)
  rw [hp] at h
  exact h

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩




@[simp] theorem cjPc0 :
    submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci0 :
    instructionPC 0 = 0 := by
  change submissionArtifact.instructionPC 0 = 0
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc1 :
    submissionArtifact.instructionPC 1 = 6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci1 :
    instructionPC 1 = 6 := by
  change submissionArtifact.instructionPC 1 = 6
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc2 :
    submissionArtifact.instructionPC 2 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci2 :
    instructionPC 2 = 7 := by
  change submissionArtifact.instructionPC 2 = 7
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc3 :
    submissionArtifact.instructionPC 3 = 8 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci3 :
    instructionPC 3 = 8 := by
  change submissionArtifact.instructionPC 3 = 8
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc4 :
    submissionArtifact.instructionPC 4 = 9 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci4 :
    instructionPC 4 = 9 := by
  change submissionArtifact.instructionPC 4 = 9
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc5 :
    submissionArtifact.instructionPC 5 = 11 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci5 :
    instructionPC 5 = 11 := by
  change submissionArtifact.instructionPC 5 = 11
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc6 :
    submissionArtifact.instructionPC 6 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci6 :
    instructionPC 6 = 12 := by
  change submissionArtifact.instructionPC 6 = 12
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc7 :
    submissionArtifact.instructionPC 7 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci7 :
    instructionPC 7 = 13 := by
  change submissionArtifact.instructionPC 7 = 13
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc8 :
    submissionArtifact.instructionPC 8 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci8 :
    instructionPC 8 = 16 := by
  change submissionArtifact.instructionPC 8 = 16
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc9 :
    submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci9 :
    instructionPC 9 = 17 := by
  change submissionArtifact.instructionPC 9 = 17
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc10 :
    submissionArtifact.instructionPC 10 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci10 :
    instructionPC 10 = 20 := by
  change submissionArtifact.instructionPC 10 = 20
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc11 :
    submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci11 :
    instructionPC 11 = 21 := by
  change submissionArtifact.instructionPC 11 = 21
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc12 :
    submissionArtifact.instructionPC 12 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci12 :
    instructionPC 12 = 22 := by
  change submissionArtifact.instructionPC 12 = 22
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc13 :
    submissionArtifact.instructionPC 13 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci13 :
    instructionPC 13 = 23 := by
  change submissionArtifact.instructionPC 13 = 23
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc14 :
    submissionArtifact.instructionPC 14 = 25 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci14 :
    instructionPC 14 = 25 := by
  change submissionArtifact.instructionPC 14 = 25
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc15 :
    submissionArtifact.instructionPC 15 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci15 :
    instructionPC 15 = 26 := by
  change submissionArtifact.instructionPC 15 = 26
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc16 :
    submissionArtifact.instructionPC 16 = 28 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci16 :
    instructionPC 16 = 28 := by
  change submissionArtifact.instructionPC 16 = 28
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc17 :
    submissionArtifact.instructionPC 17 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci17 :
    instructionPC 17 = 29 := by
  change submissionArtifact.instructionPC 17 = 29
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc18 :
    submissionArtifact.instructionPC 18 = 32 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci18 :
    instructionPC 18 = 32 := by
  change submissionArtifact.instructionPC 18 = 32
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc19 :
    submissionArtifact.instructionPC 19 = 33 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci19 :
    instructionPC 19 = 33 := by
  change submissionArtifact.instructionPC 19 = 33
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc20 :
    submissionArtifact.instructionPC 20 = 34 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci20 :
    instructionPC 20 = 34 := by
  change submissionArtifact.instructionPC 20 = 34
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc21 :
    submissionArtifact.instructionPC 21 = 35 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci21 :
    instructionPC 21 = 35 := by
  change submissionArtifact.instructionPC 21 = 35
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc22 :
    submissionArtifact.instructionPC 22 = 38 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci22 :
    instructionPC 22 = 38 := by
  change submissionArtifact.instructionPC 22 = 38
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc23 :
    submissionArtifact.instructionPC 23 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci23 :
    instructionPC 23 = 41 := by
  change submissionArtifact.instructionPC 23 = 41
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc24 :
    submissionArtifact.instructionPC 24 = 42 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci24 :
    instructionPC 24 = 42 := by
  change submissionArtifact.instructionPC 24 = 42
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc25 :
    submissionArtifact.instructionPC 25 = 43 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci25 :
    instructionPC 25 = 43 := by
  change submissionArtifact.instructionPC 25 = 43
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc26 :
    submissionArtifact.instructionPC 26 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci26 :
    instructionPC 26 = 44 := by
  change submissionArtifact.instructionPC 26 = 44
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc27 :
    submissionArtifact.instructionPC 27 = 45 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci27 :
    instructionPC 27 = 45 := by
  change submissionArtifact.instructionPC 27 = 45
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc28 :
    submissionArtifact.instructionPC 28 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci28 :
    instructionPC 28 = 47 := by
  change submissionArtifact.instructionPC 28 = 47
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc29 :
    submissionArtifact.instructionPC 29 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci29 :
    instructionPC 29 = 48 := by
  change submissionArtifact.instructionPC 29 = 48
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc30 :
    submissionArtifact.instructionPC 30 = 49 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci30 :
    instructionPC 30 = 49 := by
  change submissionArtifact.instructionPC 30 = 49
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc31 :
    submissionArtifact.instructionPC 31 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci31 :
    instructionPC 31 = 50 := by
  change submissionArtifact.instructionPC 31 = 50
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc32 :
    submissionArtifact.instructionPC 32 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci32 :
    instructionPC 32 = 51 := by
  change submissionArtifact.instructionPC 32 = 51
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc33 :
    submissionArtifact.instructionPC 33 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci33 :
    instructionPC 33 = 52 := by
  change submissionArtifact.instructionPC 33 = 52
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc34 :
    submissionArtifact.instructionPC 34 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci34 :
    instructionPC 34 = 53 := by
  change submissionArtifact.instructionPC 34 = 53
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc35 :
    submissionArtifact.instructionPC 35 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci35 :
    instructionPC 35 = 55 := by
  change submissionArtifact.instructionPC 35 = 55
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc36 :
    submissionArtifact.instructionPC 36 = 56 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci36 :
    instructionPC 36 = 56 := by
  change submissionArtifact.instructionPC 36 = 56
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc37 :
    submissionArtifact.instructionPC 37 = 57 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci37 :
    instructionPC 37 = 57 := by
  change submissionArtifact.instructionPC 37 = 57
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc38 :
    submissionArtifact.instructionPC 38 = 58 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci38 :
    instructionPC 38 = 58 := by
  change submissionArtifact.instructionPC 38 = 58
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc39 :
    submissionArtifact.instructionPC 39 = 59 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci39 :
    instructionPC 39 = 59 := by
  change submissionArtifact.instructionPC 39 = 59
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc40 :
    submissionArtifact.instructionPC 40 = 60 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci40 :
    instructionPC 40 = 60 := by
  change submissionArtifact.instructionPC 40 = 60
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc41 :
    submissionArtifact.instructionPC 41 = 61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci41 :
    instructionPC 41 = 61 := by
  change submissionArtifact.instructionPC 41 = 61
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc42 :
    submissionArtifact.instructionPC 42 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci42 :
    instructionPC 42 = 63 := by
  change submissionArtifact.instructionPC 42 = 63
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc43 :
    submissionArtifact.instructionPC 43 = 64 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci43 :
    instructionPC 43 = 64 := by
  change submissionArtifact.instructionPC 43 = 64
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc44 :
    submissionArtifact.instructionPC 44 = 65 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci44 :
    instructionPC 44 = 65 := by
  change submissionArtifact.instructionPC 44 = 65
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc45 :
    submissionArtifact.instructionPC 45 = 66 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci45 :
    instructionPC 45 = 66 := by
  change submissionArtifact.instructionPC 45 = 66
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc46 :
    submissionArtifact.instructionPC 46 = 67 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci46 :
    instructionPC 46 = 67 := by
  change submissionArtifact.instructionPC 46 = 67
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc47 :
    submissionArtifact.instructionPC 47 = 68 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci47 :
    instructionPC 47 = 68 := by
  change submissionArtifact.instructionPC 47 = 68
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc48 :
    submissionArtifact.instructionPC 48 = 69 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci48 :
    instructionPC 48 = 69 := by
  change submissionArtifact.instructionPC 48 = 69
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc49 :
    submissionArtifact.instructionPC 49 = 70 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci49 :
    instructionPC 49 = 70 := by
  change submissionArtifact.instructionPC 49 = 70
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc50 :
    submissionArtifact.instructionPC 50 = 71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci50 :
    instructionPC 50 = 71 := by
  change submissionArtifact.instructionPC 50 = 71
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc51 :
    submissionArtifact.instructionPC 51 = 73 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci51 :
    instructionPC 51 = 73 := by
  change submissionArtifact.instructionPC 51 = 73
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc52 :
    submissionArtifact.instructionPC 52 = 74 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci52 :
    instructionPC 52 = 74 := by
  change submissionArtifact.instructionPC 52 = 74
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc53 :
    submissionArtifact.instructionPC 53 = 76 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci53 :
    instructionPC 53 = 76 := by
  change submissionArtifact.instructionPC 53 = 76
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc54 :
    submissionArtifact.instructionPC 54 = 77 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci54 :
    instructionPC 54 = 77 := by
  change submissionArtifact.instructionPC 54 = 77
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc55 :
    submissionArtifact.instructionPC 55 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci55 :
    instructionPC 55 = 98 := by
  change submissionArtifact.instructionPC 55 = 98
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc56 :
    submissionArtifact.instructionPC 56 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci56 :
    instructionPC 56 = 99 := by
  change submissionArtifact.instructionPC 56 = 99
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc57 :
    submissionArtifact.instructionPC 57 = 100 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci57 :
    instructionPC 57 = 100 := by
  change submissionArtifact.instructionPC 57 = 100
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc58 :
    submissionArtifact.instructionPC 58 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci58 :
    instructionPC 58 = 101 := by
  change submissionArtifact.instructionPC 58 = 101
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc59 :
    submissionArtifact.instructionPC 59 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci59 :
    instructionPC 59 = 102 := by
  change submissionArtifact.instructionPC 59 = 102
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc60 :
    submissionArtifact.instructionPC 60 = 103 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci60 :
    instructionPC 60 = 103 := by
  change submissionArtifact.instructionPC 60 = 103
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc61 :
    submissionArtifact.instructionPC 61 = 104 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci61 :
    instructionPC 61 = 104 := by
  change submissionArtifact.instructionPC 61 = 104
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc62 :
    submissionArtifact.instructionPC 62 = 105 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci62 :
    instructionPC 62 = 105 := by
  change submissionArtifact.instructionPC 62 = 105
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc63 :
    submissionArtifact.instructionPC 63 = 108 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci63 :
    instructionPC 63 = 108 := by
  change submissionArtifact.instructionPC 63 = 108
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc64 :
    submissionArtifact.instructionPC 64 = 109 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci64 :
    instructionPC 64 = 109 := by
  change submissionArtifact.instructionPC 64 = 109
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc65 :
    submissionArtifact.instructionPC 65 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci65 :
    instructionPC 65 = 110 := by
  change submissionArtifact.instructionPC 65 = 110
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc66 :
    submissionArtifact.instructionPC 66 = 111 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci66 :
    instructionPC 66 = 111 := by
  change submissionArtifact.instructionPC 66 = 111
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc67 :
    submissionArtifact.instructionPC 67 = 113 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci67 :
    instructionPC 67 = 113 := by
  change submissionArtifact.instructionPC 67 = 113
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc68 :
    submissionArtifact.instructionPC 68 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci68 :
    instructionPC 68 = 114 := by
  change submissionArtifact.instructionPC 68 = 114
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc69 :
    submissionArtifact.instructionPC 69 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci69 :
    instructionPC 69 = 115 := by
  change submissionArtifact.instructionPC 69 = 115
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc70 :
    submissionArtifact.instructionPC 70 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci70 :
    instructionPC 70 = 117 := by
  change submissionArtifact.instructionPC 70 = 117
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc71 :
    submissionArtifact.instructionPC 71 = 118 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci71 :
    instructionPC 71 = 118 := by
  change submissionArtifact.instructionPC 71 = 118
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc72 :
    submissionArtifact.instructionPC 72 = 119 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci72 :
    instructionPC 72 = 119 := by
  change submissionArtifact.instructionPC 72 = 119
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc73 :
    submissionArtifact.instructionPC 73 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci73 :
    instructionPC 73 = 121 := by
  change submissionArtifact.instructionPC 73 = 121
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc74 :
    submissionArtifact.instructionPC 74 = 122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci74 :
    instructionPC 74 = 122 := by
  change submissionArtifact.instructionPC 74 = 122
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc75 :
    submissionArtifact.instructionPC 75 = 125 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci75 :
    instructionPC 75 = 125 := by
  change submissionArtifact.instructionPC 75 = 125
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc76 :
    submissionArtifact.instructionPC 76 = 126 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci76 :
    instructionPC 76 = 126 := by
  change submissionArtifact.instructionPC 76 = 126
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc77 :
    submissionArtifact.instructionPC 77 = 128 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci77 :
    instructionPC 77 = 128 := by
  change submissionArtifact.instructionPC 77 = 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc78 :
    submissionArtifact.instructionPC 78 = 129 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci78 :
    instructionPC 78 = 129 := by
  change submissionArtifact.instructionPC 78 = 129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc79 :
    submissionArtifact.instructionPC 79 = 130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci79 :
    instructionPC 79 = 130 := by
  change submissionArtifact.instructionPC 79 = 130
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc80 :
    submissionArtifact.instructionPC 80 = 133 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci80 :
    instructionPC 80 = 133 := by
  change submissionArtifact.instructionPC 80 = 133
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc81 :
    submissionArtifact.instructionPC 81 = 134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci81 :
    instructionPC 81 = 134 := by
  change submissionArtifact.instructionPC 81 = 134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc82 :
    submissionArtifact.instructionPC 82 = 136 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci82 :
    instructionPC 82 = 136 := by
  change submissionArtifact.instructionPC 82 = 136
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc83 :
    submissionArtifact.instructionPC 83 = 137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci83 :
    instructionPC 83 = 137 := by
  change submissionArtifact.instructionPC 83 = 137
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc84 :
    submissionArtifact.instructionPC 84 = 157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci84 :
    instructionPC 84 = 157 := by
  change submissionArtifact.instructionPC 84 = 157
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc85 :
    submissionArtifact.instructionPC 85 = 158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci85 :
    instructionPC 85 = 158 := by
  change submissionArtifact.instructionPC 85 = 158
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc86 :
    submissionArtifact.instructionPC 86 = 160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci86 :
    instructionPC 86 = 160 := by
  change submissionArtifact.instructionPC 86 = 160
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc87 :
    submissionArtifact.instructionPC 87 = 161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci87 :
    instructionPC 87 = 161 := by
  change submissionArtifact.instructionPC 87 = 161
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc88 :
    submissionArtifact.instructionPC 88 = 162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci88 :
    instructionPC 88 = 162 := by
  change submissionArtifact.instructionPC 88 = 162
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc89 :
    submissionArtifact.instructionPC 89 = 163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci89 :
    instructionPC 89 = 163 := by
  change submissionArtifact.instructionPC 89 = 163
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc90 :
    submissionArtifact.instructionPC 90 = 164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci90 :
    instructionPC 90 = 164 := by
  change submissionArtifact.instructionPC 90 = 164
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc91 :
    submissionArtifact.instructionPC 91 = 165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci91 :
    instructionPC 91 = 165 := by
  change submissionArtifact.instructionPC 91 = 165
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc92 :
    submissionArtifact.instructionPC 92 = 168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci92 :
    instructionPC 92 = 168 := by
  change submissionArtifact.instructionPC 92 = 168
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc93 :
    submissionArtifact.instructionPC 93 = 169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci93 :
    instructionPC 93 = 169 := by
  change submissionArtifact.instructionPC 93 = 169
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc94 :
    submissionArtifact.instructionPC 94 = 171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci94 :
    instructionPC 94 = 171 := by
  change submissionArtifact.instructionPC 94 = 171
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc95 :
    submissionArtifact.instructionPC 95 = 172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci95 :
    instructionPC 95 = 172 := by
  change submissionArtifact.instructionPC 95 = 172
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc96 :
    submissionArtifact.instructionPC 96 = 174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci96 :
    instructionPC 96 = 174 := by
  change submissionArtifact.instructionPC 96 = 174
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc97 :
    submissionArtifact.instructionPC 97 = 177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci97 :
    instructionPC 97 = 177 := by
  change submissionArtifact.instructionPC 97 = 177
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc98 :
    submissionArtifact.instructionPC 98 = 178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci98 :
    instructionPC 98 = 178 := by
  change submissionArtifact.instructionPC 98 = 178
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc99 :
    submissionArtifact.instructionPC 99 = 180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci99 :
    instructionPC 99 = 180 := by
  change submissionArtifact.instructionPC 99 = 180
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc100 :
    submissionArtifact.instructionPC 100 = 181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci100 :
    instructionPC 100 = 181 := by
  change submissionArtifact.instructionPC 100 = 181
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc101 :
    submissionArtifact.instructionPC 101 = 184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci101 :
    instructionPC 101 = 184 := by
  change submissionArtifact.instructionPC 101 = 184
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc102 :
    submissionArtifact.instructionPC 102 = 185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci102 :
    instructionPC 102 = 185 := by
  change submissionArtifact.instructionPC 102 = 185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc103 :
    submissionArtifact.instructionPC 103 = 186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci103 :
    instructionPC 103 = 186 := by
  change submissionArtifact.instructionPC 103 = 186
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc104 :
    submissionArtifact.instructionPC 104 = 189 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci104 :
    instructionPC 104 = 189 := by
  change submissionArtifact.instructionPC 104 = 189
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc105 :
    submissionArtifact.instructionPC 105 = 190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci105 :
    instructionPC 105 = 190 := by
  change submissionArtifact.instructionPC 105 = 190
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc106 :
    submissionArtifact.instructionPC 106 = 191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci106 :
    instructionPC 106 = 191 := by
  change submissionArtifact.instructionPC 106 = 191
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc107 :
    submissionArtifact.instructionPC 107 = 192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci107 :
    instructionPC 107 = 192 := by
  change submissionArtifact.instructionPC 107 = 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc108 :
    submissionArtifact.instructionPC 108 = 194 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci108 :
    instructionPC 108 = 194 := by
  change submissionArtifact.instructionPC 108 = 194
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc109 :
    submissionArtifact.instructionPC 109 = 195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci109 :
    instructionPC 109 = 195 := by
  change submissionArtifact.instructionPC 109 = 195
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc110 :
    submissionArtifact.instructionPC 110 = 196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci110 :
    instructionPC 110 = 196 := by
  change submissionArtifact.instructionPC 110 = 196
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc111 :
    submissionArtifact.instructionPC 111 = 199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci111 :
    instructionPC 111 = 199 := by
  change submissionArtifact.instructionPC 111 = 199
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc112 :
    submissionArtifact.instructionPC 112 = 200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci112 :
    instructionPC 112 = 200 := by
  change submissionArtifact.instructionPC 112 = 200
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc113 :
    submissionArtifact.instructionPC 113 = 202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci113 :
    instructionPC 113 = 202 := by
  change submissionArtifact.instructionPC 113 = 202
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc114 :
    submissionArtifact.instructionPC 114 = 203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci114 :
    instructionPC 114 = 203 := by
  change submissionArtifact.instructionPC 114 = 203
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc115 :
    submissionArtifact.instructionPC 115 = 204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci115 :
    instructionPC 115 = 204 := by
  change submissionArtifact.instructionPC 115 = 204
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc116 :
    submissionArtifact.instructionPC 116 = 205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci116 :
    instructionPC 116 = 205 := by
  change submissionArtifact.instructionPC 116 = 205
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc117 :
    submissionArtifact.instructionPC 117 = 207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci117 :
    instructionPC 117 = 207 := by
  change submissionArtifact.instructionPC 117 = 207
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc118 :
    submissionArtifact.instructionPC 118 = 208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci118 :
    instructionPC 118 = 208 := by
  change submissionArtifact.instructionPC 118 = 208
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc119 :
    submissionArtifact.instructionPC 119 = 209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci119 :
    instructionPC 119 = 209 := by
  change submissionArtifact.instructionPC 119 = 209
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc120 :
    submissionArtifact.instructionPC 120 = 210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci120 :
    instructionPC 120 = 210 := by
  change submissionArtifact.instructionPC 120 = 210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc121 :
    submissionArtifact.instructionPC 121 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci121 :
    instructionPC 121 = 211 := by
  change submissionArtifact.instructionPC 121 = 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc122 :
    submissionArtifact.instructionPC 122 = 212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci122 :
    instructionPC 122 = 212 := by
  change submissionArtifact.instructionPC 122 = 212
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc123 :
    submissionArtifact.instructionPC 123 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci123 :
    instructionPC 123 = 214 := by
  change submissionArtifact.instructionPC 123 = 214
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc124 :
    submissionArtifact.instructionPC 124 = 215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci124 :
    instructionPC 124 = 215 := by
  change submissionArtifact.instructionPC 124 = 215
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc125 :
    submissionArtifact.instructionPC 125 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci125 :
    instructionPC 125 = 217 := by
  change submissionArtifact.instructionPC 125 = 217
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc126 :
    submissionArtifact.instructionPC 126 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci126 :
    instructionPC 126 = 218 := by
  change submissionArtifact.instructionPC 126 = 218
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc127 :
    submissionArtifact.instructionPC 127 = 219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci127 :
    instructionPC 127 = 219 := by
  change submissionArtifact.instructionPC 127 = 219
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc128 :
    submissionArtifact.instructionPC 128 = 220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci128 :
    instructionPC 128 = 220 := by
  change submissionArtifact.instructionPC 128 = 220
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc129 :
    submissionArtifact.instructionPC 129 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci129 :
    instructionPC 129 = 221 := by
  change submissionArtifact.instructionPC 129 = 221
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc130 :
    submissionArtifact.instructionPC 130 = 222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci130 :
    instructionPC 130 = 222 := by
  change submissionArtifact.instructionPC 130 = 222
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc131 :
    submissionArtifact.instructionPC 131 = 223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci131 :
    instructionPC 131 = 223 := by
  change submissionArtifact.instructionPC 131 = 223
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc132 :
    submissionArtifact.instructionPC 132 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci132 :
    instructionPC 132 = 225 := by
  change submissionArtifact.instructionPC 132 = 225
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc133 :
    submissionArtifact.instructionPC 133 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci133 :
    instructionPC 133 = 226 := by
  change submissionArtifact.instructionPC 133 = 226
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc134 :
    submissionArtifact.instructionPC 134 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci134 :
    instructionPC 134 = 227 := by
  change submissionArtifact.instructionPC 134 = 227
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc135 :
    submissionArtifact.instructionPC 135 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci135 :
    instructionPC 135 = 229 := by
  change submissionArtifact.instructionPC 135 = 229
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc136 :
    submissionArtifact.instructionPC 136 = 230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci136 :
    instructionPC 136 = 230 := by
  change submissionArtifact.instructionPC 136 = 230
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc137 :
    submissionArtifact.instructionPC 137 = 231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci137 :
    instructionPC 137 = 231 := by
  change submissionArtifact.instructionPC 137 = 231
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc138 :
    submissionArtifact.instructionPC 138 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci138 :
    instructionPC 138 = 232 := by
  change submissionArtifact.instructionPC 138 = 232
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc139 :
    submissionArtifact.instructionPC 139 = 234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci139 :
    instructionPC 139 = 234 := by
  change submissionArtifact.instructionPC 139 = 234
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc140 :
    submissionArtifact.instructionPC 140 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci140 :
    instructionPC 140 = 235 := by
  change submissionArtifact.instructionPC 140 = 235
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc141 :
    submissionArtifact.instructionPC 141 = 236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci141 :
    instructionPC 141 = 236 := by
  change submissionArtifact.instructionPC 141 = 236
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc142 :
    submissionArtifact.instructionPC 142 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci142 :
    instructionPC 142 = 237 := by
  change submissionArtifact.instructionPC 142 = 237
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc143 :
    submissionArtifact.instructionPC 143 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci143 :
    instructionPC 143 = 240 := by
  change submissionArtifact.instructionPC 143 = 240
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc144 :
    submissionArtifact.instructionPC 144 = 241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci144 :
    instructionPC 144 = 241 := by
  change submissionArtifact.instructionPC 144 = 241
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc145 :
    submissionArtifact.instructionPC 145 = 242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci145 :
    instructionPC 145 = 242 := by
  change submissionArtifact.instructionPC 145 = 242
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc146 :
    submissionArtifact.instructionPC 146 = 245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci146 :
    instructionPC 146 = 245 := by
  change submissionArtifact.instructionPC 146 = 245
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc147 :
    submissionArtifact.instructionPC 147 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci147 :
    instructionPC 147 = 246 := by
  change submissionArtifact.instructionPC 147 = 246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc148 :
    submissionArtifact.instructionPC 148 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci148 :
    instructionPC 148 = 247 := by
  change submissionArtifact.instructionPC 148 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc149 :
    submissionArtifact.instructionPC 149 = 278 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci149 :
    instructionPC 149 = 278 := by
  change submissionArtifact.instructionPC 149 = 278
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc150 :
    submissionArtifact.instructionPC 150 = 310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci150 :
    instructionPC 150 = 310 := by
  change submissionArtifact.instructionPC 150 = 310
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc151 :
    submissionArtifact.instructionPC 151 = 313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci151 :
    instructionPC 151 = 313 := by
  change submissionArtifact.instructionPC 151 = 313
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc152 :
    submissionArtifact.instructionPC 152 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci152 :
    instructionPC 152 = 316 := by
  change submissionArtifact.instructionPC 152 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc153 :
    submissionArtifact.instructionPC 153 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci153 :
    instructionPC 153 = 317 := by
  change submissionArtifact.instructionPC 153 = 317
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc154 :
    submissionArtifact.instructionPC 154 = 318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci154 :
    instructionPC 154 = 318 := by
  change submissionArtifact.instructionPC 154 = 318
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc155 :
    submissionArtifact.instructionPC 155 = 319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci155 :
    instructionPC 155 = 319 := by
  change submissionArtifact.instructionPC 155 = 319
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc156 :
    submissionArtifact.instructionPC 156 = 320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci156 :
    instructionPC 156 = 320 := by
  change submissionArtifact.instructionPC 156 = 320
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc157 :
    submissionArtifact.instructionPC 157 = 325 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci157 :
    instructionPC 157 = 325 := by
  change submissionArtifact.instructionPC 157 = 325
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc158 :
    submissionArtifact.instructionPC 158 = 330 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci158 :
    instructionPC 158 = 330 := by
  change submissionArtifact.instructionPC 158 = 330
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc159 :
    submissionArtifact.instructionPC 159 = 335 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci159 :
    instructionPC 159 = 335 := by
  change submissionArtifact.instructionPC 159 = 335
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc160 :
    submissionArtifact.instructionPC 160 = 340 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci160 :
    instructionPC 160 = 340 := by
  change submissionArtifact.instructionPC 160 = 340
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc161 :
    submissionArtifact.instructionPC 161 = 345 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci161 :
    instructionPC 161 = 345 := by
  change submissionArtifact.instructionPC 161 = 345
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc162 :
    submissionArtifact.instructionPC 162 = 359 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci162 :
    instructionPC 162 = 359 := by
  change submissionArtifact.instructionPC 162 = 359
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc163 :
    submissionArtifact.instructionPC 163 = 373 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci163 :
    instructionPC 163 = 373 := by
  change submissionArtifact.instructionPC 163 = 373
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc164 :
    submissionArtifact.instructionPC 164 = 401 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci164 :
    instructionPC 164 = 401 := by
  change submissionArtifact.instructionPC 164 = 401
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc165 :
    submissionArtifact.instructionPC 165 = 429 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci165 :
    instructionPC 165 = 429 := by
  change submissionArtifact.instructionPC 165 = 429
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc166 :
    submissionArtifact.instructionPC 166 = 434 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci166 :
    instructionPC 166 = 434 := by
  change submissionArtifact.instructionPC 166 = 434
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc167 :
    submissionArtifact.instructionPC 167 = 448 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci167 :
    instructionPC 167 = 448 := by
  change submissionArtifact.instructionPC 167 = 448
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc168 :
    submissionArtifact.instructionPC 168 = 450 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci168 :
    instructionPC 168 = 450 := by
  change submissionArtifact.instructionPC 168 = 450
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc169 :
    submissionArtifact.instructionPC 169 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci169 :
    instructionPC 169 = 451 := by
  change submissionArtifact.instructionPC 169 = 451
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc170 :
    submissionArtifact.instructionPC 170 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci170 :
    instructionPC 170 = 452 := by
  change submissionArtifact.instructionPC 170 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc171 :
    submissionArtifact.instructionPC 171 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci171 :
    instructionPC 171 = 453 := by
  change submissionArtifact.instructionPC 171 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc172 :
    submissionArtifact.instructionPC 172 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci172 :
    instructionPC 172 = 456 := by
  change submissionArtifact.instructionPC 172 = 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl


/-- The padding code is entered by fall-through; no return address is pushed. -/
def padEnterPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨148, .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255), by rfl, by decide⟩,
   ⟨149, .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), by rfl, by decide⟩]

/-- Cached located path for the fast-entry continuation, the zero offset and the calldata copy. -/
def padCopyPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨150, .push ⟨2, by decide⟩ (UInt256.ofNat 4768), by rfl, by decide⟩,
   ⟨151, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨152, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨154, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨155, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the fast-entry test: only the lengths 64, 128 and 192 (the
calldata size has no bit outside `0xc0`) go straight to the block loop. -/
def padGuardPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨167, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨168, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨169, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨171, .push ⟨2, by decide⟩ (UInt256.ofNat 104), by rfl, by decide⟩,
   ⟨172, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the sentinel byte. -/
def padSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨116, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨117, .op (.Dup ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨120, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the footer-loop setup. -/
def padFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨121, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨122, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨123, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨124, .push ⟨1, by decide⟩ (UInt256.ofNat 89), by rfl, by decide⟩,
   ⟨125, .op (.Dup ⟨14, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨126, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the footer-loop exit: the generic continuation 4757 replaces the rounded limit. -/
def padExitPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨140, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨141, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨142, .push ⟨2, by decide⟩ (UInt256.ofNat 4757), by rfl, by decide⟩,
   ⟨143, .op (.Swap ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨144, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨145, .push ⟨2, by decide⟩ (UInt256.ofNat 457), by rfl, by decide⟩,
   ⟨146, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
