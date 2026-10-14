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

The exact candidate has 5241 bytes, 3626 executable instructions and 280 data bytes, and SHA-256
`2d64429a7c81d31f56494a5be7e1be57807737772dca7ac5235d1ef4fb830633`. PUSH rows carry their typed width and value.
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
  .push 1 247,
  op 0x57,
  op 0x36,
  .push 2 1000,
  op 0x03,
  .push 2 4601,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 255,
  op 0x02,
  .push 1 97,
  op 0x01,
  .push 2 4805,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 2 960,
  .push 2 968,
  op 0x35,
  op 0x82,
  op 0x18,
  .push 1 200,
  op 0x56,
  op 0x5b,
  .push 1 128,
  op 0x8c,
  op 0x01,
  op 0x59,
  op 0x10,
  .push 2 4748,
  op 0x57,
  .push 1 47,
  op 0x9c,
  .push 1 132,
  op 0x56,
  op 0x5b,
  .push 2 1084,
  op 0x36,
  .push 1 28,
  op 0x37,
  op 0x36,
  .push 1 3,
  op 0x1b,
  op 0x80,
  .push 1 162,
  op 0x52,
  op 0x80,
  .push 2 666,
  op 0x52,
  .push 1 144,
  op 0x52,
  .push 1 128,
  op 0x80,
  op 0x80,
  .push 2 522,
  op 0x52,
  .push 1 67,
  op 0x53,
  .push 1 85,
  op 0x53,
  .push 2 4748,
  op 0x9c,
  op 0x50,
  .push 2 824,
  op 0x56,
  op 0x5b,
  .push 1 89,
  op 0x01,
  op 0x5b,
  op 0x81,
  op 0x81,
  op 0x53,
  .push 1 1,
  op 0x01,
  op 0x90,
  .push 1 8,
  .push 1 237,
  op 0x56,
  op 0x5b,
  .push 1 64,
  op 0x9c,
  op 0x5b,
  op 0x50,
  op 0x9a,
  .push 1 64,
  op 0x01,
  op 0x9a,
  .push 2 457,
  op 0x56,
  op 0x5b,
  .push 2 4748,
  op 0x9c,
  op 0x50,
  .push 1 128,
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
  .push 0 0,
  .push 1 157,
  op 0x52,
  .push 1 128,
  op 0x8c,
  op 0x36,
  op 0x01,
  op 0x53,
  op 0x36,
  .push 1 3,
  op 0x1b,
  op 0x36,
  .push 2 968,
  op 0x01,
  .push 1 63,
  op 0x17,
  .push 1 111,
  op 0x56,
  op 0x01,
  op 0x5b,
  .push 1 128,
  op 0x9c,
  .push 1 132,
  op 0x56,
  op 0x01,
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
  .push 1 200,
  op 0x57,
  .push 1 247,
  op 0x57,
  .push 2 4720,
  op 0x56,
  op 0x5b,
  op 0x1c,
  op 0x90,
  op 0x81,
  .push 1 115,
  .push 2 4708,
  op 0x56,
  op 0x5b
]

@[simp] private theorem submissionInstructionsChunk0_length : submissionInstructionsChunk0.length = 172 := by rfl

private def submissionInstructionsChunk1 : List Instr :=
[
.push 30 1766820105243087041267848467410591083712559083657179364930612997358944255,
  .push 31 450552876409790643671482431940419874915447411150352389258589821042463539455,
  op 0x36,
  .push 0 0,
  .push 2 1056,
  op 0x37,
  op 0x36,
  .push 2 1056,
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
  .push 1 143,
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
  op 0x16,
  .push 2 257
]

@[simp] private theorem submissionInstructionsChunk1_length : submissionInstructionsChunk1.length = 63 := by rfl

private def submissionInstructionsChunk2 : List Instr :=
[
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
  op 0x52,
  .push 22 95780971281817308448866066055358605703522837925462015
]

@[simp] private theorem submissionInstructionsChunk2_length : submissionInstructionsChunk2.length = 149 := by rfl

private def submissionInstructionsChunk3 : List Instr :=
[
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
  .push 22 95780971281817308448866066055358605703522833630494720,
  .push 22 95780971281817308448866066055358605703522837925462015,
  .push 2 360,
  op 0x51,
  .push 1 23,
  op 0x8c,
  op 0x8a
]

@[simp] private theorem submissionInstructionsChunk3_length : submissionInstructionsChunk3.length = 150 := by rfl

private def submissionInstructionsChunk4 : List Instr :=
[
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
  op 0x51,
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
  op 0x8c
]

@[simp] private theorem submissionInstructionsChunk4_length : submissionInstructionsChunk4.length = 223 := by rfl

private def submissionInstructionsChunk5 : List Instr :=
[
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
  op 0x01
]

@[simp] private theorem submissionInstructionsChunk5_length : submissionInstructionsChunk5.length = 214 := by rfl

private def submissionInstructionsChunk6 : List Instr :=
[
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
  op 0x17,
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
  op 0x01
]

@[simp] private theorem submissionInstructionsChunk6_length : submissionInstructionsChunk6.length = 195 := by rfl

private def submissionInstructionsChunk7 : List Instr :=
[
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
  op 0x8c
]

@[simp] private theorem submissionInstructionsChunk7_length : submissionInstructionsChunk7.length = 206 := by rfl

private def submissionInstructionsChunk8 : List Instr :=
[
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
  op 0x8d,
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
  op 0x17
]

@[simp] private theorem submissionInstructionsChunk8_length : submissionInstructionsChunk8.length = 208 := by rfl

private def submissionInstructionsChunk9 : List Instr :=
[
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
  op 0x18,
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
  op 0x89,
  op 0x01,
  op 0x01,
  op 0x86,
  op 0x16
]

@[simp] private theorem submissionInstructionsChunk9_length : submissionInstructionsChunk9.length = 185 := by rfl

private def submissionInstructionsChunk10 : List Instr :=
[
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
  op 0x16,
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
  op 0x1c
]

@[simp] private theorem submissionInstructionsChunk10_length : submissionInstructionsChunk10.length = 216 := by rfl

private def submissionInstructionsChunk11 : List Instr :=
[
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
  .push 2 576,
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
  op 0x8e
]

@[simp] private theorem submissionInstructionsChunk11_length : submissionInstructionsChunk11.length = 193 := by rfl

private def submissionInstructionsChunk12 : List Instr :=
[
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
  op 0x89,
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
  op 0x8c
]

@[simp] private theorem submissionInstructionsChunk12_length : submissionInstructionsChunk12.length = 214 := by rfl

private def submissionInstructionsChunk13 : List Instr :=
[
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
  .push 2 846,
  op 0x51,
  op 0x01,
  op 0x83,
  op 0x01,
  op 0x85,
  op 0x16
]

@[simp] private theorem submissionInstructionsChunk13_length : submissionInstructionsChunk13.length = 206 := by rfl

private def submissionInstructionsChunk14 : List Instr :=
[
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
  op 0x01,
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
  op 0x01
]

@[simp] private theorem submissionInstructionsChunk14_length : submissionInstructionsChunk14.length = 216 := by rfl

private def submissionInstructionsChunk15 : List Instr :=
[
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
  op 0x02
]

@[simp] private theorem submissionInstructionsChunk15_length : submissionInstructionsChunk15.length = 224 := by rfl

private def submissionInstructionsChunk16 : List Instr :=
[
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
  op 0x8c,
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
  op 0x95
]

@[simp] private theorem submissionInstructionsChunk16_length : submissionInstructionsChunk16.length = 219 := by rfl

private def submissionInstructionsChunk17 : List Instr :=
[
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
  .push 2 144,
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
  op 0x9c,
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
  .push 2 4891,
  op 0x57,
  .push 2 4917,
  op 0x56,
  op 0x5b,
  op 0x36,
  .push 1 1,
  .push 17 342276208914615837337402008677671501826,
  op 0x36,
  op 0x1c,
  op 0x16,
  .push 2 4808,
  op 0x57
]

@[simp] private theorem submissionInstructionsChunk17_length : submissionInstructionsChunk17.length = 213 := by rfl

private def submissionInstructionsChunk18 : List Instr :=
[
.push 2 256,
  op 0x14,
  .push 2 376,
  op 0x36,
  op 0x14,
  op 0x01,
  .push 2 4805,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 232,
  op 0x1d,
  op 0x36,
  .push 3 2127393,
  op 0x02,
  op 0x18,
  .push 1 247,
  op 0x57,
  .push 20 95383801997447390147238369573240532004699299169,
  op 0x36,
  op 0x1c,
  .push 20 802931186561056611446976448233794645126013734992,
  op 0x18,
  .push 2 4742,
  op 0x56,
  op 0x5b,
  op 0x57,
  op 0x50,
  op 0x50,
  .push 1 47,
  op 0x9c,
  op 0x50,
  .push 2 457,
  op 0x56,
  op 0x5b,
  .push 20 972889429405991776604892044862621566948497025487,
  op 0x5b,
  .push 0 0,
  op 0x52,
  op 0x59,
  .push 0 0,
  op 0xf3,
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
  .push 2 4917
]

@[simp] private theorem submissionInstructionsChunk18_length : submissionInstructionsChunk18.length = 102 := by rfl

private def submissionInstructionsChunk19 : List Instr :=
[
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
  .push 2 4891,
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
  .push 1 247,
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
  op 0xf3
]

@[simp] private theorem submissionInstructionsChunk19_length : submissionInstructionsChunk19.length = 58 := by rfl

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

theorem referenceInstructions_count : submissionInstructions.length = 3626 := by
  simp only [submissionInstructions, List.length_append, submissionInstructionsChunk0_length, submissionInstructionsChunk1_length, submissionInstructionsChunk2_length, submissionInstructionsChunk3_length, submissionInstructionsChunk4_length, submissionInstructionsChunk5_length, submissionInstructionsChunk6_length, submissionInstructionsChunk7_length, submissionInstructionsChunk8_length, submissionInstructionsChunk9_length, submissionInstructionsChunk10_length, submissionInstructionsChunk11_length, submissionInstructionsChunk12_length, submissionInstructionsChunk13_length, submissionInstructionsChunk14_length, submissionInstructionsChunk15_length, submissionInstructionsChunk16_length, submissionInstructionsChunk17_length, submissionInstructionsChunk18_length, submissionInstructionsChunk19_length]

private theorem submissionInstructionsChunk0_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk0 = [
  0x64, 0x10, 0x8c, 0x86, 0x82, 0x1c, 0x5f, 0x35, 0x16, 0x60, 0xf7, 0x57, 0x36, 0x61, 0x03, 0xe8, 0x03, 0x61, 0x11, 0xf9, 0x57, 0x5f, 0x35, 0x60, 0xff, 0x02, 0x60, 0x61, 0x01, 0x61, 0x12, 0xc5, 0x57, 0x5f, 0x35, 0x61, 0x03, 0xc0, 0x61, 0x03,
  0xc8, 0x35, 0x82, 0x18, 0x60, 0xc8, 0x56, 0x5b, 0x60, 0x80, 0x8c, 0x01, 0x59, 0x10, 0x61, 0x12, 0x8c, 0x57, 0x60, 0x2f, 0x9c, 0x60, 0x84, 0x56, 0x5b, 0x61, 0x04, 0x3c, 0x36, 0x60, 0x1c, 0x37, 0x36, 0x60, 0x03, 0x1b, 0x80, 0x60, 0xa2, 0x52,
  0x80, 0x61, 0x02, 0x9a, 0x52, 0x60, 0x90, 0x52, 0x60, 0x80, 0x80, 0x80, 0x61, 0x02, 0x0a, 0x52, 0x60, 0x43, 0x53, 0x60, 0x55, 0x53, 0x61, 0x12, 0x8c, 0x9c, 0x50, 0x61, 0x03, 0x38, 0x56, 0x5b, 0x60, 0x59, 0x01, 0x5b, 0x81, 0x81, 0x53, 0x60,
  0x01, 0x01, 0x90, 0x60, 0x08, 0x60, 0xed, 0x56, 0x5b, 0x60, 0x40, 0x9c, 0x5b, 0x50, 0x9a, 0x60, 0x40, 0x01, 0x9a, 0x61, 0x01, 0xc9, 0x56, 0x5b, 0x61, 0x12, 0x8c, 0x9c, 0x50, 0x60, 0x80, 0x60, 0xa5, 0x53, 0x84, 0x60, 0xbc, 0x53, 0x36, 0x60,
  0x20, 0x14, 0x61, 0x01, 0xee, 0x57, 0x5f, 0x60, 0x9d, 0x52, 0x60, 0x80, 0x8c, 0x36, 0x01, 0x53, 0x36, 0x60, 0x03, 0x1b, 0x36, 0x61, 0x03, 0xc8, 0x01, 0x60, 0x3f, 0x17, 0x60, 0x6f, 0x56, 0x01, 0x5b, 0x60, 0x80, 0x9c, 0x60, 0x84, 0x56, 0x01,
  0x5b, 0x60, 0x20, 0x82, 0x03, 0x35, 0x83, 0x18, 0x17, 0x60, 0x40, 0x82, 0x03, 0x35, 0x83, 0x18, 0x17, 0x60, 0x60, 0x82, 0x03, 0x91, 0x35, 0x83, 0x18, 0x17, 0x81, 0x60, 0xc8, 0x57, 0x60, 0xf7, 0x57, 0x61, 0x12, 0x70, 0x56, 0x5b, 0x1c, 0x90,
  0x81, 0x60, 0x73, 0x61, 0x12, 0x64, 0x56, 0x5b
] := by decide

private theorem submissionInstructionsChunk1_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk1 = [
  0x7d, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x7e, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00,
  0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x36, 0x5f, 0x61, 0x04, 0x20, 0x37, 0x36, 0x61, 0x04, 0x20, 0x63, 0x67, 0x45, 0x23, 0x01, 0x63, 0xef,
  0xcd, 0xab, 0x89, 0x63, 0x98, 0xba, 0xdc, 0xfe, 0x63, 0x10, 0x32, 0x54, 0x76, 0x63, 0xc3, 0xd2, 0xe1, 0xf0, 0x6c, 0x06, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x6c, 0x0e, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00,
  0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x7a, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7a, 0x01, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x63, 0xff, 0xff, 0xff, 0xff, 0x6c, 0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
  0x02, 0x60, 0xc0, 0x19, 0x36, 0x16, 0x60, 0x8f, 0x57, 0x5b, 0x8b, 0x61, 0x00, 0x20, 0x01, 0x51, 0x80, 0x60, 0x08, 0x1c, 0x81, 0x18, 0x8f, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x8f, 0x81, 0x80, 0x60, 0x10, 0x1c, 0x18, 0x16, 0x62, 0x01, 0x00,
  0x01, 0x02, 0x18, 0x60, 0xa2, 0x52, 0x5b, 0x8b, 0x51, 0x80, 0x60, 0x08, 0x1c, 0x81, 0x18, 0x8f, 0x16, 0x61, 0x01, 0x01
] := by decide

private theorem submissionInstructionsChunk2_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk2 = [
  0x02, 0x18, 0x8f, 0x81, 0x80, 0x61, 0x00, 0x10, 0x1c, 0x18, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x60, 0xfc, 0x52, 0x61, 0x00, 0x92, 0x51, 0x60, 0x80, 0x52, 0x60, 0xb2, 0x51, 0x60, 0xc4, 0x52, 0x60, 0xec, 0x51, 0x60, 0xda, 0x52, 0x61,
  0x01, 0x0c, 0x51, 0x61, 0x01, 0x1e, 0x52, 0x60, 0xb0, 0x51, 0x60, 0xa8, 0x51, 0x61, 0x01, 0x0a, 0x51, 0x61, 0x01, 0x0e, 0x51, 0x60, 0x8e, 0x51, 0x60, 0xac, 0x51, 0x60, 0xe8, 0x51, 0x61, 0x01, 0x02, 0x51, 0x60, 0xe4, 0x51, 0x60, 0xb4, 0x51,
  0x61, 0x01, 0x06, 0x51, 0x60, 0x92, 0x51, 0x60, 0x86, 0x51, 0x60, 0xec, 0x51, 0x60, 0xe0, 0x51, 0x60, 0x8a, 0x51, 0x80, 0x61, 0x03, 0x84, 0x52, 0x86, 0x61, 0x03, 0xf0, 0x52, 0x82, 0x61, 0x03, 0x72, 0x52, 0x84, 0x60, 0x7e, 0x52, 0x84, 0x61,
  0x03, 0x60, 0x52, 0x82, 0x61, 0x03, 0x4e, 0x52, 0x80, 0x61, 0x03, 0x3c, 0x52, 0x83, 0x61, 0x03, 0xa8, 0x52, 0x83, 0x61, 0x02, 0x2e, 0x52, 0x87, 0x61, 0x02, 0x1c, 0x52, 0x85, 0x60, 0x6c, 0x52, 0x8d, 0x61, 0x02, 0xac, 0x52, 0x8f, 0x58, 0x52,
  0x8d, 0x61, 0x01, 0x9e, 0x52, 0x61, 0x02, 0xf4, 0x52, 0x80, 0x61, 0x02, 0x0a, 0x52, 0x8d, 0x60, 0x5a, 0x52, 0x87, 0x60, 0x48, 0x52, 0x60, 0x36, 0x52, 0x85, 0x61, 0x01, 0xf8, 0x52, 0x83, 0x61, 0x04, 0x38, 0x52, 0x83, 0x61, 0x01, 0xe6, 0x52,
  0x88, 0x61, 0x04, 0x26, 0x52, 0x61, 0x03, 0xcc, 0x52, 0x88, 0x61, 0x00, 0xd8, 0x52, 0x83, 0x61, 0x02, 0x88, 0x52, 0x88, 0x61, 0x02, 0x76, 0x52, 0x83, 0x62, 0x00, 0x02, 0x64, 0x52, 0x58, 0x52, 0x88, 0x61, 0x01, 0x20, 0x52, 0x75, 0xff, 0xff,
  0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff
] := by decide

private theorem submissionInstructionsChunk3_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk3 = [
  0x16, 0x61, 0x02, 0x52, 0x52, 0x88, 0x61, 0x04, 0x14, 0x52, 0x61, 0x02, 0xd0, 0x52, 0x61, 0x01, 0x0e, 0x52, 0x81, 0x61, 0x01, 0x8c, 0x52, 0x80, 0x58, 0x52, 0x61, 0x01, 0xd4, 0x52, 0x60, 0x12, 0x52, 0x61, 0x01, 0x68, 0x52, 0x60, 0xc6, 0x52,
  0x61, 0x01, 0x44, 0x52, 0x60, 0xfc, 0x52, 0x5f, 0x52, 0x61, 0x01, 0xc2, 0x52, 0x60, 0xa2, 0x52, 0x5b, 0x88, 0x81, 0x02, 0x60, 0x17, 0x1c, 0x88, 0x88, 0x8d, 0x63, 0x50, 0xa2, 0x8b, 0xe6, 0x01, 0x61, 0x01, 0xe6, 0x51, 0x01, 0x8d, 0x8d, 0x8d,
  0x19, 0x17, 0x18, 0x01, 0x85, 0x16, 0x84, 0x02, 0x60, 0x19, 0x1c, 0x01, 0x84, 0x16, 0x84, 0x84, 0x86, 0x8f, 0x86, 0x19, 0x17, 0x84, 0x18, 0x60, 0xa2, 0x51, 0x8e, 0x01, 0x01, 0x63, 0x50, 0xa2, 0x8b, 0xe6, 0x01, 0x16, 0x02, 0x60, 0x18, 0x1c,
  0x83, 0x01, 0x16, 0x63, 0x50, 0xa2, 0x8b, 0xe6, 0x8e, 0x86, 0x02, 0x60, 0x17, 0x1c, 0x93, 0x83, 0x85, 0x19, 0x17, 0x83, 0x18, 0x01, 0x60, 0xfc, 0x51, 0x01, 0x01, 0x86, 0x16, 0x85, 0x02, 0x60, 0x18, 0x1c, 0x84, 0x01, 0x86, 0x16, 0x60, 0x90,
  0x1b, 0x8e, 0x17, 0x90, 0x60, 0x90, 0x1b, 0x8d, 0x17, 0x93, 0x60, 0x90, 0x1b, 0x8f, 0x17, 0x91, 0x85, 0x02, 0x60, 0x17, 0x1c, 0x60, 0x90, 0x1b, 0x8c, 0x17, 0x92, 0x60, 0x90, 0x1b, 0x8b, 0x17, 0x75, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x75, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0x61, 0x01,
  0x68, 0x51, 0x60, 0x17, 0x8c, 0x8a
] := by decide

private theorem submissionInstructionsChunk4_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk4 = [
  0x75, 0x50, 0xa2, 0x8b, 0xe6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x98, 0x86, 0x8c, 0x81, 0x16, 0x8c, 0x17, 0x8d, 0x18, 0x18, 0x89, 0x18, 0x01, 0x60, 0x36, 0x51, 0x01,
  0x89, 0x01, 0x85, 0x16, 0x81, 0x02, 0x60, 0x16, 0x1c, 0x87, 0x01, 0x85, 0x16, 0x9a, 0x81, 0x02, 0x83, 0x1c, 0x85, 0x16, 0x96, 0x87, 0x89, 0x88, 0x16, 0x17, 0x87, 0x18, 0x89, 0x8d, 0x18, 0x18, 0x01, 0x61, 0x03, 0x06, 0x51, 0x01, 0x89, 0x01,
  0x85, 0x16, 0x09, 0x60, 0x13, 0x1c, 0x88, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x81, 0x1c, 0x83, 0x16, 0x8c, 0x8f, 0x82, 0x9a, 0x89, 0x8d, 0x85, 0x8a, 0x82, 0x16, 0x17, 0x8a, 0x18, 0x18, 0x18, 0x01, 0x85, 0x01, 0x8a, 0x01, 0x86, 0x16, 0x8d,
  0x02, 0x60, 0x12, 0x1c, 0x88, 0x01, 0x86, 0x16, 0x9b, 0x8d, 0x02, 0x84, 0x1c, 0x86, 0x16, 0x97, 0x89, 0x88, 0x8a, 0x81, 0x83, 0x16, 0x17, 0x18, 0x18, 0x8d, 0x18, 0x01, 0x61, 0x03, 0x72, 0x51, 0x01, 0x8a, 0x01, 0x86, 0x16, 0x09, 0x60, 0x14,
  0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x81, 0x1c, 0x83, 0x16, 0x8d, 0x8b, 0x82, 0x9a, 0x89, 0x8d, 0x89, 0x16, 0x8d, 0x17, 0x89, 0x18, 0x18, 0x8d, 0x18, 0x01, 0x61, 0x01, 0x8c, 0x51, 0x01, 0x8a, 0x01, 0x86, 0x16, 0x8d, 0x02, 0x60, 0x1c,
  0x1c, 0x88, 0x01, 0x86, 0x16, 0x9b, 0x8d, 0x02, 0x84, 0x1c, 0x86, 0x16, 0x97, 0x89, 0x88, 0x8a, 0x81, 0x83, 0x16, 0x17, 0x18, 0x18, 0x8d, 0x18, 0x01, 0x61, 0x04, 0x38, 0x51, 0x01, 0x8a, 0x01, 0x86, 0x16, 0x09, 0x60, 0x19, 0x1c, 0x01, 0x83,
  0x16, 0x95, 0x8a, 0x02, 0x81, 0x1c, 0x83, 0x16, 0x8d, 0x8b, 0x82, 0x9a, 0x8c, 0x88, 0x16, 0x8c, 0x17, 0x8d, 0x89, 0x8c
] := by decide

private theorem submissionInstructionsChunk5_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk5 = [
  0x18, 0x18, 0x18, 0x01, 0x61, 0x04, 0x14, 0x51, 0x01, 0x8a, 0x01, 0x86, 0x16, 0x81, 0x02, 0x60, 0x1a, 0x1c, 0x88, 0x01, 0x86, 0x16, 0x9b, 0x81, 0x02, 0x84, 0x1c, 0x86, 0x16, 0x97, 0x8c, 0x8a, 0x8a, 0x81, 0x8b, 0x16, 0x17, 0x8a, 0x18, 0x18,
  0x18, 0x01, 0x61, 0x01, 0x20, 0x51, 0x01, 0x8a, 0x01, 0x86, 0x16, 0x09, 0x60, 0x18, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x81, 0x1c, 0x83, 0x16, 0x8c, 0x81, 0x99, 0x8b, 0x8b, 0x81, 0x89, 0x16, 0x17, 0x8a, 0x89, 0x18, 0x18, 0x18, 0x01,
  0x61, 0x03, 0xa8, 0x51, 0x01, 0x89, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x16, 0x1c, 0x87, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x83, 0x1c, 0x85, 0x16, 0x96, 0x87, 0x87, 0x8a, 0x16, 0x17, 0x8c, 0x18, 0x87, 0x8a, 0x18, 0x18, 0x01, 0x61, 0x03,
  0x2a, 0x51, 0x01, 0x89, 0x01, 0x85, 0x16, 0x6c, 0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x09, 0x60, 0x13, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x81, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x99, 0x88, 0x8c,
  0x88, 0x18, 0x18, 0x83, 0x8d, 0x89, 0x16, 0x17, 0x18, 0x01, 0x61, 0x01, 0x44, 0x51, 0x01, 0x89, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x13, 0x1c, 0x87, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x83, 0x1c, 0x85, 0x16, 0x96, 0x88, 0x87, 0x89, 0x81,
  0x83, 0x16, 0x17, 0x18, 0x18, 0x8c, 0x18, 0x01, 0x61, 0x03, 0x60, 0x51, 0x01, 0x89, 0x01, 0x85, 0x16, 0x6c, 0x0e, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x08, 0x09, 0x60, 0x14, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a,
  0x02, 0x81, 0x1c, 0x83, 0x16, 0x97, 0x89, 0x85, 0x16, 0x89, 0x17, 0x8a, 0x88, 0x18, 0x18, 0x85, 0x18, 0x01
] := by decide

private theorem submissionInstructionsChunk6_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk6 = [
  0x61, 0x01, 0xc2, 0x51, 0x01, 0x90, 0x96, 0x01, 0x82, 0x16, 0x89, 0x02, 0x60, 0x1b, 0x1c, 0x84, 0x01, 0x82, 0x16, 0x97, 0x89, 0x02, 0x86, 0x1c, 0x82, 0x16, 0x8b, 0x8f, 0x75, 0x5c, 0x4d, 0xd1, 0x24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x96, 0x8b, 0x89, 0x8d, 0x89, 0x16, 0x18, 0x85, 0x89, 0x16, 0x17, 0x85, 0x18, 0x18, 0x01, 0x61, 0x04, 0x26, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x09, 0x60, 0x19, 0x1c, 0x88,
  0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x97, 0x84, 0x87, 0x16, 0x8a, 0x18, 0x85, 0x8a, 0x16, 0x17, 0x87, 0x8a, 0x18, 0x18, 0x01, 0x60, 0x90, 0x51, 0x01, 0x85, 0x01, 0x8c, 0x80, 0x6c, 0x1e, 0x00, 0x00, 0x00, 0x1e, 0x00,
  0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x81, 0x93, 0x87, 0x16, 0x09, 0x89, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x8c, 0x88, 0x82, 0x16, 0x8b, 0x82, 0x8b, 0x16, 0x18, 0x17, 0x18, 0x18, 0x01,
  0x61, 0x03, 0xde, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x6c, 0xfe, 0x00, 0x00, 0x00, 0xfe, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x09, 0x60, 0x18, 0x1c, 0x89, 0x01, 0x84, 0x16, 0x96, 0x8b, 0x02, 0x88, 0x1c, 0x84, 0x16, 0x95, 0x63,
  0x5a, 0x82, 0x79, 0x99, 0x01, 0x98, 0x86, 0x8b, 0x88, 0x17, 0x89, 0x88, 0x18, 0x16, 0x18, 0x8b, 0x89, 0x16, 0x17, 0x01, 0x60, 0xfc, 0x51, 0x01, 0x89, 0x01, 0x84, 0x16, 0x8b, 0x02, 0x60, 0x1a, 0x1c, 0x82, 0x01, 0x84, 0x16, 0x99, 0x8b, 0x02,
  0x88, 0x1c, 0x84, 0x16, 0x91, 0x82, 0x8b, 0x87, 0x18, 0x89, 0x82, 0x17, 0x16, 0x18, 0x8b, 0x89, 0x16, 0x17, 0x01
] := by decide

private theorem submissionInstructionsChunk7_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk7 = [
  0x60, 0x48, 0x51, 0x01, 0x89, 0x01, 0x84, 0x16, 0x6c, 0x7e, 0x00, 0x00, 0x00, 0x7e, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x09, 0x60, 0x1a, 0x1c, 0x85, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96,
  0x87, 0x8c, 0x81, 0x17, 0x8a, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x60, 0xc6, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x19, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83,
  0x89, 0x85, 0x17, 0x8d, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x61, 0x01, 0xf8, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x6c, 0x1e, 0x00, 0x00, 0x00, 0x1e, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x10, 0x09, 0x88, 0x1c, 0x01,
  0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96, 0x87, 0x8c, 0x89, 0x17, 0x8a, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x61, 0x01, 0x44, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x16, 0x1c,
  0x83, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x89, 0x85, 0x17, 0x8d, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x61, 0x02, 0xac, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x6c, 0x06, 0x00, 0x00, 0x00,
  0x06, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x09, 0x60, 0x19, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96, 0x87, 0x8c, 0x89, 0x17, 0x8a, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01,
  0x61, 0x03, 0xf0, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x1a, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x9a, 0x8c
] := by decide

private theorem submissionInstructionsChunk8_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk8 = [
  0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x89, 0x85, 0x17, 0x8d, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x61, 0x03, 0xba, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x6c, 0x0e, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x08, 0x00,
  0x00, 0x00, 0x08, 0x09, 0x60, 0x14, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96, 0x87, 0x8c, 0x89, 0x17, 0x8a, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x61, 0x01, 0xc2, 0x51, 0x01, 0x8a,
  0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x1a, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x89, 0x85, 0x17, 0x8d, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17, 0x01, 0x60, 0x24, 0x51, 0x01, 0x8a, 0x01,
  0x85, 0x16, 0x6c, 0x7e, 0x00, 0x00, 0x00, 0x7e, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x40, 0x09, 0x60, 0x1a, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x94, 0x86, 0x8a, 0x16, 0x8a, 0x87, 0x17, 0x88, 0x87, 0x18,
  0x16, 0x87, 0x18, 0x17, 0x01, 0x61, 0x03, 0x3c, 0x51, 0x01, 0x88, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x12, 0x1c, 0x81, 0x01, 0x83, 0x16, 0x98, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x90, 0x81, 0x87, 0x17, 0x8a, 0x86, 0x18, 0x16, 0x82, 0x18,
  0x8a, 0x88, 0x16, 0x17, 0x01, 0x61, 0x01, 0xe6, 0x51, 0x01, 0x88, 0x01, 0x8f, 0x8d, 0x6c, 0x1e, 0x00, 0x00, 0x00, 0x1e, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x81, 0x93, 0x87, 0x16, 0x09, 0x89, 0x1c, 0x87, 0x01, 0x85, 0x16, 0x97,
  0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x96, 0x87, 0x8c, 0x81, 0x17, 0x8a, 0x89, 0x18, 0x16, 0x18, 0x8c, 0x8a, 0x16, 0x17
] := by decide

private theorem submissionInstructionsChunk9_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk9 = [
  0x01, 0x84, 0x01, 0x75, 0x6d, 0x70, 0x3e, 0xf3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5a, 0x82, 0x79, 0x99, 0x9a, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x16, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x9a,
  0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x87, 0x8a, 0x8e, 0x83, 0x16, 0x18, 0x8e, 0x82, 0x18, 0x16, 0x18, 0x18, 0x01, 0x61, 0x02, 0x9a, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x09, 0x60, 0x19, 0x1c, 0x85, 0x01, 0x83, 0x16, 0x95, 0x8a,
  0x02, 0x87, 0x1c, 0x83, 0x16, 0x94, 0x85, 0x85, 0x18, 0x8a, 0x88, 0x88, 0x16, 0x18, 0x88, 0x87, 0x18, 0x16, 0x18, 0x01, 0x60, 0x7e, 0x51, 0x01, 0x88, 0x01, 0x6c, 0x7e, 0x00, 0x00, 0x00, 0x7e, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x40,
  0x8e, 0x91, 0x85, 0x16, 0x09, 0x60, 0x19, 0x1c, 0x81, 0x01, 0x83, 0x16, 0x98, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x97, 0x86, 0x8a, 0x8a, 0x16, 0x18, 0x8a, 0x86, 0x18, 0x16, 0x89, 0x86, 0x18, 0x18, 0x01, 0x61, 0x02, 0x2e, 0x51, 0x01, 0x01,
  0x8d, 0x8c, 0x91, 0x84, 0x16, 0x09, 0x60, 0x14, 0x1c, 0x84, 0x01, 0x82, 0x16, 0x94, 0x89, 0x02, 0x86, 0x1c, 0x82, 0x16, 0x8c, 0x8a, 0x81, 0x76, 0x01, 0x6d, 0x70, 0x3e, 0xf2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x01, 0x6e, 0xd9, 0xeb, 0xa1, 0x97, 0x84, 0x8d, 0x19, 0x8b, 0x17, 0x18, 0x01, 0x61, 0x03, 0xcc, 0x51, 0x01, 0x88, 0x01, 0x86, 0x16, 0x8d, 0x02, 0x60, 0x16, 0x1c, 0x8b, 0x01, 0x86, 0x16, 0x9b, 0x8d, 0x02, 0x8a, 0x1c, 0x86, 0x16,
  0x9a, 0x8b, 0x8d, 0x8b, 0x19, 0x17, 0x18, 0x01, 0x61, 0x01, 0x32, 0x51, 0x89, 0x01, 0x01, 0x86, 0x16
] := by decide

private theorem submissionInstructionsChunk10_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk10 = [
  0x6c, 0x3e, 0x00, 0x00, 0x00, 0x3e, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x20, 0x09, 0x60, 0x18, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x97, 0x81, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x8c, 0x19, 0x8a, 0x17, 0x18, 0x01, 0x60, 0xa2, 0x51,
  0x01, 0x87, 0x01, 0x85, 0x16, 0x81, 0x02, 0x60, 0x1b, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x81, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x8a, 0x8c, 0x8a, 0x19, 0x17, 0x18, 0x01, 0x60, 0x12, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x09, 0x60, 0x1a,
  0x1c, 0x81, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8c, 0x8f, 0x82, 0x93, 0x83, 0x8d, 0x19, 0x8b, 0x17, 0x18, 0x01, 0x61, 0x03, 0x3c, 0x51, 0x01, 0x88, 0x01, 0x86, 0x16, 0x8d, 0x02, 0x60, 0x13, 0x1c, 0x8b, 0x01, 0x86,
  0x16, 0x9b, 0x8d, 0x02, 0x8a, 0x1c, 0x86, 0x16, 0x9a, 0x8c, 0x8a, 0x19, 0x17, 0x8c, 0x18, 0x01, 0x61, 0x02, 0x64, 0x51, 0x01, 0x88, 0x01, 0x86, 0x16, 0x09, 0x88, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81,
  0x92, 0x83, 0x8c, 0x19, 0x8a, 0x17, 0x18, 0x01, 0x61, 0x03, 0xa8, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x14, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x8a, 0x8c, 0x8a, 0x19, 0x17, 0x18,
  0x01, 0x61, 0x01, 0xd4, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x6d, 0x07, 0xfe, 0x00, 0x00, 0x07, 0xfe, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x00, 0x09, 0x60, 0x1b, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8c,
  0x81, 0x92, 0x83, 0x8c, 0x19, 0x8a, 0x17, 0x18, 0x01, 0x84, 0x01, 0x87, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x13, 0x1c
] := by decide

private theorem submissionInstructionsChunk11_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk11 = [
  0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x8a, 0x8c, 0x8a, 0x19, 0x17, 0x18, 0x01, 0x60, 0xea, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x6c, 0x3e, 0x00, 0x00, 0x00, 0x3e, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x09, 0x60, 0x18, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x90, 0x81, 0x8a, 0x19, 0x88, 0x17, 0x18, 0x01, 0x60, 0x36, 0x51, 0x01, 0x85, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x14, 0x1c, 0x88, 0x01, 0x83, 0x16,
  0x98, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x97, 0x88, 0x8a, 0x88, 0x19, 0x17, 0x18, 0x01, 0x61, 0x01, 0x9e, 0x51, 0x01, 0x85, 0x01, 0x8e, 0x8d, 0x6c, 0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x81, 0x93,
  0x87, 0x16, 0x09, 0x60, 0x1a, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x97, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x83, 0x8c, 0x19, 0x8a, 0x17, 0x18, 0x01, 0x60, 0xc6, 0x51, 0x01, 0x75, 0x7a, 0x6d, 0x76, 0xe9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x6e, 0xd9, 0xeb, 0xa1, 0x97, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x1c, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x8a, 0x8c, 0x8f, 0x18, 0x8a, 0x8e, 0x8e,
  0x16, 0x18, 0x16, 0x8f, 0x18, 0x18, 0x01, 0x61, 0x02, 0x40, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x09, 0x60, 0x14, 0x1c, 0x81, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x90, 0x81, 0x8c, 0x81, 0x89, 0x16, 0x8c, 0x18, 0x8e,
  0x8a, 0x18, 0x16, 0x18, 0x18, 0x01, 0x61, 0x02, 0xbe, 0x51, 0x01, 0x85, 0x01, 0x8e, 0x8e
] := by decide

private theorem submissionInstructionsChunk12_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk12 = [
  0x6c, 0x06, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x8f, 0x93, 0x87, 0x16, 0x09, 0x60, 0x1b, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x8a, 0x8c, 0x8f, 0x18, 0x8a, 0x8e,
  0x8e, 0x16, 0x18, 0x16, 0x8f, 0x18, 0x18, 0x01, 0x60, 0x5a, 0x51, 0x01, 0x87, 0x01, 0x85, 0x16, 0x09, 0x60, 0x1b, 0x1c, 0x81, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x94, 0x63, 0x20, 0x41, 0xd1, 0x3b, 0x01, 0x90, 0x86,
  0x8a, 0x86, 0x17, 0x18, 0x8a, 0x86, 0x16, 0x87, 0x18, 0x16, 0x8a, 0x18, 0x01, 0x61, 0x03, 0x18, 0x51, 0x01, 0x81, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x16, 0x1c, 0x88, 0x01, 0x83, 0x16, 0x98, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x97, 0x84,
  0x87, 0x16, 0x89, 0x18, 0x85, 0x88, 0x17, 0x8b, 0x18, 0x16, 0x87, 0x18, 0x01, 0x61, 0x03, 0x84, 0x51, 0x01, 0x81, 0x01, 0x83, 0x16, 0x8f, 0x8d, 0x91, 0x09, 0x60, 0x14, 0x1c, 0x85, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16,
  0x8d, 0x81, 0x96, 0x87, 0x87, 0x8d, 0x16, 0x18, 0x87, 0x8d, 0x17, 0x8a, 0x18, 0x16, 0x8c, 0x18, 0x01, 0x61, 0x02, 0x52, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x13, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c,
  0x85, 0x16, 0x99, 0x8a, 0x87, 0x8a, 0x16, 0x18, 0x8c, 0x8a, 0x89, 0x17, 0x18, 0x16, 0x89, 0x18, 0x01, 0x61, 0x02, 0x76, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x6d, 0x03, 0xfe, 0x00, 0x00, 0x03, 0xfe, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x02,
  0x00, 0x09, 0x60, 0x1a, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96, 0x88, 0x8c
] := by decide

private theorem submissionInstructionsChunk13_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk13 = [
  0x88, 0x17, 0x18, 0x8c, 0x88, 0x16, 0x89, 0x18, 0x16, 0x8c, 0x18, 0x01, 0x60, 0x36, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x13, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x88, 0x8c, 0x81,
  0x89, 0x17, 0x18, 0x8c, 0x89, 0x83, 0x16, 0x18, 0x16, 0x18, 0x01, 0x61, 0x02, 0xe2, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x6d, 0x03, 0xfe, 0x00, 0x00, 0x03, 0xfe, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x09, 0x60, 0x1a, 0x1c, 0x01,
  0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8c, 0x81, 0x96, 0x8b, 0x87, 0x81, 0x17, 0x8a, 0x18, 0x89, 0x89, 0x83, 0x16, 0x18, 0x16, 0x18, 0x01, 0x61, 0x01, 0xc2, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x18, 0x1c,
  0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x8a, 0x87, 0x8a, 0x16, 0x18, 0x8c, 0x8a, 0x89, 0x17, 0x18, 0x16, 0x89, 0x18, 0x01, 0x61, 0x01, 0x7a, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x6c, 0x1e, 0x00, 0x00, 0x00,
  0x1e, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x09, 0x60, 0x18, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96, 0x88, 0x8c, 0x88, 0x17, 0x18, 0x8c, 0x88, 0x16, 0x89, 0x18, 0x16, 0x8c, 0x18, 0x01,
  0x60, 0xc6, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x18, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x88, 0x8c, 0x81, 0x89, 0x17, 0x18, 0x8c, 0x89, 0x83, 0x16, 0x18, 0x16, 0x18, 0x01, 0x61,
  0x03, 0x4e, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16
] := by decide

private theorem submissionInstructionsChunk14_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk14 = [
  0x6c, 0x06, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x09, 0x60, 0x14, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8c, 0x81, 0x96, 0x8b, 0x87, 0x81, 0x17, 0x8a, 0x18, 0x89, 0x89, 0x83,
  0x16, 0x18, 0x16, 0x18, 0x01, 0x60, 0xfc, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x8c, 0x02, 0x60, 0x1c, 0x1c, 0x8a, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x99, 0x88, 0x8c, 0x8a, 0x89, 0x17, 0x18, 0x8c, 0x89, 0x83, 0x16,
  0x18, 0x16, 0x18, 0x01, 0x61, 0x02, 0x88, 0x51, 0x01, 0x83, 0x01, 0x85, 0x16, 0x6d, 0x03, 0xfe, 0x00, 0x00, 0x03, 0xfe, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x09, 0x60, 0x1a, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c,
  0x83, 0x16, 0x94, 0x86, 0x8a, 0x86, 0x17, 0x18, 0x8a, 0x86, 0x16, 0x87, 0x18, 0x16, 0x8a, 0x18, 0x01, 0x60, 0xa2, 0x51, 0x01, 0x01, 0x82, 0x16, 0x89, 0x02, 0x60, 0x19, 0x1c, 0x87, 0x01, 0x82, 0x16, 0x97, 0x89, 0x02, 0x86, 0x1c, 0x82, 0x16,
  0x8b, 0x8f, 0x63, 0x8f, 0x1b, 0xbc, 0xdc, 0x99, 0x86, 0x8c, 0x8a, 0x18, 0x17, 0x84, 0x16, 0x89, 0x18, 0x8c, 0x88, 0x16, 0x18, 0x01, 0x60, 0x6c, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x09, 0x60, 0x1a, 0x1c, 0x85, 0x01, 0x83, 0x16, 0x95, 0x8a,
  0x02, 0x87, 0x1c, 0x83, 0x16, 0x94, 0x85, 0x8a, 0x88, 0x18, 0x86, 0x17, 0x16, 0x85, 0x88, 0x16, 0x18, 0x8a, 0x18, 0x01, 0x61, 0x04, 0x02, 0x51, 0x01, 0x88, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x1c, 0x1c, 0x81, 0x01, 0x83, 0x16, 0x98, 0x8a,
  0x02, 0x87, 0x1c, 0x83, 0x16, 0x90, 0x84, 0x8a, 0x16, 0x87, 0x18, 0x82, 0x88, 0x8c, 0x18, 0x87, 0x17, 0x16, 0x18, 0x01
] := by decide

private theorem submissionInstructionsChunk15_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk15 = [
  0x61, 0x01, 0x56, 0x51, 0x01, 0x63, 0xa9, 0x53, 0xfd, 0x4e, 0x98, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x15, 0x1c, 0x85, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8c, 0x8f, 0x8f, 0x85, 0x93, 0x98, 0x8f, 0x8a, 0x8f, 0x82,
  0x16, 0x17, 0x8c, 0x18, 0x8f, 0x18, 0x18, 0x01, 0x61, 0x01, 0x8c, 0x51, 0x01, 0x8c, 0x01, 0x87, 0x16, 0x8e, 0x02, 0x60, 0x18, 0x1c, 0x85, 0x01, 0x87, 0x16, 0x9c, 0x8e, 0x02, 0x8b, 0x1c, 0x87, 0x16, 0x94, 0x8f, 0x80, 0x8c, 0x16, 0x87, 0x17,
  0x18, 0x8b, 0x18, 0x8e, 0x18, 0x01, 0x61, 0x02, 0x0a, 0x51, 0x01, 0x8c, 0x01, 0x87, 0x16, 0x6c, 0x0e, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x08, 0x09, 0x60, 0x14, 0x1c, 0x88, 0x01, 0x86, 0x16, 0x98, 0x8d, 0x02,
  0x8a, 0x1c, 0x86, 0x16, 0x97, 0x8e, 0x8d, 0x8a, 0x82, 0x82, 0x16, 0x17, 0x18, 0x8b, 0x18, 0x18, 0x01, 0x61, 0x02, 0xd0, 0x51, 0x01, 0x8b, 0x01, 0x86, 0x16, 0x8d, 0x02, 0x60, 0x1c, 0x1c, 0x84, 0x01, 0x86, 0x16, 0x9b, 0x8d, 0x02, 0x8a, 0x1c,
  0x86, 0x16, 0x93, 0x8e, 0x8a, 0x86, 0x82, 0x82, 0x16, 0x17, 0x18, 0x18, 0x8d, 0x18, 0x01, 0x61, 0x02, 0xf4, 0x51, 0x01, 0x8b, 0x01, 0x86, 0x16, 0x09, 0x60, 0x15, 0x1c, 0x86, 0x01, 0x84, 0x16, 0x96, 0x8b, 0x02, 0x88, 0x1c, 0x84, 0x16, 0x95,
  0x86, 0x8b, 0x8e, 0x16, 0x17, 0x8b, 0x8e, 0x18, 0x89, 0x18, 0x18, 0x01, 0x60, 0xfc, 0x51, 0x01, 0x89, 0x01, 0x84, 0x16, 0x8b, 0x02, 0x60, 0x1b, 0x1c, 0x82, 0x01, 0x84, 0x16, 0x99, 0x8b, 0x02, 0x88, 0x1c, 0x84, 0x16, 0x91, 0x8c, 0x88, 0x84,
  0x82, 0x8b, 0x16, 0x17, 0x18, 0x8c, 0x18, 0x18, 0x01, 0x61, 0x01, 0xb0, 0x51, 0x01, 0x89, 0x01, 0x84, 0x16, 0x8b, 0x02
] := by decide

private theorem submissionInstructionsChunk16_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk16 = [
  0x60, 0x19, 0x1c, 0x86, 0x01, 0x84, 0x16, 0x96, 0x8b, 0x02, 0x88, 0x1c, 0x84, 0x16, 0x95, 0x8c, 0x8b, 0x81, 0x81, 0x16, 0x89, 0x17, 0x18, 0x89, 0x18, 0x18, 0x01, 0x01, 0x88, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x14, 0x1c, 0x81, 0x01, 0x83,
  0x16, 0x98, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x90, 0x8b, 0x82, 0x88, 0x8e, 0x16, 0x17, 0x88, 0x18, 0x8b, 0x18, 0x18, 0x01, 0x60, 0xd8, 0x51, 0x01, 0x88, 0x01, 0x6c, 0x7e, 0x00, 0x00, 0x00, 0x7e, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00,
  0x40, 0x8e, 0x91, 0x85, 0x16, 0x09, 0x60, 0x1a, 0x1c, 0x85, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8c, 0x8f, 0x82, 0x97, 0x8c, 0x8f, 0x18, 0x8f, 0x8e, 0x16, 0x85, 0x17, 0x8b, 0x18, 0x18, 0x01, 0x60, 0xa2, 0x51, 0x01,
  0x8b, 0x01, 0x86, 0x16, 0x8d, 0x02, 0x60, 0x1c, 0x1c, 0x84, 0x01, 0x86, 0x16, 0x9b, 0x8d, 0x02, 0x8a, 0x1c, 0x86, 0x16, 0x93, 0x8e, 0x8a, 0x16, 0x85, 0x17, 0x8a, 0x18, 0x8f, 0x8e, 0x18, 0x18, 0x01, 0x61, 0x02, 0x1c, 0x51, 0x01, 0x8b, 0x01,
  0x86, 0x16, 0x09, 0x60, 0x14, 0x1c, 0x01, 0x83, 0x16, 0x95, 0x8a, 0x02, 0x87, 0x1c, 0x83, 0x16, 0x8d, 0x81, 0x96, 0x8d, 0x8c, 0x81, 0x81, 0x16, 0x8a, 0x17, 0x18, 0x8a, 0x18, 0x18, 0x01, 0x61, 0x03, 0xcc, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16,
  0x8c, 0x02, 0x60, 0x14, 0x1c, 0x83, 0x01, 0x85, 0x16, 0x9a, 0x8c, 0x02, 0x89, 0x1c, 0x85, 0x16, 0x92, 0x8d, 0x89, 0x81, 0x81, 0x16, 0x86, 0x17, 0x18, 0x18, 0x8c, 0x18, 0x01, 0x61, 0x03, 0x96, 0x51, 0x01, 0x8a, 0x01, 0x85, 0x16, 0x6c, 0x0e,
  0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x08, 0x09, 0x60, 0x15, 0x1c, 0x01, 0x83, 0x16, 0x95
] := by decide

private theorem submissionInstructionsChunk17_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk17 = [
  0x8a, 0x02, 0x87, 0x1c, 0x94, 0x8b, 0x8a, 0x81, 0x81, 0x16, 0x88, 0x17, 0x18, 0x88, 0x18, 0x18, 0x01, 0x61, 0x02, 0x52, 0x51, 0x01, 0x88, 0x01, 0x83, 0x16, 0x8a, 0x02, 0x60, 0x16, 0x1c, 0x81, 0x01, 0x83, 0x16, 0x98, 0x8a, 0x02, 0x87, 0x1c,
  0x8a, 0x87, 0x02, 0x88, 0x1c, 0x8c, 0x8b, 0x83, 0x19, 0x8a, 0x17, 0x18, 0x5f, 0x51, 0x85, 0x01, 0x01, 0x8b, 0x01, 0x16, 0x8c, 0x02, 0x60, 0x19, 0x1c, 0x87, 0x01, 0x8d, 0x16, 0x61, 0x02, 0x64, 0x51, 0x8b, 0x82, 0x8e, 0x85, 0x19, 0x17, 0x18,
  0x01, 0x01, 0x88, 0x01, 0x8e, 0x16, 0x8d, 0x02, 0x60, 0x1c, 0x1c, 0x83, 0x01, 0x8c, 0x8e, 0x02, 0x8b, 0x1c, 0x9b, 0x81, 0x83, 0x8e, 0x19, 0x17, 0x18, 0x85, 0x01, 0x60, 0xc6, 0x51, 0x01, 0x01, 0x8f, 0x16, 0x8e, 0x02, 0x60, 0x1b, 0x1c, 0x83,
  0x01, 0x93, 0x61, 0x00, 0x90, 0x1c, 0x01, 0x96, 0x50, 0x8c, 0x02, 0x93, 0x50, 0x96, 0x61, 0x00, 0x90, 0x1c, 0x01, 0x94, 0x61, 0x00, 0x90, 0x1c, 0x92, 0x50, 0x61, 0x00, 0x90, 0x1c, 0x97, 0x60, 0x90, 0x1c, 0x95, 0x1c, 0x01, 0x8f, 0x01, 0x88,
  0x16, 0x9f, 0x01, 0x87, 0x16, 0x9f, 0x01, 0x86, 0x16, 0x9a, 0x01, 0x01, 0x84, 0x16, 0x99, 0x01, 0x01, 0x82, 0x16, 0x98, 0x9c, 0x56, 0x5b, 0x91, 0x85, 0x60, 0x02, 0x1b, 0x81, 0x81, 0x17, 0x60, 0x09, 0x81, 0x92, 0x05, 0x01, 0x18, 0x18, 0x91,
  0x60, 0xfb, 0x87, 0x01, 0x80, 0x36, 0x03, 0x80, 0x36, 0x1d, 0x16, 0x01, 0x60, 0x20, 0x81, 0x03, 0x94, 0x50, 0x96, 0x91, 0x84, 0x11, 0x61, 0x13, 0x1b, 0x57, 0x61, 0x13, 0x35, 0x56, 0x5b, 0x36, 0x60, 0x01, 0x70, 0x01, 0x01, 0x80, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x03, 0x81, 0x80, 0x00, 0x01, 0x80, 0x00, 0x00, 0x02, 0x36, 0x1c, 0x16, 0x61, 0x12, 0xc8, 0x57
] := by decide

private theorem submissionInstructionsChunk18_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk18 = [
  0x61, 0x01, 0x00, 0x14, 0x61, 0x01, 0x78, 0x36, 0x14, 0x01, 0x61, 0x12, 0xc5, 0x57, 0x5f, 0x35, 0x60, 0xe8, 0x1d, 0x36, 0x62, 0x20, 0x76, 0x21, 0x02, 0x18, 0x60, 0xf7, 0x57, 0x73, 0x10, 0xb5, 0x28, 0x59, 0x05, 0x16, 0xb2, 0x62, 0xaf, 0xd6,
  0x90, 0x1a, 0xb0, 0x2b, 0x21, 0xf1, 0x6e, 0xaa, 0xdd, 0x61, 0x36, 0x1c, 0x73, 0x8c, 0xa4, 0xad, 0xfc, 0xc0, 0xff, 0x4e, 0x36, 0xce, 0xfe, 0x98, 0x8d, 0xce, 0xc3, 0xd4, 0xb9, 0xdc, 0x8f, 0x50, 0x50, 0x18, 0x61, 0x12, 0x86, 0x56, 0x5b, 0x57,
  0x50, 0x50, 0x60, 0x2f, 0x9c, 0x50, 0x61, 0x01, 0xc9, 0x56, 0x5b, 0x73, 0xaa, 0x69, 0xde, 0xee, 0x9a, 0x89, 0x22, 0xe9, 0x2f, 0x81, 0x05, 0xe0, 0x07, 0xf7, 0x61, 0x10, 0xf3, 0x81, 0xe9, 0xcf, 0x5b, 0x5f, 0x52, 0x59, 0x5f, 0xf3, 0x5b, 0x50,
  0x50, 0x50, 0x50, 0x50, 0x50, 0x60, 0x10, 0x52, 0x60, 0x0c, 0x52, 0x60, 0x08, 0x52, 0x60, 0x04, 0x52, 0x5f, 0x52, 0x60, 0x10, 0x51, 0x61, 0x01, 0x01, 0x81, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x85, 0x16, 0x02, 0x18, 0x80, 0x81, 0x60, 0x10, 0x1c,
  0x18, 0x85, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x60, 0xfb, 0x5b, 0x7f, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60,
  0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x80, 0x19, 0x60, 0x20, 0x83, 0x03, 0x7f, 0x07, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0x0a, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0x0d, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb,
  0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82, 0x5f, 0x5f, 0x60, 0x21, 0x36, 0x10, 0x61, 0x13, 0x35
] := by decide

private theorem submissionInstructionsChunk19_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk19 = [
  0x57, 0x5b, 0x81, 0x60, 0x20, 0x01, 0x91, 0x35, 0x85, 0x84, 0x17, 0x87, 0x81, 0x03, 0x18, 0x84, 0x18, 0x93, 0x18, 0x17, 0x83, 0x82, 0x10, 0x61, 0x13, 0x1b, 0x57, 0x5b, 0x81, 0x35, 0x83, 0x18, 0x84, 0x83, 0x03, 0x60, 0x03, 0x1b, 0x1c, 0x17,
  0x36, 0x87, 0x03, 0x61, 0x11, 0xc9, 0x57, 0x60, 0xf7, 0x57, 0x60, 0x14, 0x60, 0x0f, 0x36, 0x62, 0xdb, 0x14, 0x7b, 0x04, 0x16, 0x81, 0x02, 0x38, 0x03, 0x60, 0x0c, 0x39, 0x59, 0x5f, 0xf3
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
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk0).length = 248 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk1_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk1).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk2_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk2).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk3_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk3).length = 246 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk4_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk4).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk5_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk5).length = 258 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk6_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk6).length = 259 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk7_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk7).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk8_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk8).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk9_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk9).length = 257 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk10_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk10).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk11_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk11).length = 255 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk12_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk12).length = 260 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem chunk13_byteLength :
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk13).length = 248 := by
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
    (Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk18).length = 260 := by
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

private theorem tailPrefix_length : tailPrefix.length = 3568 := by
  simp only [tailPrefix, List.length_append, submissionInstructionsChunk0_length, submissionInstructionsChunk1_length, submissionInstructionsChunk2_length, submissionInstructionsChunk3_length, submissionInstructionsChunk4_length, submissionInstructionsChunk5_length, submissionInstructionsChunk6_length, submissionInstructionsChunk7_length, submissionInstructionsChunk8_length, submissionInstructionsChunk9_length, submissionInstructionsChunk10_length, submissionInstructionsChunk11_length, submissionInstructionsChunk12_length, submissionInstructionsChunk13_length, submissionInstructionsChunk14_length, submissionInstructionsChunk15_length, submissionInstructionsChunk16_length, submissionInstructionsChunk17_length, submissionInstructionsChunk18_length]

private theorem tailPrefix_bytes_length : (Challenge.EvmProof.PcEncoding.assembleBytes tailPrefix).length = 4890 := by
  simp only [tailPrefix, Challenge.EvmProof.PcEncoding.assembleBytes_append, List.length_append, chunk0_byteLength, chunk1_byteLength, chunk2_byteLength, chunk3_byteLength, chunk4_byteLength, chunk5_byteLength, chunk6_byteLength, chunk7_byteLength, chunk8_byteLength, chunk9_byteLength, chunk10_byteLength, chunk11_byteLength, chunk12_byteLength, chunk13_byteLength, chunk14_byteLength, chunk15_byteLength, chunk16_byteLength, chunk17_byteLength, chunk18_byteLength]

private theorem instructionPC_tail (i : Nat) (hi : i ≤ 58) :
    submissionArtifact.instructionPC (3568 + i) =
      4890 + (Challenge.EvmProof.PcEncoding.assembleBytes (submissionInstructionsChunk19.take i)).length := by
  apply ArtifactSegment.instructionPC_segment_of_bounds submissionArtifact
    tailPrefix submissionInstructionsChunk19 [] 3568 4890
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
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc405 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc405 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_406 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc406 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc406 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_407 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc407 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc407 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_408 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc408 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc408 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_409 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc409 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc409 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_410 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc410 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc410 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_412 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc412 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc412 :
    instructionPC 175 = 312 := by
  change submissionArtifact.instructionPC 175 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_417 :
    submissionArtifact.instructionPC 177 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc417 :
    submissionArtifact.instructionPC 177 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc417 :
    instructionPC 177 = 316 := by
  change submissionArtifact.instructionPC 177 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_420 :
    submissionArtifact.instructionPC 171 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc420 :
    submissionArtifact.instructionPC 171 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc420 :
    instructionPC 171 = 247 := by
  change submissionArtifact.instructionPC 171 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_421 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc421 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc421 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_422 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc422 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc422 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_423 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc423 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc423 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_424 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc424 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc424 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_426 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc426 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc426 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_427 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc427 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc427 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_428 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc428 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc428 :
    instructionPC 175 = 312 := by
  change submissionArtifact.instructionPC 175 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_430 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc430 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc430 :
    instructionPC 175 = 312 := by
  change submissionArtifact.instructionPC 175 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_431 :
    submissionArtifact.instructionPC 177 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc431 :
    submissionArtifact.instructionPC 177 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc431 :
    instructionPC 177 = 316 := by
  change submissionArtifact.instructionPC 177 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_439 :
    submissionArtifact.instructionPC 180 = 321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc439 :
    submissionArtifact.instructionPC 180 = 321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc439 :
    instructionPC 180 = 321 := by
  change submissionArtifact.instructionPC 180 = 321
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_440 :
    submissionArtifact.instructionPC 181 = 326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc440 :
    submissionArtifact.instructionPC 181 = 326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc440 :
    instructionPC 181 = 326 := by
  change submissionArtifact.instructionPC 181 = 326
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_441 :
    submissionArtifact.instructionPC 182 = 331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc441 :
    submissionArtifact.instructionPC 182 = 331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc441 :
    instructionPC 182 = 331 := by
  change submissionArtifact.instructionPC 182 = 331
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_442 :
    submissionArtifact.instructionPC 183 = 336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc442 :
    submissionArtifact.instructionPC 183 = 336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc442 :
    instructionPC 183 = 336 := by
  change submissionArtifact.instructionPC 183 = 336
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_443 :
    submissionArtifact.instructionPC 184 = 341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc443 :
    submissionArtifact.instructionPC 184 = 341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc443 :
    instructionPC 184 = 341 := by
  change submissionArtifact.instructionPC 184 = 341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_444 :
    submissionArtifact.instructionPC 185 = 346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc444 :
    submissionArtifact.instructionPC 185 = 346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc444 :
    instructionPC 185 = 346 := by
  change submissionArtifact.instructionPC 185 = 346
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_445 :
    submissionArtifact.instructionPC 186 = 360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc445 :
    submissionArtifact.instructionPC 186 = 360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc445 :
    instructionPC 186 = 360 := by
  change submissionArtifact.instructionPC 186 = 360
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_446 :
    submissionArtifact.instructionPC 187 = 374 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc446 :
    submissionArtifact.instructionPC 187 = 374 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc446 :
    instructionPC 187 = 374 := by
  change submissionArtifact.instructionPC 187 = 374
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_448 :
    submissionArtifact.instructionPC 189 = 430 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc448 :
    submissionArtifact.instructionPC 189 = 430 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc448 :
    instructionPC 189 = 430 := by
  change submissionArtifact.instructionPC 189 = 430
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_449 :
    submissionArtifact.instructionPC 190 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc449 :
    submissionArtifact.instructionPC 190 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc449 :
    instructionPC 190 = 435 := by
  change submissionArtifact.instructionPC 190 = 435
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_450 :
    submissionArtifact.instructionPC 191 = 449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc450 :
    submissionArtifact.instructionPC 191 = 449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc450 :
    instructionPC 191 = 449 := by
  change submissionArtifact.instructionPC 191 = 449
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_451 :
    submissionArtifact.instructionPC 192 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc451 :
    submissionArtifact.instructionPC 192 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc451 :
    instructionPC 192 = 451 := by
  change submissionArtifact.instructionPC 192 = 451
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_452 :
    submissionArtifact.instructionPC 193 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc452 :
    submissionArtifact.instructionPC 193 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc452 :
    instructionPC 193 = 452 := by
  change submissionArtifact.instructionPC 193 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_455 :
    submissionArtifact.instructionPC 72 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc455 :
    submissionArtifact.instructionPC 72 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc455 :
    instructionPC 72 = 114 := by
  change submissionArtifact.instructionPC 72 = 114
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_843 :
    submissionArtifact.instructionPC 171 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc843 :
    submissionArtifact.instructionPC 171 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc843 :
    instructionPC 171 = 247 := by
  change submissionArtifact.instructionPC 171 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_844 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc844 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc844 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_859 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc859 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc859 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_860 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc860 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc860 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_861 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc861 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc861 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_862 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc862 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc862 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_265 :
    submissionArtifact.instructionPC 194 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_265 :
    instructionPC 194 = 453 := by
  change submissionArtifact.instructionPC 194 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_266 :
    submissionArtifact.instructionPC 194 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_266 :
    instructionPC 194 = 453 := by
  change submissionArtifact.instructionPC 194 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_268 :
    submissionArtifact.instructionPC 112 = 170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_268 :
    instructionPC 112 = 170 := by
  change submissionArtifact.instructionPC 112 = 170
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_270 :
    submissionArtifact.instructionPC 114 = 173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_270 :
    instructionPC 114 = 173 := by
  change submissionArtifact.instructionPC 114 = 173
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_271 :
    submissionArtifact.instructionPC 115 = 174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_271 :
    instructionPC 115 = 174 := by
  change submissionArtifact.instructionPC 115 = 174
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_272 :
    submissionArtifact.instructionPC 116 = 175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_272 :
    instructionPC 116 = 175 := by
  change submissionArtifact.instructionPC 116 = 175
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_273 :
    submissionArtifact.instructionPC 117 = 176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_273 :
    instructionPC 117 = 176 := by
  change submissionArtifact.instructionPC 117 = 176
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_274 :
    submissionArtifact.instructionPC 118 = 177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_274 :
    instructionPC 118 = 177 := by
  change submissionArtifact.instructionPC 118 = 177
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_275 :
    submissionArtifact.instructionPC 119 = 179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_275 :
    instructionPC 119 = 179 := by
  change submissionArtifact.instructionPC 119 = 179
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_279 :
    submissionArtifact.instructionPC 73 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_279 :
    instructionPC 73 = 115 := by
  change submissionArtifact.instructionPC 73 = 115
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_280 :
    submissionArtifact.instructionPC 74 = 116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_280 :
    instructionPC 74 = 116 := by
  change submissionArtifact.instructionPC 74 = 116
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_281 :
    submissionArtifact.instructionPC 75 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_281 :
    instructionPC 75 = 117 := by
  change submissionArtifact.instructionPC 75 = 117
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_282 :
    submissionArtifact.instructionPC 76 = 118 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_282 :
    instructionPC 76 = 118 := by
  change submissionArtifact.instructionPC 76 = 118
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_283 :
    submissionArtifact.instructionPC 77 = 119 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_283 :
    instructionPC 77 = 119 := by
  change submissionArtifact.instructionPC 77 = 119
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_284 :
    submissionArtifact.instructionPC 78 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_284 :
    instructionPC 78 = 121 := by
  change submissionArtifact.instructionPC 78 = 121
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_285 :
    submissionArtifact.instructionPC 79 = 122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_285 :
    instructionPC 79 = 122 := by
  change submissionArtifact.instructionPC 79 = 122
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_286 :
    submissionArtifact.instructionPC 80 = 123 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_286 :
    instructionPC 80 = 123 := by
  change submissionArtifact.instructionPC 80 = 123
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_287 :
    submissionArtifact.instructionPC 165 = 238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_287 :
    instructionPC 165 = 238 := by
  change submissionArtifact.instructionPC 165 = 238
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_288 :
    submissionArtifact.instructionPC 166 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_288 :
    instructionPC 166 = 239 := by
  change submissionArtifact.instructionPC 166 = 239
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_289 :
    submissionArtifact.instructionPC 167 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_289 :
    instructionPC 167 = 240 := by
  change submissionArtifact.instructionPC 167 = 240
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_295 :
    submissionArtifact.instructionPC 170 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_295 :
    instructionPC 170 = 246 := by
  change submissionArtifact.instructionPC 170 = 246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem validJumpDest_210 :
    Decode.isValidJumpDest submissionBytecode 115 = true := by
  have hp : submissionArtifact.instructionPC 73 = 115 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 73 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem pcU2_345 :
    submissionArtifact.instructionPC 196 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_345 :
    instructionPC 196 = 456 := by
  change submissionArtifact.instructionPC 196 = 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem validJumpDest_loop :
    Decode.isValidJumpDest submissionBytecode 457 = true := by
  have hp : submissionArtifact.instructionPC 197 = 457 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 197 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest submissionBytecode 247 = true := by
  have hp : submissionArtifact.instructionPC 171 = 247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 171 (by rfl)
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
    submissionArtifact.instructionPC 134 = 200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci26 :
    instructionPC 134 = 200 := by
  change submissionArtifact.instructionPC 134 = 200
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc27 :
    submissionArtifact.instructionPC 135 = 201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci27 :
    instructionPC 135 = 201 := by
  change submissionArtifact.instructionPC 135 = 201
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc28 :
    submissionArtifact.instructionPC 136 = 203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci28 :
    instructionPC 136 = 203 := by
  change submissionArtifact.instructionPC 136 = 203
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc29 :
    submissionArtifact.instructionPC 137 = 204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci29 :
    instructionPC 137 = 204 := by
  change submissionArtifact.instructionPC 137 = 204
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc30 :
    submissionArtifact.instructionPC 138 = 205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci30 :
    instructionPC 138 = 205 := by
  change submissionArtifact.instructionPC 138 = 205
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc31 :
    submissionArtifact.instructionPC 139 = 206 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci31 :
    instructionPC 139 = 206 := by
  change submissionArtifact.instructionPC 139 = 206
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc32 :
    submissionArtifact.instructionPC 140 = 207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci32 :
    instructionPC 140 = 207 := by
  change submissionArtifact.instructionPC 140 = 207
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc33 :
    submissionArtifact.instructionPC 141 = 208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci33 :
    instructionPC 141 = 208 := by
  change submissionArtifact.instructionPC 141 = 208
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc34 :
    submissionArtifact.instructionPC 142 = 209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci34 :
    instructionPC 142 = 209 := by
  change submissionArtifact.instructionPC 142 = 209
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc35 :
    submissionArtifact.instructionPC 143 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci35 :
    instructionPC 143 = 211 := by
  change submissionArtifact.instructionPC 143 = 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc36 :
    submissionArtifact.instructionPC 144 = 212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci36 :
    instructionPC 144 = 212 := by
  change submissionArtifact.instructionPC 144 = 212
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc37 :
    submissionArtifact.instructionPC 145 = 213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci37 :
    instructionPC 145 = 213 := by
  change submissionArtifact.instructionPC 145 = 213
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc38 :
    submissionArtifact.instructionPC 146 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci38 :
    instructionPC 146 = 214 := by
  change submissionArtifact.instructionPC 146 = 214
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc39 :
    submissionArtifact.instructionPC 147 = 215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci39 :
    instructionPC 147 = 215 := by
  change submissionArtifact.instructionPC 147 = 215
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc40 :
    submissionArtifact.instructionPC 148 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci40 :
    instructionPC 148 = 216 := by
  change submissionArtifact.instructionPC 148 = 216
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc41 :
    submissionArtifact.instructionPC 149 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci41 :
    instructionPC 149 = 217 := by
  change submissionArtifact.instructionPC 149 = 217
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc42 :
    submissionArtifact.instructionPC 150 = 219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci42 :
    instructionPC 150 = 219 := by
  change submissionArtifact.instructionPC 150 = 219
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc43 :
    submissionArtifact.instructionPC 151 = 220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci43 :
    instructionPC 151 = 220 := by
  change submissionArtifact.instructionPC 151 = 220
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc44 :
    submissionArtifact.instructionPC 152 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci44 :
    instructionPC 152 = 221 := by
  change submissionArtifact.instructionPC 152 = 221
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc45 :
    submissionArtifact.instructionPC 153 = 222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci45 :
    instructionPC 153 = 222 := by
  change submissionArtifact.instructionPC 153 = 222
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc46 :
    submissionArtifact.instructionPC 154 = 223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci46 :
    instructionPC 154 = 223 := by
  change submissionArtifact.instructionPC 154 = 223
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc47 :
    submissionArtifact.instructionPC 155 = 224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci47 :
    instructionPC 155 = 224 := by
  change submissionArtifact.instructionPC 155 = 224
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc48 :
    submissionArtifact.instructionPC 156 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci48 :
    instructionPC 156 = 225 := by
  change submissionArtifact.instructionPC 156 = 225
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc49 :
    submissionArtifact.instructionPC 157 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci49 :
    instructionPC 157 = 226 := by
  change submissionArtifact.instructionPC 157 = 226
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc50 :
    submissionArtifact.instructionPC 158 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci50 :
    instructionPC 158 = 227 := by
  change submissionArtifact.instructionPC 158 = 227
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc51 :
    submissionArtifact.instructionPC 159 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci51 :
    instructionPC 159 = 229 := by
  change submissionArtifact.instructionPC 159 = 229
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc52 :
    submissionArtifact.instructionPC 160 = 230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci52 :
    instructionPC 160 = 230 := by
  change submissionArtifact.instructionPC 160 = 230
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc53 :
    submissionArtifact.instructionPC 161 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci53 :
    instructionPC 161 = 232 := by
  change submissionArtifact.instructionPC 161 = 232
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc54 :
    submissionArtifact.instructionPC 3501 = 4721 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci54 :
    instructionPC 3501 = 4721 := by
  change submissionArtifact.instructionPC 3501 = 4721
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc55 :
    submissionArtifact.instructionPC 3502 = 4742 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci55 :
    instructionPC 3502 = 4742 := by
  change submissionArtifact.instructionPC 3502 = 4742
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc56 :
    submissionArtifact.instructionPC 3503 = 4743 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci56 :
    instructionPC 3503 = 4743 := by
  change submissionArtifact.instructionPC 3503 = 4743
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc57 :
    submissionArtifact.instructionPC 3504 = 4744 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci57 :
    instructionPC 3504 = 4744 := by
  change submissionArtifact.instructionPC 3504 = 4744
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc58 :
    submissionArtifact.instructionPC 3505 = 4745 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci58 :
    instructionPC 3505 = 4745 := by
  change submissionArtifact.instructionPC 3505 = 4745
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc59 :
    submissionArtifact.instructionPC 3506 = 4746 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci59 :
    instructionPC 3506 = 4746 := by
  change submissionArtifact.instructionPC 3506 = 4746
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc60 :
    submissionArtifact.instructionPC 3507 = 4747 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci60 :
    instructionPC 3507 = 4747 := by
  change submissionArtifact.instructionPC 3507 = 4747
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem cjPc66 :
    submissionArtifact.instructionPC 99 = 151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci66 :
    instructionPC 99 = 151 := by
  change submissionArtifact.instructionPC 99 = 151
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc67 :
    submissionArtifact.instructionPC 100 = 153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci67 :
    instructionPC 100 = 153 := by
  change submissionArtifact.instructionPC 100 = 153
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc68 :
    submissionArtifact.instructionPC 101 = 154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci68 :
    instructionPC 101 = 154 := by
  change submissionArtifact.instructionPC 101 = 154
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc69 :
    submissionArtifact.instructionPC 102 = 155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci69 :
    instructionPC 102 = 155 := by
  change submissionArtifact.instructionPC 102 = 155
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc70 :
    submissionArtifact.instructionPC 103 = 157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci70 :
    instructionPC 103 = 157 := by
  change submissionArtifact.instructionPC 103 = 157
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc71 :
    submissionArtifact.instructionPC 104 = 158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci71 :
    instructionPC 104 = 158 := by
  change submissionArtifact.instructionPC 104 = 158
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc72 :
    submissionArtifact.instructionPC 105 = 159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci72 :
    instructionPC 105 = 159 := by
  change submissionArtifact.instructionPC 105 = 159
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc73 :
    submissionArtifact.instructionPC 106 = 161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci73 :
    instructionPC 106 = 161 := by
  change submissionArtifact.instructionPC 106 = 161
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc74 :
    submissionArtifact.instructionPC 107 = 162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci74 :
    instructionPC 107 = 162 := by
  change submissionArtifact.instructionPC 107 = 162
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc75 :
    submissionArtifact.instructionPC 108 = 165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci75 :
    instructionPC 108 = 165 := by
  change submissionArtifact.instructionPC 108 = 165
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc84 :
    submissionArtifact.instructionPC 45 = 72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci84 :
    instructionPC 45 = 72 := by
  change submissionArtifact.instructionPC 45 = 72
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc85 :
    submissionArtifact.instructionPC 46 = 73 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci85 :
    instructionPC 46 = 73 := by
  change submissionArtifact.instructionPC 46 = 73
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc86 :
    submissionArtifact.instructionPC 47 = 75 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci86 :
    instructionPC 47 = 75 := by
  change submissionArtifact.instructionPC 47 = 75
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc87 :
    submissionArtifact.instructionPC 48 = 76 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci87 :
    instructionPC 48 = 76 := by
  change submissionArtifact.instructionPC 48 = 76
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc89 :
    submissionArtifact.instructionPC 50 = 79 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci89 :
    instructionPC 50 = 79 := by
  change submissionArtifact.instructionPC 50 = 79
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc90 :
    submissionArtifact.instructionPC 51 = 80 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci90 :
    instructionPC 51 = 80 := by
  change submissionArtifact.instructionPC 51 = 80
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc91 :
    submissionArtifact.instructionPC 52 = 81 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci91 :
    instructionPC 52 = 81 := by
  change submissionArtifact.instructionPC 52 = 81
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc92 :
    submissionArtifact.instructionPC 53 = 84 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci92 :
    instructionPC 53 = 84 := by
  change submissionArtifact.instructionPC 53 = 84
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc93 :
    submissionArtifact.instructionPC 54 = 85 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci93 :
    instructionPC 54 = 85 := by
  change submissionArtifact.instructionPC 54 = 85
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc94 :
    submissionArtifact.instructionPC 55 = 87 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci94 :
    instructionPC 55 = 87 := by
  change submissionArtifact.instructionPC 55 = 87
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc95 :
    submissionArtifact.instructionPC 56 = 88 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci95 :
    instructionPC 56 = 88 := by
  change submissionArtifact.instructionPC 56 = 88
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc104 :
    submissionArtifact.instructionPC 163 = 236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci104 :
    instructionPC 163 = 236 := by
  change submissionArtifact.instructionPC 163 = 236
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc105 :
    submissionArtifact.instructionPC 164 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci105 :
    instructionPC 164 = 237 := by
  change submissionArtifact.instructionPC 164 = 237
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc109 :
    submissionArtifact.instructionPC 120 = 180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci109 :
    instructionPC 120 = 180 := by
  change submissionArtifact.instructionPC 120 = 180
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc110 :
    submissionArtifact.instructionPC 121 = 181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci110 :
    instructionPC 121 = 181 := by
  change submissionArtifact.instructionPC 121 = 181
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc111 :
    submissionArtifact.instructionPC 122 = 184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci111 :
    instructionPC 122 = 184 := by
  change submissionArtifact.instructionPC 122 = 184
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc112 :
    submissionArtifact.instructionPC 123 = 185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci112 :
    instructionPC 123 = 185 := by
  change submissionArtifact.instructionPC 123 = 185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc113 :
    submissionArtifact.instructionPC 124 = 187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci113 :
    instructionPC 124 = 187 := by
  change submissionArtifact.instructionPC 124 = 187
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc116 :
    submissionArtifact.instructionPC 112 = 170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci116 :
    instructionPC 112 = 170 := by
  change submissionArtifact.instructionPC 112 = 170
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc117 :
    submissionArtifact.instructionPC 113 = 172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci117 :
    instructionPC 113 = 172 := by
  change submissionArtifact.instructionPC 113 = 172
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc118 :
    submissionArtifact.instructionPC 114 = 173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci118 :
    instructionPC 114 = 173 := by
  change submissionArtifact.instructionPC 114 = 173
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc119 :
    submissionArtifact.instructionPC 115 = 174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci119 :
    instructionPC 115 = 174 := by
  change submissionArtifact.instructionPC 115 = 174
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc120 :
    submissionArtifact.instructionPC 116 = 175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci120 :
    instructionPC 116 = 175 := by
  change submissionArtifact.instructionPC 116 = 175
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc121 :
    submissionArtifact.instructionPC 117 = 176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci121 :
    instructionPC 117 = 176 := by
  change submissionArtifact.instructionPC 117 = 176
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc122 :
    submissionArtifact.instructionPC 118 = 177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci122 :
    instructionPC 118 = 177 := by
  change submissionArtifact.instructionPC 118 = 177
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc123 :
    submissionArtifact.instructionPC 119 = 179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci123 :
    instructionPC 119 = 179 := by
  change submissionArtifact.instructionPC 119 = 179
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc126 :
    submissionArtifact.instructionPC 72 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci126 :
    instructionPC 72 = 114 := by
  change submissionArtifact.instructionPC 72 = 114
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc127 :
    submissionArtifact.instructionPC 73 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci127 :
    instructionPC 73 = 115 := by
  change submissionArtifact.instructionPC 73 = 115
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc128 :
    submissionArtifact.instructionPC 74 = 116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci128 :
    instructionPC 74 = 116 := by
  change submissionArtifact.instructionPC 74 = 116
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc129 :
    submissionArtifact.instructionPC 75 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci129 :
    instructionPC 75 = 117 := by
  change submissionArtifact.instructionPC 75 = 117
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc130 :
    submissionArtifact.instructionPC 76 = 118 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci130 :
    instructionPC 76 = 118 := by
  change submissionArtifact.instructionPC 76 = 118
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc131 :
    submissionArtifact.instructionPC 77 = 119 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci131 :
    instructionPC 77 = 119 := by
  change submissionArtifact.instructionPC 77 = 119
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc132 :
    submissionArtifact.instructionPC 78 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci132 :
    instructionPC 78 = 121 := by
  change submissionArtifact.instructionPC 78 = 121
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc133 :
    submissionArtifact.instructionPC 79 = 122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci133 :
    instructionPC 79 = 122 := by
  change submissionArtifact.instructionPC 79 = 122
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc134 :
    submissionArtifact.instructionPC 80 = 123 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci134 :
    instructionPC 80 = 123 := by
  change submissionArtifact.instructionPC 80 = 123
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc135 :
    submissionArtifact.instructionPC 165 = 238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci135 :
    instructionPC 165 = 238 := by
  change submissionArtifact.instructionPC 165 = 238
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc136 :
    submissionArtifact.instructionPC 166 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci136 :
    instructionPC 166 = 239 := by
  change submissionArtifact.instructionPC 166 = 239
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc137 :
    submissionArtifact.instructionPC 167 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci137 :
    instructionPC 167 = 240 := by
  change submissionArtifact.instructionPC 167 = 240
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc146 :
    submissionArtifact.instructionPC 170 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci146 :
    instructionPC 170 = 246 := by
  change submissionArtifact.instructionPC 170 = 246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc147 :
    submissionArtifact.instructionPC 171 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci147 :
    instructionPC 171 = 247 := by
  change submissionArtifact.instructionPC 171 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc148 :
    submissionArtifact.instructionPC 172 = 248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci148 :
    instructionPC 172 = 248 := by
  change submissionArtifact.instructionPC 172 = 248
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc149 :
    submissionArtifact.instructionPC 173 = 279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci149 :
    instructionPC 173 = 279 := by
  change submissionArtifact.instructionPC 173 = 279
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc152 :
    submissionArtifact.instructionPC 174 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci152 :
    instructionPC 174 = 311 := by
  change submissionArtifact.instructionPC 174 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc153 :
    submissionArtifact.instructionPC 175 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci153 :
    instructionPC 175 = 312 := by
  change submissionArtifact.instructionPC 175 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc155 :
    submissionArtifact.instructionPC 177 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci155 :
    instructionPC 177 = 316 := by
  change submissionArtifact.instructionPC 177 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc156 :
    submissionArtifact.instructionPC 180 = 321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci156 :
    instructionPC 180 = 321 := by
  change submissionArtifact.instructionPC 180 = 321
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc157 :
    submissionArtifact.instructionPC 181 = 326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci157 :
    instructionPC 181 = 326 := by
  change submissionArtifact.instructionPC 181 = 326
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc158 :
    submissionArtifact.instructionPC 182 = 331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci158 :
    instructionPC 182 = 331 := by
  change submissionArtifact.instructionPC 182 = 331
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc159 :
    submissionArtifact.instructionPC 183 = 336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci159 :
    instructionPC 183 = 336 := by
  change submissionArtifact.instructionPC 183 = 336
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc160 :
    submissionArtifact.instructionPC 184 = 341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci160 :
    instructionPC 184 = 341 := by
  change submissionArtifact.instructionPC 184 = 341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc161 :
    submissionArtifact.instructionPC 185 = 346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci161 :
    instructionPC 185 = 346 := by
  change submissionArtifact.instructionPC 185 = 346
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc162 :
    submissionArtifact.instructionPC 186 = 360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci162 :
    instructionPC 186 = 360 := by
  change submissionArtifact.instructionPC 186 = 360
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc163 :
    submissionArtifact.instructionPC 187 = 374 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci163 :
    instructionPC 187 = 374 := by
  change submissionArtifact.instructionPC 187 = 374
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc164 :
    submissionArtifact.instructionPC 188 = 402 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci164 :
    instructionPC 188 = 402 := by
  change submissionArtifact.instructionPC 188 = 402
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc165 :
    submissionArtifact.instructionPC 189 = 430 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci165 :
    instructionPC 189 = 430 := by
  change submissionArtifact.instructionPC 189 = 430
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc166 :
    submissionArtifact.instructionPC 190 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci166 :
    instructionPC 190 = 435 := by
  change submissionArtifact.instructionPC 190 = 435
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc167 :
    submissionArtifact.instructionPC 191 = 449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci167 :
    instructionPC 191 = 449 := by
  change submissionArtifact.instructionPC 191 = 449
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc168 :
    submissionArtifact.instructionPC 192 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci168 :
    instructionPC 192 = 451 := by
  change submissionArtifact.instructionPC 192 = 451
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc169 :
    submissionArtifact.instructionPC 193 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci169 :
    instructionPC 193 = 452 := by
  change submissionArtifact.instructionPC 193 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc170 :
    submissionArtifact.instructionPC 194 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci170 :
    instructionPC 194 = 453 := by
  change submissionArtifact.instructionPC 194 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc172 :
    submissionArtifact.instructionPC 196 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci172 :
    instructionPC 196 = 456 := by
  change submissionArtifact.instructionPC 196 = 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

/-! Cached instruction PCs of the CONT prologue and footer tail. -/

@[simp] theorem cgPc9 :
    submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci9 :
    instructionPC 9 = 17 := by
  change submissionArtifact.instructionPC 9 = 17
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc17 :
    submissionArtifact.instructionPC 17 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci17 :
    instructionPC 17 = 29 := by
  change submissionArtifact.instructionPC 17 = 29
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc26 :
    submissionArtifact.instructionPC 26 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci26 :
    instructionPC 26 = 44 := by
  change submissionArtifact.instructionPC 26 = 44
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc27 :
    submissionArtifact.instructionPC 27 = 46 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci27 :
    instructionPC 27 = 46 := by
  change submissionArtifact.instructionPC 27 = 46
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc28 :
    submissionArtifact.instructionPC 28 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci28 :
    instructionPC 28 = 47 := by
  change submissionArtifact.instructionPC 28 = 47
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc29 :
    submissionArtifact.instructionPC 29 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci29 :
    instructionPC 29 = 48 := by
  change submissionArtifact.instructionPC 29 = 48
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc30 :
    submissionArtifact.instructionPC 30 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci30 :
    instructionPC 30 = 50 := by
  change submissionArtifact.instructionPC 30 = 50
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc31 :
    submissionArtifact.instructionPC 31 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci31 :
    instructionPC 31 = 51 := by
  change submissionArtifact.instructionPC 31 = 51
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc32 :
    submissionArtifact.instructionPC 32 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci32 :
    instructionPC 32 = 52 := by
  change submissionArtifact.instructionPC 32 = 52
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc33 :
    submissionArtifact.instructionPC 33 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci33 :
    instructionPC 33 = 53 := by
  change submissionArtifact.instructionPC 33 = 53
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc34 :
    submissionArtifact.instructionPC 34 = 54 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci34 :
    instructionPC 34 = 54 := by
  change submissionArtifact.instructionPC 34 = 54
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc35 :
    submissionArtifact.instructionPC 35 = 57 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci35 :
    instructionPC 35 = 57 := by
  change submissionArtifact.instructionPC 35 = 57
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc36 :
    submissionArtifact.instructionPC 36 = 58 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci36 :
    instructionPC 36 = 58 := by
  change submissionArtifact.instructionPC 36 = 58
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc37 :
    submissionArtifact.instructionPC 37 = 60 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci37 :
    instructionPC 37 = 60 := by
  change submissionArtifact.instructionPC 37 = 60
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc38 :
    submissionArtifact.instructionPC 38 = 61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci38 :
    instructionPC 38 = 61 := by
  change submissionArtifact.instructionPC 38 = 61
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc39 :
    submissionArtifact.instructionPC 39 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci39 :
    instructionPC 39 = 63 := by
  change submissionArtifact.instructionPC 39 = 63
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc40 :
    submissionArtifact.instructionPC 39 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci40 :
    instructionPC 39 = 63 := by
  change submissionArtifact.instructionPC 39 = 63
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc41 :
    submissionArtifact.instructionPC 40 = 64 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci41 :
    instructionPC 40 = 64 := by
  change submissionArtifact.instructionPC 40 = 64
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc42 :
    submissionArtifact.instructionPC 41 = 65 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci42 :
    instructionPC 41 = 65 := by
  change submissionArtifact.instructionPC 41 = 65
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc43 :
    submissionArtifact.instructionPC 42 = 68 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci43 :
    instructionPC 42 = 68 := by
  change submissionArtifact.instructionPC 42 = 68
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc44 :
    submissionArtifact.instructionPC 43 = 69 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci44 :
    instructionPC 43 = 69 := by
  change submissionArtifact.instructionPC 43 = 69
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc45 :
    submissionArtifact.instructionPC 44 = 71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci45 :
    instructionPC 44 = 71 := by
  change submissionArtifact.instructionPC 44 = 71
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc50 :
    submissionArtifact.instructionPC 49 = 77 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci50 :
    instructionPC 49 = 77 := by
  change submissionArtifact.instructionPC 49 = 77
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc58 :
    submissionArtifact.instructionPC 57 = 90 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci58 :
    instructionPC 57 = 90 := by
  change submissionArtifact.instructionPC 57 = 90
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc59 :
    submissionArtifact.instructionPC 58 = 91 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci59 :
    instructionPC 58 = 91 := by
  change submissionArtifact.instructionPC 58 = 91
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc60 :
    submissionArtifact.instructionPC 59 = 92 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci60 :
    instructionPC 59 = 92 := by
  change submissionArtifact.instructionPC 59 = 92
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc61 :
    submissionArtifact.instructionPC 60 = 95 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci61 :
    instructionPC 60 = 95 := by
  change submissionArtifact.instructionPC 60 = 95
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc62 :
    submissionArtifact.instructionPC 61 = 96 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci62 :
    instructionPC 61 = 96 := by
  change submissionArtifact.instructionPC 61 = 96
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc63 :
    submissionArtifact.instructionPC 62 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci63 :
    instructionPC 62 = 98 := by
  change submissionArtifact.instructionPC 62 = 98
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc64 :
    submissionArtifact.instructionPC 63 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci64 :
    instructionPC 63 = 99 := by
  change submissionArtifact.instructionPC 63 = 99
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc65 :
    submissionArtifact.instructionPC 64 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci65 :
    instructionPC 64 = 101 := by
  change submissionArtifact.instructionPC 64 = 101
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc66 :
    submissionArtifact.instructionPC 65 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci66 :
    instructionPC 65 = 102 := by
  change submissionArtifact.instructionPC 65 = 102
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc67 :
    submissionArtifact.instructionPC 66 = 105 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci67 :
    instructionPC 66 = 105 := by
  change submissionArtifact.instructionPC 66 = 105
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc68 :
    submissionArtifact.instructionPC 67 = 106 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci68 :
    instructionPC 67 = 106 := by
  change submissionArtifact.instructionPC 67 = 106
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc69 :
    submissionArtifact.instructionPC 68 = 107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci69 :
    instructionPC 68 = 107 := by
  change submissionArtifact.instructionPC 68 = 107
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc70 :
    submissionArtifact.instructionPC 69 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci70 :
    instructionPC 69 = 110 := by
  change submissionArtifact.instructionPC 69 = 110
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc71 :
    submissionArtifact.instructionPC 70 = 111 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci71 :
    instructionPC 70 = 111 := by
  change submissionArtifact.instructionPC 70 = 111
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc72 :
    submissionArtifact.instructionPC 71 = 112 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci72 :
    instructionPC 71 = 112 := by
  change submissionArtifact.instructionPC 71 = 112
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc82 :
    submissionArtifact.instructionPC 81 = 125 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci82 :
    instructionPC 81 = 125 := by
  change submissionArtifact.instructionPC 81 = 125
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc83 :
    submissionArtifact.instructionPC 82 = 127 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci83 :
    instructionPC 82 = 127 := by
  change submissionArtifact.instructionPC 82 = 127
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc84 :
    submissionArtifact.instructionPC 83 = 128 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci84 :
    instructionPC 83 = 128 := by
  change submissionArtifact.instructionPC 83 = 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc85 :
    submissionArtifact.instructionPC 84 = 129 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci85 :
    instructionPC 84 = 129 := by
  change submissionArtifact.instructionPC 84 = 129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc86 :
    submissionArtifact.instructionPC 85 = 131 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci86 :
    instructionPC 85 = 131 := by
  change submissionArtifact.instructionPC 85 = 131
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc87 :
    submissionArtifact.instructionPC 86 = 132 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci87 :
    instructionPC 86 = 132 := by
  change submissionArtifact.instructionPC 86 = 132
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc88 :
    submissionArtifact.instructionPC 87 = 133 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci88 :
    instructionPC 87 = 133 := by
  change submissionArtifact.instructionPC 87 = 133
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc89 :
    submissionArtifact.instructionPC 88 = 134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci89 :
    instructionPC 88 = 134 := by
  change submissionArtifact.instructionPC 88 = 134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc90 :
    submissionArtifact.instructionPC 89 = 135 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci90 :
    instructionPC 89 = 135 := by
  change submissionArtifact.instructionPC 89 = 135
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc91 :
    submissionArtifact.instructionPC 90 = 137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci91 :
    instructionPC 90 = 137 := by
  change submissionArtifact.instructionPC 90 = 137
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc92 :
    submissionArtifact.instructionPC 91 = 138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci92 :
    instructionPC 91 = 138 := by
  change submissionArtifact.instructionPC 91 = 138
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc93 :
    submissionArtifact.instructionPC 92 = 139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci93 :
    instructionPC 92 = 139 := by
  change submissionArtifact.instructionPC 92 = 139
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc94 :
    submissionArtifact.instructionPC 93 = 142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci94 :
    instructionPC 93 = 142 := by
  change submissionArtifact.instructionPC 93 = 142
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc95 :
    submissionArtifact.instructionPC 94 = 143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci95 :
    instructionPC 94 = 143 := by
  change submissionArtifact.instructionPC 94 = 143
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc96 :
    submissionArtifact.instructionPC 95 = 144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci96 :
    instructionPC 95 = 144 := by
  change submissionArtifact.instructionPC 95 = 144
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc97 :
    submissionArtifact.instructionPC 96 = 147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci97 :
    instructionPC 96 = 147 := by
  change submissionArtifact.instructionPC 96 = 147
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc98 :
    submissionArtifact.instructionPC 97 = 148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci98 :
    instructionPC 97 = 148 := by
  change submissionArtifact.instructionPC 97 = 148
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc99 :
    submissionArtifact.instructionPC 98 = 149 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci99 :
    instructionPC 98 = 149 := by
  change submissionArtifact.instructionPC 98 = 149
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc110 :
    submissionArtifact.instructionPC 109 = 166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci110 :
    instructionPC 109 = 166 := by
  change submissionArtifact.instructionPC 109 = 166
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc111 :
    submissionArtifact.instructionPC 110 = 167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci111 :
    instructionPC 110 = 167 := by
  change submissionArtifact.instructionPC 110 = 167
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc112 :
    submissionArtifact.instructionPC 111 = 169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci112 :
    instructionPC 111 = 169 := by
  change submissionArtifact.instructionPC 111 = 169
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc126 :
    submissionArtifact.instructionPC 125 = 188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci126 :
    instructionPC 125 = 188 := by
  change submissionArtifact.instructionPC 125 = 188
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc127 :
    submissionArtifact.instructionPC 126 = 190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci127 :
    instructionPC 126 = 190 := by
  change submissionArtifact.instructionPC 126 = 190
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc128 :
    submissionArtifact.instructionPC 127 = 191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci128 :
    instructionPC 127 = 191 := by
  change submissionArtifact.instructionPC 127 = 191
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc129 :
    submissionArtifact.instructionPC 128 = 192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci129 :
    instructionPC 128 = 192 := by
  change submissionArtifact.instructionPC 128 = 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc130 :
    submissionArtifact.instructionPC 129 = 193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci130 :
    instructionPC 129 = 193 := by
  change submissionArtifact.instructionPC 129 = 193
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc131 :
    submissionArtifact.instructionPC 130 = 195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci131 :
    instructionPC 130 = 195 := by
  change submissionArtifact.instructionPC 130 = 195
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc132 :
    submissionArtifact.instructionPC 131 = 196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci132 :
    instructionPC 131 = 196 := by
  change submissionArtifact.instructionPC 131 = 196
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc133 :
    submissionArtifact.instructionPC 133 = 199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci133 :
    instructionPC 133 = 199 := by
  change submissionArtifact.instructionPC 133 = 199
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc134 :
    submissionArtifact.instructionPC 133 = 199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci134 :
    instructionPC 133 = 199 := by
  change submissionArtifact.instructionPC 133 = 199
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc163 :
    submissionArtifact.instructionPC 162 = 233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci163 :
    instructionPC 162 = 233 := by
  change submissionArtifact.instructionPC 162 = 233
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc169 :
    submissionArtifact.instructionPC 168 = 241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci169 :
    instructionPC 168 = 241 := by
  change submissionArtifact.instructionPC 168 = 241
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc170 :
    submissionArtifact.instructionPC 169 = 243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci170 :
    instructionPC 169 = 243 := by
  change submissionArtifact.instructionPC 169 = 243
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc177 :
    submissionArtifact.instructionPC 176 = 313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci177 :
    instructionPC 176 = 313 := by
  change submissionArtifact.instructionPC 176 = 313
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc179 :
    submissionArtifact.instructionPC 178 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci179 :
    instructionPC 178 = 317 := by
  change submissionArtifact.instructionPC 178 = 317
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc180 :
    submissionArtifact.instructionPC 179 = 318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci180 :
    instructionPC 179 = 318 := by
  change submissionArtifact.instructionPC 179 = 318
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc196 :
    submissionArtifact.instructionPC 195 = 454 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci196 :
    instructionPC 195 = 454 := by
  change submissionArtifact.instructionPC 195 = 454
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc198 :
    submissionArtifact.instructionPC 197 = 457 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci198 :
    instructionPC 197 = 457 := by
  change submissionArtifact.instructionPC 197 = 457
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc199 :
    submissionArtifact.instructionPC 198 = 458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci199 :
    instructionPC 198 = 458 := by
  change submissionArtifact.instructionPC 198 = 458
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3455 :
    submissionArtifact.instructionPC 3453 = 4593 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3455 :
    instructionPC 3453 = 4593 := by
  change submissionArtifact.instructionPC 3453 = 4593
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3456 :
    submissionArtifact.instructionPC 3454 = 4596 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3456 :
    instructionPC 3454 = 4596 := by
  change submissionArtifact.instructionPC 3454 = 4596
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3457 :
    submissionArtifact.instructionPC 3455 = 4597 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3457 :
    instructionPC 3455 = 4597 := by
  change submissionArtifact.instructionPC 3455 = 4597
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3458 :
    submissionArtifact.instructionPC 3456 = 4600 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3458 :
    instructionPC 3456 = 4600 := by
  change submissionArtifact.instructionPC 3456 = 4600
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3459 :
    submissionArtifact.instructionPC 3457 = 4601 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3459 :
    instructionPC 3457 = 4601 := by
  change submissionArtifact.instructionPC 3457 = 4601
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3460 :
    submissionArtifact.instructionPC 3458 = 4602 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3460 :
    instructionPC 3458 = 4602 := by
  change submissionArtifact.instructionPC 3458 = 4602
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3461 :
    submissionArtifact.instructionPC 3459 = 4603 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3461 :
    instructionPC 3459 = 4603 := by
  change submissionArtifact.instructionPC 3459 = 4603
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3462 :
    submissionArtifact.instructionPC 3460 = 4605 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3462 :
    instructionPC 3460 = 4605 := by
  change submissionArtifact.instructionPC 3460 = 4605
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3463 :
    submissionArtifact.instructionPC 3461 = 4623 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3463 :
    instructionPC 3461 = 4623 := by
  change submissionArtifact.instructionPC 3461 = 4623
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3464 :
    submissionArtifact.instructionPC 3462 = 4624 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3464 :
    instructionPC 3462 = 4624 := by
  change submissionArtifact.instructionPC 3462 = 4624
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3465 :
    submissionArtifact.instructionPC 3463 = 4625 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3465 :
    instructionPC 3463 = 4625 := by
  change submissionArtifact.instructionPC 3463 = 4625
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3466 :
    submissionArtifact.instructionPC 3464 = 4626 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3466 :
    instructionPC 3464 = 4626 := by
  change submissionArtifact.instructionPC 3464 = 4626
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3467 :
    submissionArtifact.instructionPC 3465 = 4629 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3467 :
    instructionPC 3465 = 4629 := by
  change submissionArtifact.instructionPC 3465 = 4629
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3468 :
    submissionArtifact.instructionPC 3466 = 4630 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3468 :
    instructionPC 3466 = 4630 := by
  change submissionArtifact.instructionPC 3466 = 4630
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3469 :
    submissionArtifact.instructionPC 3467 = 4633 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3469 :
    instructionPC 3467 = 4633 := by
  change submissionArtifact.instructionPC 3467 = 4633
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3470 :
    submissionArtifact.instructionPC 3468 = 4634 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3470 :
    instructionPC 3468 = 4634 := by
  change submissionArtifact.instructionPC 3468 = 4634
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3471 :
    submissionArtifact.instructionPC 3469 = 4637 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3471 :
    instructionPC 3469 = 4637 := by
  change submissionArtifact.instructionPC 3469 = 4637
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3472 :
    submissionArtifact.instructionPC 3470 = 4638 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3472 :
    instructionPC 3470 = 4638 := by
  change submissionArtifact.instructionPC 3470 = 4638
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3473 :
    submissionArtifact.instructionPC 3471 = 4639 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3473 :
    instructionPC 3471 = 4639 := by
  change submissionArtifact.instructionPC 3471 = 4639
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3474 :
    submissionArtifact.instructionPC 3472 = 4640 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3474 :
    instructionPC 3472 = 4640 := by
  change submissionArtifact.instructionPC 3472 = 4640
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3475 :
    submissionArtifact.instructionPC 3473 = 4643 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3475 :
    instructionPC 3473 = 4643 := by
  change submissionArtifact.instructionPC 3473 = 4643
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3476 :
    submissionArtifact.instructionPC 3474 = 4644 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3476 :
    instructionPC 3474 = 4644 := by
  change submissionArtifact.instructionPC 3474 = 4644
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3477 :
    submissionArtifact.instructionPC 3475 = 4645 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3477 :
    instructionPC 3475 = 4645 := by
  change submissionArtifact.instructionPC 3475 = 4645
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3478 :
    submissionArtifact.instructionPC 3476 = 4646 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3478 :
    instructionPC 3476 = 4646 := by
  change submissionArtifact.instructionPC 3476 = 4646
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3479 :
    submissionArtifact.instructionPC 3477 = 4648 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3479 :
    instructionPC 3477 = 4648 := by
  change submissionArtifact.instructionPC 3477 = 4648
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3480 :
    submissionArtifact.instructionPC 3478 = 4649 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3480 :
    instructionPC 3478 = 4649 := by
  change submissionArtifact.instructionPC 3478 = 4649
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3481 :
    submissionArtifact.instructionPC 3479 = 4650 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3481 :
    instructionPC 3479 = 4650 := by
  change submissionArtifact.instructionPC 3479 = 4650
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3482 :
    submissionArtifact.instructionPC 3480 = 4654 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3482 :
    instructionPC 3480 = 4654 := by
  change submissionArtifact.instructionPC 3480 = 4654
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3483 :
    submissionArtifact.instructionPC 3481 = 4655 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3483 :
    instructionPC 3481 = 4655 := by
  change submissionArtifact.instructionPC 3481 = 4655
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3484 :
    submissionArtifact.instructionPC 3482 = 4656 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3484 :
    instructionPC 3482 = 4656 := by
  change submissionArtifact.instructionPC 3482 = 4656
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3485 :
    submissionArtifact.instructionPC 3483 = 4658 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3485 :
    instructionPC 3483 = 4658 := by
  change submissionArtifact.instructionPC 3483 = 4658
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3486 :
    submissionArtifact.instructionPC 3484 = 4659 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3486 :
    instructionPC 3484 = 4659 := by
  change submissionArtifact.instructionPC 3484 = 4659
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3487 :
    submissionArtifact.instructionPC 3485 = 4680 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3487 :
    instructionPC 3485 = 4680 := by
  change submissionArtifact.instructionPC 3485 = 4680
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3488 :
    submissionArtifact.instructionPC 3486 = 4681 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3488 :
    instructionPC 3486 = 4681 := by
  change submissionArtifact.instructionPC 3486 = 4681
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3489 :
    submissionArtifact.instructionPC 3487 = 4682 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3489 :
    instructionPC 3487 = 4682 := by
  change submissionArtifact.instructionPC 3487 = 4682
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3490 :
    submissionArtifact.instructionPC 3488 = 4703 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3490 :
    instructionPC 3488 = 4703 := by
  change submissionArtifact.instructionPC 3488 = 4703
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3491 :
    submissionArtifact.instructionPC 3489 = 4704 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3491 :
    instructionPC 3489 = 4704 := by
  change submissionArtifact.instructionPC 3489 = 4704
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3492 :
    submissionArtifact.instructionPC 3490 = 4707 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3492 :
    instructionPC 3490 = 4707 := by
  change submissionArtifact.instructionPC 3490 = 4707
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3493 :
    submissionArtifact.instructionPC 3491 = 4708 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3493 :
    instructionPC 3491 = 4708 := by
  change submissionArtifact.instructionPC 3491 = 4708
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3494 :
    submissionArtifact.instructionPC 3492 = 4709 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3494 :
    instructionPC 3492 = 4709 := by
  change submissionArtifact.instructionPC 3492 = 4709
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3495 :
    submissionArtifact.instructionPC 3493 = 4710 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3495 :
    instructionPC 3493 = 4710 := by
  change submissionArtifact.instructionPC 3493 = 4710
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3496 :
    submissionArtifact.instructionPC 3494 = 4711 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3496 :
    instructionPC 3494 = 4711 := by
  change submissionArtifact.instructionPC 3494 = 4711
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3497 :
    submissionArtifact.instructionPC 3495 = 4712 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3497 :
    instructionPC 3495 = 4712 := by
  change submissionArtifact.instructionPC 3495 = 4712
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3498 :
    submissionArtifact.instructionPC 3496 = 4714 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3498 :
    instructionPC 3496 = 4714 := by
  change submissionArtifact.instructionPC 3496 = 4714
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3499 :
    submissionArtifact.instructionPC 3497 = 4715 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3499 :
    instructionPC 3497 = 4715 := by
  change submissionArtifact.instructionPC 3497 = 4715
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3500 :
    submissionArtifact.instructionPC 3498 = 4716 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3500 :
    instructionPC 3498 = 4716 := by
  change submissionArtifact.instructionPC 3498 = 4716
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3501 :
    submissionArtifact.instructionPC 3499 = 4719 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3501 :
    instructionPC 3499 = 4719 := by
  change submissionArtifact.instructionPC 3499 = 4719
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3502 :
    submissionArtifact.instructionPC 3500 = 4720 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3502 :
    instructionPC 3500 = 4720 := by
  change submissionArtifact.instructionPC 3500 = 4720
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3510 :
    submissionArtifact.instructionPC 3508 = 4748 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3510 :
    instructionPC 3508 = 4748 := by
  change submissionArtifact.instructionPC 3508 = 4748
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3511 :
    submissionArtifact.instructionPC 3509 = 4749 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3511 :
    instructionPC 3509 = 4749 := by
  change submissionArtifact.instructionPC 3509 = 4749
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

/-- The padding code is entered by fall-through; no return address is pushed. -/
def padEnterPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨172, .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255), by rfl, by decide⟩,
   ⟨173, .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), by rfl, by decide⟩]

/-- Cached located path for the calldata copy and the zero offset; CALLDATASIZE stays in slot 12 as the fast-entry continuation. -/
def padCopyPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨174, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨175, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨176, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨177, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨178, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩]

/-- Cached located path for the fast-entry test: only the lengths 64, 128 and 192 (the
calldata size has no bit outside `0xc0`) go straight to the block loop. -/
def padGuardPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨191, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨192, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨193, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨194, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨195, .push ⟨1, by decide⟩ (UInt256.ofNat 143), by rfl, by decide⟩,
   ⟨196, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the sentinel byte. -/
def padSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨112, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨113, .op (.Dup ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨114, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨115, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨116, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the footer-loop setup: bit length, rounded length offset plus 89, then the jump to the loop head 115. -/
def padFooterSetupA : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨117, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨119, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨120, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨121, .push ⟨2, by decide⟩ (UInt256.ofNat 968), by rfl, by decide⟩,
   ⟨122, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨123, .push ⟨1, by decide⟩ (UInt256.ofNat 63), by rfl, by decide⟩,
   ⟨124, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, .push ⟨1, by decide⟩ (UInt256.ofNat 111), by rfl, by decide⟩,
   ⟨126, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]
def padFooterSetupB : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨70, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨71, .push ⟨1, by decide⟩ (UInt256.ofNat 89), by rfl, by decide⟩,
   ⟨72, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩]
def padFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  padFooterSetupA ++ padFooterSetupB

/-- Cached located path for the footer-loop exit: the generic continuation 47 replaces the output entry. -/
def padExitPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨3493, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3494, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3495, .push ⟨1, by decide⟩ (UInt256.ofNat 47), by rfl, by decide⟩,
   ⟨3496, .op (.Swap ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3497, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3498, .push ⟨2, by decide⟩ (UInt256.ofNat 457), by rfl, by decide⟩,
   ⟨3499, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]


@[simp] theorem validJumpDest_111 :
    Decode.isValidJumpDest submissionBytecode 111 = true := by
  have hp : submissionArtifact.instructionPC 70 = 111 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 70 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_237 :
    Decode.isValidJumpDest submissionBytecode 237 = true := by
  have hp : submissionArtifact.instructionPC 164 = 237 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 164 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4708 :
    Decode.isValidJumpDest submissionBytecode 4708 = true := by
  have hp : submissionArtifact.instructionPC 3491 = 4708 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3491 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_47 :
    Decode.isValidJumpDest submissionBytecode 47 = true := by
  have hp : submissionArtifact.instructionPC 28 = 47 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 28 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_64 :
    Decode.isValidJumpDest submissionBytecode 64 = true := by
  have hp : submissionArtifact.instructionPC 40 = 64 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 40 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_128 :
    Decode.isValidJumpDest submissionBytecode 128 = true := by
  have hp : submissionArtifact.instructionPC 83 = 128 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 83 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_132 :
    Decode.isValidJumpDest submissionBytecode 132 = true := by
  have hp : submissionArtifact.instructionPC 86 = 132 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 86 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_143 :
    Decode.isValidJumpDest submissionBytecode 143 = true := by
  have hp : submissionArtifact.instructionPC 94 = 143 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 94 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_192 :
    Decode.isValidJumpDest submissionBytecode 192 = true := by
  have hp : submissionArtifact.instructionPC 128 = 192 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 128 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_494 :
    Decode.isValidJumpDest submissionBytecode 494 = true := by
  have hp : submissionArtifact.instructionPC 224 = 494 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 224 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_824 :
    Decode.isValidJumpDest submissionBytecode 824 = true := by
  have hp : submissionArtifact.instructionPC 418 = 824 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 418 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4748 :
    Decode.isValidJumpDest submissionBytecode 4748 = true := by
  have hp : submissionArtifact.instructionPC 3508 = 4748 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3508 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4553 :
    Decode.isValidJumpDest submissionBytecode 4553 = true := by
  have hp : submissionArtifact.instructionPC 3417 = 4553 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3417 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4601 :
    Decode.isValidJumpDest submissionBytecode 4601 = true := by
  have hp : submissionArtifact.instructionPC 3457 = 4601 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3457 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4742 :
    Decode.isValidJumpDest submissionBytecode 4742 = true := by
  have hp : submissionArtifact.instructionPC 3502 = 4742 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3502 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4805 :
    Decode.isValidJumpDest submissionBytecode 4805 = true := by
  have hp : submissionArtifact.instructionPC 3552 = 4805 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3552 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4808 :
    Decode.isValidJumpDest submissionBytecode 4808 = true := by
  have hp : submissionArtifact.instructionPC 3554 = 4808 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3554 (by rfl)
  rw [hp] at h
  exact h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
