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

The exact candidate has 5247 bytes, 3617 executable instructions and 280 data bytes, and SHA-256
`34b57b79b00486b64a85666336c9e0e48c9822c2fc925bda08ccb3222c17c9c5`. PUSH rows carry their typed width and value.
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
  .push 6 24260332913180,
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
  .push 2 4793,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 2 960,
  .push 2 968,
  op 0x35,
  op 0x82,
  op 0x18,
  .push 1 212,
  op 0x56,
  op 0x5b,
  .push 1 128,
  op 0x8c,
  op 0x01,
  op 0x59,
  op 0x10,
  .push 2 4736,
  op 0x57,
  .push 1 48,
  .push 1 195,
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
  .push 2 522,
  op 0x52,
  .push 19 2854495385411919762116571938898990272765493376,
  .push 1 54,
  op 0x52,
  .push 2 4736,
  op 0x9c,
  op 0x50,
  .push 2 824,
  op 0x56,
  op 0x04,
  op 0x04,
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
  .push 2 4736,
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
  .push 1 128,
  op 0x8c,
  op 0x36,
  op 0x01,
  op 0x53,
  .push 2 4949,
  op 0x36,
  .push 1 3,
  op 0x1b,
  op 0x36,
  .push 2 968,
  op 0x01,
  .push 1 63,
  op 0x17,
  .push 1 89,
  op 0x01,
  op 0x82,
  op 0x56,
  op 0x5b,
  .push 1 128,
  op 0x5b,
  op 0x9c,
  .push 1 132,
  op 0x56,
  op 0x5b,
  .push 1 48,
  op 0x9f,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  .push 2 457,
  op 0x56,
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
  .push 1 212,
  op 0x57,
  op 0x15,
  .push 2 4709,
  op 0x57,
  op 0x5b
]

@[simp] private theorem submissionInstructionsChunk0_length : submissionInstructionsChunk0.length = 157 := by rfl

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
  op 0x88,
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
  op 0x18,
  op 0x89,
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
  .push 2 324,
  op 0x51,
  op 0x01,
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
  op 0x8c,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x18,
  op 0x8c,
  op 0x18,
  .push 2 864,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
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
  op 0x88,
  op 0x82,
  op 0x16,
  op 0x18,
  op 0x88,
  op 0x86,
  op 0x16,
  op 0x17,
  op 0x18,
  op 0x84,
  op 0x18,
  .push 2 1062,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
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
  op 0x86,
  op 0x85,
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
  op 0x8d,
  .push 13 2376844875981332450021900025857,
  op 0x86,
  op 0x83,
  op 0x94,
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
  op 0x85,
  op 0x89,
  op 0x16,
  op 0x8b,
  op 0x8a,
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x17,
  op 0x18,
  op 0x18,
  .push 2 990,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
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
  op 0x17,
  op 0x88,
  op 0x87,
  op 0x18,
  op 0x16,
  op 0x87,
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
  op 0x8a,
  op 0x01,
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
  op 0x86,
  op 0x82,
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
  op 0x8f,
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
  .push 1 162,
  op 0x51,
  op 0x01,
  op 0x87,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
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
  .push 2 828,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
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
  .push 2 612,
  op 0x51,
  op 0x8a,
  op 0x01,
  op 0x01,
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
  .push 2 936,
  op 0x51,
  op 0x01,
  op 0x88,
  op 0x01,
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
  .push 2 468,
  op 0x51,
  op 0x89,
  op 0x01,
  op 0x01,
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
  op 0x85,
  op 0x01,
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
  .push 1 234,
  op 0x51,
  op 0x89,
  op 0x01,
  op 0x01,
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
  .push 1 54,
  op 0x51,
  op 0x87,
  op 0x01,
  op 0x01,
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
  .push 2 414,
  op 0x51,
  op 0x87,
  op 0x01,
  op 0x01,
  op 0x01,
  op 0x8e,
  op 0x8d,
  .push 13 158456325065422163338801971201,
  op 0x8f,
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
  .push 1 198,
  op 0x51,
  op 0x01,
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
  op 0x83,
  op 0x16,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x8e,
  op 0x18,
  .push 2 576,
  op 0x51,
  op 0x01,
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
  op 0x89,
  op 0x8f,
  op 0x18,
  op 0x16,
  op 0x18,
  op 0x18,
  .push 2 702,
  op 0x51,
  op 0x87,
  op 0x01,
  op 0x01,
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
  .push 1 90,
  op 0x51,
  op 0x01,
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
  .push 2 792,
  op 0x51,
  op 0x83,
  op 0x01,
  op 0x01,
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
  op 0x86,
  op 0x85,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x87,
  op 0x86,
  op 0x17,
  op 0x8b,
  op 0x18,
  op 0x16,
  op 0x87,
  op 0x18,
  .push 2 900,
  op 0x51,
  op 0x01,
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
  .push 2 594,
  op 0x51,
  op 0x85,
  op 0x01,
  op 0x01,
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
  .push 2 630,
  op 0x51,
  op 0x85,
  op 0x01,
  op 0x01,
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
  op 0x89,
  op 0x8d,
  op 0x18,
  op 0x17,
  op 0x84,
  op 0x16,
  op 0x89,
  op 0x18,
  op 0x87,
  op 0x8d,
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
  op 0x87,
  op 0x8b,
  op 0x18,
  op 0x86,
  op 0x17,
  op 0x16,
  op 0x87,
  op 0x86,
  op 0x16,
  op 0x18,
  op 0x8a,
  op 0x18,
  .push 2 1026,
  op 0x51,
  op 0x01,
  op 0x89,
  op 0x01,
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
  op 0x89,
  op 0x85,
  op 0x16,
  op 0x82,
  op 0x88,
  op 0x8c,
  op 0x18,
  op 0x87,
  op 0x17,
  op 0x16,
  op 0x18,
  op 0x87,
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
  op 0x8d,
  op 0x81,
  op 0x96,
  op 0x8d,
  op 0x8c,
  op 0x16,
  op 0x83,
  op 0x17,
  op 0x89,
  op 0x18,
  op 0x8c,
  op 0x18,
  op 0x8e,
  op 0x18,
  .push 2 396,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x85,
  op 0x16,
  op 0x8c,
  op 0x02,
  .push 1 24,
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
  op 0x18,
  op 0x89,
  op 0x8f,
  op 0x16,
  op 0x85,
  op 0x17,
  op 0x8d,
  op 0x18,
  op 0x18,
  .push 2 522,
  op 0x51,
  op 0x01,
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
  op 0x8c,
  op 0x8f,
  op 0x82,
  op 0x97,
  op 0x8c,
  op 0x8f,
  op 0x16,
  op 0x89,
  op 0x17,
  op 0x8f,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x8a,
  op 0x18,
  .push 2 720,
  op 0x51,
  op 0x8d,
  op 0x01,
  op 0x01,
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
  op 0x89,
  op 0x8f,
  op 0x16,
  op 0x85,
  op 0x17,
  op 0x8d,
  op 0x18,
  op 0x8f,
  op 0x18,
  op 0x8a,
  op 0x18,
  .push 2 756,
  op 0x51,
  op 0x01,
  op 0x8c,
  op 0x01,
  op 0x01,
  op 0x86,
  op 0x16,
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
  op 0x83,
  op 0x16,
  op 0x94,
  op 0x89,
  op 0x8c,
  op 0x16,
  op 0x86,
  op 0x17,
  op 0x87,
  op 0x18,
  op 0x8a,
  op 0x18,
  op 0x8c,
  op 0x18,
  .push 1 252,
  op 0x51,
  op 0x8a,
  op 0x01,
  op 0x01,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 27,
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
  op 0x86,
  op 0x8c,
  op 0x16,
  op 0x82,
  op 0x17,
  op 0x8c,
  op 0x18,
  op 0x87,
  op 0x18,
  op 0x8a,
  op 0x18,
  .push 2 432,
  op 0x51,
  op 0x8a,
  op 0x01,
  op 0x01,
  op 0x01,
  op 0x83,
  op 0x16,
  op 0x8a,
  op 0x02,
  .push 1 25
]

@[simp] private theorem submissionInstructionsChunk15_length : submissionInstructionsChunk15.length = 223 := by rfl

private def submissionInstructionsChunk16 : List Instr :=
[
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
  op 0x8b,
  op 0x87,
  op 0x18,
  op 0x8a,
  op 0x8d,
  op 0x16,
  op 0x87,
  op 0x17,
  op 0x18,
  op 0x8a,
  op 0x18,
  op 0x83,
  op 0x8a,
  op 0x01,
  op 0x01,
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
  op 0x8d,
  op 0x81,
  op 0x92,
  op 0x88,
  op 0x8e,
  op 0x16,
  op 0x84,
  op 0x17,
  op 0x89,
  op 0x18,
  op 0x8c,
  op 0x18,
  op 0x8e,
  op 0x18,
  .push 1 216,
  op 0x51,
  op 0x8c,
  op 0x01,
  op 0x01,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 14 9982748479121596290348819152960,
  op 0x09,
  .push 1 26,
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
  op 0x18,
  op 0x8b,
  op 0x8e,
  op 0x16,
  op 0x88,
  op 0x17,
  op 0x89,
  op 0x18,
  op 0x18,
  .push 1 162,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x8b,
  op 0x02,
  .push 1 28,
  op 0x1c,
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
  op 0x8c,
  op 0x8f,
  op 0x82,
  op 0x93,
  op 0x8c,
  op 0x8f,
  op 0x18,
  op 0x8f,
  op 0x8b,
  op 0x16,
  op 0x86,
  op 0x17,
  op 0x18,
  op 0x8a,
  op 0x18,
  .push 2 540,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x86,
  op 0x16,
  op 0x09,
  .push 1 20,
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
  op 0x8a,
  op 0x8d,
  op 0x16,
  op 0x87,
  op 0x17,
  op 0x88,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x8b,
  op 0x18,
  .push 2 972,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x8b,
  op 0x02,
  .push 1 20,
  op 0x1c,
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
  op 0x8d,
  op 0x81,
  op 0x92,
  op 0x88,
  op 0x8e,
  op 0x16,
  op 0x84,
  op 0x17,
  op 0x8e,
  op 0x8d,
  op 0x18,
  op 0x8a,
  op 0x18,
  op 0x18,
  .push 2 918,
  op 0x51,
  op 0x01,
  op 0x8b,
  op 0x01,
  op 0x01,
  op 0x85,
  op 0x16,
  .push 14 1109194275457955143375908765704,
  op 0x09,
  .push 1 21,
  op 0x1c,
  op 0x86,
  op 0x01,
  op 0x84,
  op 0x16
]

@[simp] private theorem submissionInstructionsChunk16_length : submissionInstructionsChunk16.length = 218 := by rfl

private def submissionInstructionsChunk17 : List Instr :=
[
  op 0x96,
  op 0x8b,
  op 0x02,
  op 0x88,
  op 0x1c,
  op 0x95,
  op 0x8a,
  op 0x8d,
  op 0x16,
  op 0x87,
  op 0x17,
  op 0x88,
  op 0x18,
  op 0x8d,
  op 0x18,
  op 0x8b,
  op 0x18,
  .push 2 594,
  op 0x51,
  op 0x01,
  op 0x8a,
  op 0x01,
  op 0x01,
  op 0x84,
  op 0x16,
  op 0x8b,
  op 0x02,
  .push 1 22,
  op 0x1c,
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
  .push 2 4879,
  op 0x57,
  .push 2 4905,
  op 0x56,
  op 0x5b,
  op 0x36,
  .push 1 1,
  .push 17 342276208914615837337402008677671501826,
  op 0x36,
  op 0x1c,
  op 0x16,
  .push 2 4796,
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
  .push 2 4793,
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
  .push 0 0,
  op 0x52,
  op 0x59,
  .push 0 0,
  op 0xf3,
  op 0x5b,
  .push 20 972889429405991776604892044862621566948497025487,
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
  .push 2 4905,
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
  op 0x87
]

@[simp] private theorem submissionInstructionsChunk18_length : submissionInstructionsChunk18.length = 106 := by rfl

private def submissionInstructionsChunk19 : List Instr :=
[
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
  .push 2 4879,
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
  op 0xf3,
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
  op 0x83,
  op 0x57,
  .push 1 200,
  op 0x56
]

@[simp] private theorem submissionInstructionsChunk19_length : submissionInstructionsChunk19.length = 62 := by rfl

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

theorem referenceInstructions_count : submissionInstructions.length = 3617 := by
  simp only [submissionInstructions, List.length_append, submissionInstructionsChunk0_length, submissionInstructionsChunk1_length, submissionInstructionsChunk2_length, submissionInstructionsChunk3_length, submissionInstructionsChunk4_length, submissionInstructionsChunk5_length, submissionInstructionsChunk6_length, submissionInstructionsChunk7_length, submissionInstructionsChunk8_length, submissionInstructionsChunk9_length, submissionInstructionsChunk10_length, submissionInstructionsChunk11_length, submissionInstructionsChunk12_length, submissionInstructionsChunk13_length, submissionInstructionsChunk14_length, submissionInstructionsChunk15_length, submissionInstructionsChunk16_length, submissionInstructionsChunk17_length, submissionInstructionsChunk18_length, submissionInstructionsChunk19_length]

private theorem submissionInstructionsChunk0_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk0 = [
  101, 22, 16, 140, 134, 130, 28, 95, 53, 22, 96, 247, 87, 54, 97, 3, 232, 3, 97, 17, 249, 87, 95, 53, 96, 255, 2, 96, 97, 1, 97, 18, 185, 87, 95, 53, 97, 3, 192, 97, 3, 200, 53, 130, 24, 96, 212, 86,
  91, 96, 128, 140, 1, 89, 16, 97, 18, 128, 87, 96, 48, 96, 195, 86, 91, 97, 4, 60, 54, 96, 28, 55, 54, 96, 3, 27, 128, 96, 162, 82, 128, 97, 2, 154, 82, 96, 144, 82, 96, 128, 97, 2, 10, 82, 114, 128,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 96, 54, 82, 97, 18, 128, 156, 80, 97, 3, 56, 86, 4, 4, 91, 96, 64, 156, 91, 80, 154, 96, 64, 1, 154, 97, 1, 201, 86, 91,
  97, 18, 128, 156, 80, 96, 128, 96, 165, 83, 132, 96, 188, 83, 54, 96, 32, 20, 97, 1, 238, 87, 96, 128, 140, 54, 1, 83, 97, 19, 85, 54, 96, 3, 27, 54, 97, 3, 200, 1, 96, 63, 23, 96, 89, 1, 130, 86,
  91, 96, 128, 91, 156, 96, 132, 86, 91, 96, 48, 159, 80, 80, 80, 80, 97, 1, 201, 86, 91, 96, 32, 130, 3, 53, 131, 24, 23, 96, 64, 130, 3, 53, 131, 24, 23, 96, 96, 130, 3, 145, 53, 131, 24, 23, 129, 96,
  212, 87, 21, 97, 18, 101, 87, 91,

] := by decide

private theorem submissionInstructionsChunk1_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk1 = [
  125, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 0, 0, 255, 255, 126, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0,
  255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 54, 95, 97, 4, 32, 55, 54, 97, 4, 32, 99, 103, 69, 35, 1, 99, 239, 205, 171, 137, 99, 152, 186, 220, 254, 99, 16, 50, 84, 118, 99, 195, 210,
  225, 240, 108, 6, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 1, 108, 14, 0, 0, 0, 14, 0, 0, 0, 1, 0, 0, 0, 1, 122, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 122, 1, 255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 255, 255, 255, 255, 108, 2, 0, 0, 0,
  2, 0, 0, 0, 2, 0, 0, 0, 2, 96, 192, 25, 54, 22, 96, 143, 87, 91, 139, 97, 0, 32, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1, 0,
  1, 2, 24, 96, 162, 82, 91, 139, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1,

] := by decide

private theorem submissionInstructionsChunk2_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk2 = [
  2, 24, 143, 129, 128, 97, 0, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24, 96, 252, 82, 97, 0, 146, 81, 96, 128, 82, 96, 178, 81, 96, 196, 82, 96, 236, 81, 96, 218, 82, 97, 1, 12, 81, 97, 1, 30, 82, 96,
  176, 81, 96, 168, 81, 97, 1, 10, 81, 97, 1, 14, 81, 96, 142, 81, 96, 172, 81, 96, 232, 81, 97, 1, 2, 81, 96, 228, 81, 96, 180, 81, 97, 1, 6, 81, 96, 146, 81, 96, 134, 81, 96, 236, 81, 96, 224, 81,
  96, 138, 81, 128, 97, 3, 132, 82, 134, 97, 3, 240, 82, 130, 97, 3, 114, 82, 132, 96, 126, 82, 132, 97, 3, 96, 82, 130, 97, 3, 78, 82, 128, 97, 3, 60, 82, 131, 97, 3, 168, 82, 131, 97, 2, 46, 82, 135,
  97, 2, 28, 82, 133, 96, 108, 82, 141, 97, 2, 172, 82, 143, 88, 82, 141, 97, 1, 158, 82, 97, 2, 244, 82, 128, 97, 2, 10, 82, 141, 96, 90, 82, 135, 96, 72, 82, 96, 54, 82, 133, 97, 1, 248, 82, 131, 97,
  4, 56, 82, 131, 97, 1, 230, 82, 136, 97, 4, 38, 82, 97, 3, 204, 82, 136, 97, 0, 216, 82, 131, 97, 2, 136, 82, 136, 97, 2, 118, 82, 131, 98, 0, 2, 100, 82, 88, 82, 136, 97, 1, 32, 82, 117, 255, 255,
  255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255,

] := by decide

private theorem submissionInstructionsChunk3_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk3 = [
  22, 97, 2, 82, 82, 136, 97, 4, 20, 82, 97, 2, 208, 82, 97, 1, 14, 82, 129, 97, 1, 140, 82, 128, 88, 82, 97, 1, 212, 82, 96, 18, 82, 97, 1, 104, 82, 96, 198, 82, 97, 1, 68, 82, 96, 252, 82, 95,
  82, 97, 1, 194, 82, 96, 162, 82, 91, 136, 129, 2, 96, 23, 28, 136, 136, 141, 99, 80, 162, 139, 230, 1, 97, 1, 230, 81, 1, 141, 141, 141, 25, 23, 24, 1, 133, 22, 132, 2, 96, 25, 28, 1, 132, 22, 132, 132,
  134, 143, 134, 25, 23, 132, 24, 96, 162, 81, 142, 1, 1, 99, 80, 162, 139, 230, 1, 22, 2, 96, 24, 28, 131, 1, 22, 99, 80, 162, 139, 230, 142, 134, 2, 96, 23, 28, 147, 131, 133, 25, 23, 131, 24, 1, 96, 252,
  81, 1, 1, 134, 22, 133, 2, 96, 24, 28, 132, 1, 134, 22, 96, 144, 27, 142, 23, 144, 96, 144, 27, 141, 23, 147, 96, 144, 27, 143, 23, 145, 133, 2, 96, 23, 28, 96, 144, 27, 140, 23, 146, 96, 144, 27, 139, 23,
  117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 97, 1,
  104, 81, 96, 23, 140, 138,

] := by decide

private theorem submissionInstructionsChunk4_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk4 = [
  117, 80, 162, 139, 230, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 152, 134, 140, 136, 22, 140, 23, 141, 24, 24, 137, 24, 1, 96, 54, 81, 1, 137, 1, 133, 22, 140, 2, 96, 22,
  28, 135, 1, 133, 22, 154, 140, 2, 131, 28, 133, 22, 150, 135, 137, 136, 22, 23, 135, 24, 137, 141, 24, 24, 1, 97, 3, 6, 81, 1, 137, 1, 133, 22, 9, 96, 19, 28, 136, 1, 131, 22, 149, 138, 2, 129, 28, 131,
  22, 140, 143, 130, 154, 137, 141, 133, 138, 130, 22, 23, 138, 24, 24, 24, 1, 133, 1, 138, 1, 134, 22, 141, 2, 96, 18, 28, 136, 1, 134, 22, 155, 141, 2, 132, 28, 134, 22, 151, 137, 136, 138, 129, 131, 22, 23, 24,
  24, 141, 24, 1, 97, 3, 114, 81, 1, 138, 1, 134, 22, 9, 96, 20, 28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 141, 139, 130, 154, 137, 141, 137, 22, 141, 23, 137, 24, 24, 141, 24, 1, 97, 1, 140, 81, 1,
  138, 1, 134, 22, 141, 2, 96, 28, 28, 136, 1, 134, 22, 155, 141, 2, 132, 28, 134, 22, 151, 137, 136, 138, 129, 131, 22, 23, 24, 24, 141, 24, 1, 97, 4, 56, 81, 1, 138, 1, 134, 22, 9, 96, 25, 28, 1, 131,
  22, 149, 138, 2, 129, 28, 131, 22, 141, 139, 130, 154, 140, 136, 22, 140, 23, 141, 137, 140,

] := by decide

private theorem submissionInstructionsChunk5_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk5 = [
  24, 24, 24, 1, 97, 4, 20, 81, 1, 138, 1, 134, 22, 129, 2, 96, 26, 28, 136, 1, 134, 22, 155, 129, 2, 132, 28, 134, 22, 151, 140, 138, 138, 129, 139, 22, 23, 138, 24, 24, 24, 1, 97, 1, 32, 81, 1, 138,
  1, 134, 22, 9, 96, 24, 28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 140, 129, 153, 139, 139, 129, 137, 22, 23, 138, 137, 24, 24, 24, 1, 97, 3, 168, 81, 1, 137, 1, 133, 22, 140, 2, 96, 22, 28, 135, 1,
  133, 22, 154, 140, 2, 131, 28, 133, 22, 150, 135, 135, 138, 22, 23, 140, 24, 135, 24, 137, 24, 1, 97, 3, 42, 81, 1, 137, 1, 133, 22, 108, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 19,
  28, 1, 131, 22, 149, 138, 2, 129, 28, 131, 22, 141, 129, 153, 136, 140, 136, 24, 24, 131, 141, 137, 22, 23, 24, 97, 1, 68, 81, 1, 1, 137, 1, 133, 22, 140, 2, 96, 19, 28, 135, 1, 133, 22, 154, 140, 2, 131,
  28, 133, 22, 150, 136, 135, 137, 129, 140, 22, 23, 24, 24, 140, 24, 97, 3, 96, 81, 1, 138, 1, 1, 133, 22, 108, 14, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 20, 28, 1, 131, 22, 149, 138,
  2, 129, 28, 131, 22, 151, 137, 133, 22, 137, 23, 138, 136, 24, 24, 133, 24, 1
] := by decide

private theorem submissionInstructionsChunk6_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk6 = [
  97, 1, 194, 81, 1, 144, 150, 1, 130, 22, 137, 2, 96, 27, 28, 132, 1, 130, 22, 151, 137, 2, 134, 28, 130, 22, 139, 143, 117, 92, 77, 209, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 150, 139, 137, 136, 130, 22, 24, 136, 134, 22, 23, 24, 132, 24, 97, 4, 38, 81, 1, 136, 1, 1, 133, 22, 9, 96, 25, 28, 136, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 151, 134, 133, 22, 138, 24,
  133, 138, 22, 23, 135, 138, 24, 24, 1, 96, 144, 81, 1, 133, 1, 140, 141, 108, 30, 0, 0, 0, 30, 0, 0, 0, 1, 0, 0, 0, 1, 134, 131, 148, 22, 9, 137, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133,
  22, 146, 131, 140, 133, 137, 22, 139, 138, 131, 22, 24, 23, 24, 24, 97, 3, 222, 81, 1, 136, 1, 1, 133, 22, 108, 254, 0, 0, 0, 254, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 24, 28, 137, 1, 132, 22, 150,
  139, 2, 136, 28, 132, 22, 149, 99, 90, 130, 121, 153, 1, 152, 134, 139, 23, 136, 135, 24, 22, 135, 24, 139, 137, 22, 23, 1, 96, 252, 81, 1, 137, 1, 132, 22, 139, 2, 96, 26, 28, 130, 1, 132, 22, 153, 139, 2,
  136, 28, 132, 22, 145, 130, 139, 135, 24, 137, 130, 23, 22, 24, 139, 137, 22, 23, 1
] := by decide

private theorem submissionInstructionsChunk7_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk7 = [
  96, 72, 81, 138, 1, 1, 132, 22, 108, 126, 0, 0, 0, 126, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 26, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 140, 129, 23, 138, 137, 24, 22,
  24, 140, 138, 22, 23, 1, 96, 198, 81, 1, 138, 1, 133, 22, 140, 2, 96, 25, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 137, 133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 1, 248,
  81, 1, 138, 1, 133, 22, 108, 30, 0, 0, 0, 30, 0, 0, 0, 16, 0, 0, 0, 16, 9, 136, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22,
  23, 1, 97, 1, 68, 81, 1, 138, 1, 133, 22, 140, 2, 96, 22, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131, 137, 133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 2, 172, 81, 1, 138,
  1, 133, 22, 108, 6, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 9, 96, 25, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1,
  97, 3, 240, 81, 1, 138, 1, 133, 22, 140, 2, 96, 26, 28, 131, 1, 133, 22, 154, 140
] := by decide

private theorem submissionInstructionsChunk8_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk8 = [
  2, 137, 28, 133, 22, 146, 131, 137, 133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 3, 186, 81, 1, 138, 1, 133, 22, 108, 14, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 20, 28, 1,
  131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23, 1, 97, 1, 194, 81, 1, 138, 1, 133, 22, 140, 2, 96, 26, 28, 131, 1, 133, 22, 154, 140, 2, 137,
  28, 133, 22, 146, 131, 137, 133, 23, 141, 137, 24, 22, 24, 140, 138, 22, 23, 1, 96, 36, 81, 1, 138, 1, 133, 22, 108, 126, 0, 0, 0, 126, 0, 0, 0, 64, 0, 0, 0, 64, 9, 96, 26, 28, 1, 131, 22, 149,
  138, 2, 135, 28, 131, 22, 148, 134, 138, 22, 138, 135, 23, 136, 135, 24, 22, 135, 24, 23, 1, 97, 3, 60, 81, 1, 136, 1, 131, 22, 138, 2, 96, 18, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 144, 134,
  130, 23, 138, 134, 24, 22, 130, 24, 138, 136, 22, 23, 1, 97, 1, 230, 81, 1, 136, 1, 143, 141, 108, 30, 0, 0, 0, 30, 0, 0, 0, 1, 0, 0, 0, 1, 143, 147, 135, 22, 9, 137, 28, 135, 1, 133, 22, 151,
  140, 2, 137, 28, 133, 22, 150, 135, 140, 137, 23, 138, 137, 24, 22, 24, 140, 138, 22, 23,

] := by decide

private theorem submissionInstructionsChunk9_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk9 = [
  1, 132, 1, 117, 109, 112, 62, 243, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 130, 121, 153, 154, 1, 133, 22, 140, 2, 96, 22, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 131,
  135, 138, 142, 131, 22, 24, 142, 130, 24, 22, 24, 24, 1, 97, 2, 154, 81, 1, 138, 1, 133, 22, 9, 96, 25, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 133, 133, 24, 138, 136, 136, 22, 24, 136, 135,
  24, 22, 24, 1, 96, 126, 81, 1, 136, 1, 108, 126, 0, 0, 0, 126, 0, 0, 0, 64, 0, 0, 0, 64, 142, 145, 133, 22, 9, 96, 25, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 151, 134, 138, 138, 22,
  24, 138, 134, 24, 22, 137, 134, 24, 24, 1, 97, 2, 46, 81, 1, 1, 141, 140, 145, 132, 22, 9, 96, 20, 28, 132, 1, 130, 22, 148, 137, 2, 134, 28, 130, 22, 140, 138, 129, 118, 1, 109, 112, 62, 242, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 110, 217, 235, 161, 151, 132, 141, 25, 139, 23, 24, 1, 97, 3, 204, 81, 1, 136, 1, 134, 22, 141, 2, 96, 22, 28, 139, 1, 134, 22, 155, 141, 2, 138, 28, 134, 22,
  154, 139, 141, 139, 25, 23, 24, 1, 97, 1, 50, 81, 137, 1, 1, 134, 22,

] := by decide

private theorem submissionInstructionsChunk10_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk10 = [
  108, 62, 0, 0, 0, 62, 0, 0, 0, 32, 0, 0, 0, 32, 9, 96, 24, 28, 131, 1, 133, 22, 151, 140, 2, 137, 28, 133, 22, 146, 131, 140, 25, 138, 23, 24, 1, 96, 162, 81, 1, 135, 1, 133, 22, 140, 2, 96,
  27, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 140, 138, 25, 23, 24, 1, 96, 18, 81, 1, 135, 1, 133, 22, 9, 96, 26, 28, 129, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 143, 130, 147,
  131, 141, 25, 139, 23, 24, 97, 3, 60, 81, 1, 137, 1, 1, 134, 22, 141, 2, 96, 19, 28, 139, 1, 134, 22, 155, 141, 2, 138, 28, 134, 22, 154, 140, 138, 25, 23, 140, 24, 97, 2, 100, 81, 138, 1, 1, 1, 134,
  22, 9, 136, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 146, 131, 140, 25, 138, 23, 24, 97, 3, 168, 81, 1, 136, 1, 1, 133, 22, 140, 2, 96, 20, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133,
  22, 153, 138, 140, 138, 25, 23, 24, 97, 1, 212, 81, 137, 1, 1, 1, 133, 22, 109, 7, 254, 0, 0, 7, 254, 0, 0, 4, 0, 0, 0, 4, 0, 9, 96, 27, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140,
  129, 146, 131, 140, 25, 138, 23, 24, 133, 1, 1, 135, 1, 133, 22, 140, 2, 96, 19, 28,

] := by decide

private theorem submissionInstructionsChunk11_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk11 = [
  138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 140, 138, 25, 23, 24, 96, 234, 81, 137, 1, 1, 1, 133, 22, 108, 62, 0, 0, 0, 62, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 24, 28, 1, 131, 22,
  149, 138, 2, 135, 28, 131, 22, 144, 129, 138, 25, 136, 23, 24, 96, 54, 81, 135, 1, 1, 1, 131, 22, 138, 2, 96, 20, 28, 136, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 151, 136, 138, 136, 25, 23, 24, 97, 1,
  158, 81, 135, 1, 1, 1, 142, 141, 108, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 143, 147, 135, 22, 9, 96, 26, 28, 131, 1, 133, 22, 151, 140, 2, 137, 28, 133, 22, 146, 131, 140, 25, 138, 23, 24,
  96, 198, 81, 1, 1, 117, 122, 109, 118, 233, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 217, 235, 161, 151, 1, 133, 22, 140, 2, 96, 28, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22,
  153, 138, 140, 143, 24, 138, 142, 131, 22, 24, 22, 24, 142, 24, 97, 2, 64, 81, 1, 1, 135, 1, 133, 22, 9, 96, 20, 28, 129, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 144, 129, 140, 129, 137, 22, 140, 24, 137,
  143, 24, 22, 24, 24, 97, 2, 190, 81, 135, 1, 1, 1, 142, 142
] := by decide

private theorem submissionInstructionsChunk12_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk12 = [
  108, 6, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 143, 147, 135, 22, 9, 96, 27, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 140, 143, 24, 138, 142, 142, 22, 24, 22, 143, 24, 24, 96,
  90, 81, 1, 1, 135, 1, 133, 22, 9, 96, 27, 28, 129, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 99, 32, 65, 209, 59, 1, 144, 134, 138, 134, 23, 24, 138, 134, 22, 135, 24, 22, 138, 24, 97, 3, 24, 81,
  131, 1, 1, 1, 131, 22, 138, 2, 96, 22, 28, 136, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 151, 134, 133, 22, 137, 24, 135, 134, 23, 139, 24, 22, 135, 24, 97, 3, 132, 81, 1, 1, 129, 1, 131, 22, 143, 141,
  145, 9, 96, 20, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 135, 135, 141, 22, 24, 135, 141, 23, 138, 24, 22, 140, 24, 97, 2, 82, 81, 133, 1, 1, 1, 133, 22, 140, 2, 96, 19, 28, 138,
  1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 135, 138, 22, 24, 140, 138, 137, 23, 24, 22, 137, 24, 97, 2, 118, 81, 133, 1, 1, 1, 133, 22, 109, 3, 254, 0, 0, 3, 254, 0, 0, 2, 0, 0, 0, 2,
  0, 9, 96, 26, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 136, 140
] := by decide

private theorem submissionInstructionsChunk13_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk13 = [
  136, 23, 24, 140, 136, 22, 137, 24, 22, 140, 24, 1, 96, 54, 81, 1, 131, 1, 133, 22, 140, 2, 96, 19, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 136, 140, 129, 137, 23, 24, 140, 137, 131, 22, 24,
  22, 24, 1, 97, 2, 226, 81, 1, 131, 1, 133, 22, 109, 3, 254, 0, 0, 3, 254, 0, 0, 2, 0, 0, 0, 2, 0, 9, 96, 26, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 129, 150, 139, 135, 129, 23,
  138, 24, 137, 137, 131, 22, 24, 22, 24, 1, 97, 1, 194, 81, 1, 131, 1, 133, 22, 140, 2, 96, 24, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 138, 135, 138, 22, 24, 140, 138, 137, 23, 24, 22, 137,
  24, 1, 97, 1, 122, 81, 1, 131, 1, 133, 22, 108, 30, 0, 0, 0, 30, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 24, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 136, 140, 136, 23, 24, 140,
  136, 22, 137, 24, 22, 140, 24, 1, 96, 198, 81, 1, 131, 1, 133, 22, 140, 2, 96, 24, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 136, 140, 129, 137, 23, 24, 140, 137, 131, 22, 24, 22, 24, 1, 97,
  3, 78, 81, 1, 131, 1, 133, 22,

] := by decide

private theorem submissionInstructionsChunk14_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk14 = [
  108, 6, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 9, 96, 20, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 129, 150, 139, 135, 129, 23, 138, 24, 137, 137, 131, 22, 24, 22, 24, 1, 96, 252, 81,
  1, 131, 1, 133, 22, 140, 2, 96, 28, 28, 138, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 153, 136, 140, 138, 137, 23, 24, 140, 137, 131, 22, 24, 22, 24, 1, 97, 2, 136, 81, 1, 131, 1, 133, 22, 109, 3, 254,
  0, 0, 3, 254, 0, 0, 0, 1, 0, 0, 0, 1, 9, 96, 26, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 134, 138, 134, 23, 24, 138, 134, 22, 135, 24, 22, 138, 24, 1, 96, 162, 81, 1, 1, 130, 22,
  137, 2, 96, 25, 28, 135, 1, 130, 22, 151, 137, 2, 134, 28, 130, 22, 139, 143, 99, 143, 27, 188, 220, 153, 134, 137, 141, 24, 23, 132, 22, 137, 24, 135, 141, 22, 24, 1, 96, 108, 81, 1, 138, 1, 133, 22, 9, 96,
  26, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 133, 135, 139, 24, 134, 23, 22, 135, 134, 22, 24, 138, 24, 97, 4, 2, 81, 1, 137, 1, 1, 131, 22, 138, 2, 96, 28, 28, 129, 1, 131, 22, 152, 138,
  2, 135, 28, 131, 22, 144, 137, 133, 22, 130, 136, 140, 24, 135, 23, 22, 24, 135, 24, 1
] := by decide

private theorem submissionInstructionsChunk15_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk15 = [
  97, 1, 86, 81, 1, 99, 169, 83, 253, 78, 152, 1, 131, 22, 138, 2, 96, 21, 28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 141, 129, 150, 141, 140, 22, 131, 23, 137, 24, 140, 24, 142, 24, 97, 1, 140, 81,
  1, 1, 138, 1, 133, 22, 140, 2, 96, 24, 28, 131, 1, 133, 22, 154, 140, 2, 137, 28, 133, 22, 146, 141, 137, 24, 137, 143, 22, 133, 23, 141, 24, 24, 97, 2, 10, 81, 1, 1, 138, 1, 133, 22, 108, 14, 0, 0,
  0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 20, 28, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 140, 143, 130, 151, 140, 143, 22, 137, 23, 143, 24, 141, 24, 138, 24, 97, 2, 208, 81, 141, 1, 1, 1, 134,
  22, 141, 2, 96, 28, 28, 132, 1, 134, 22, 155, 141, 2, 138, 28, 134, 22, 147, 137, 143, 22, 133, 23, 141, 24, 143, 24, 138, 24, 97, 2, 244, 81, 1, 140, 1, 1, 134, 22, 9, 96, 21, 28, 1, 131, 22, 149, 138,
  2, 135, 28, 131, 22, 148, 137, 140, 22, 134, 23, 135, 24, 138, 24, 140, 24, 96, 252, 81, 138, 1, 1, 1, 131, 22, 138, 2, 96, 27, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 144, 134, 140, 22, 130, 23,
  140, 24, 135, 24, 138, 24, 97, 1, 176, 81, 138, 1, 1, 1, 131, 22, 138, 2, 96, 25
] := by decide

private theorem submissionInstructionsChunk16_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk16 = [
  28, 133, 1, 131, 22, 149, 138, 2, 135, 28, 131, 22, 148, 139, 135, 24, 138, 141, 22, 135, 23, 24, 138, 24, 131, 138, 1, 1, 1, 131, 22, 138, 2, 96, 20, 28, 129, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 141,
  129, 146, 136, 142, 22, 132, 23, 137, 24, 140, 24, 142, 24, 96, 216, 81, 140, 1, 1, 1, 133, 22, 109, 0, 126, 0, 0, 0, 126, 0, 0, 0, 64, 0, 0, 0, 64, 9, 96, 26, 28, 134, 1, 132, 22, 150, 139, 2,
  136, 28, 132, 22, 149, 140, 139, 24, 139, 142, 22, 136, 23, 137, 24, 24, 96, 162, 81, 1, 138, 1, 1, 132, 22, 139, 2, 96, 28, 28, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 140, 143, 130, 147, 140, 143, 24, 143,
  139, 22, 134, 23, 24, 138, 24, 97, 2, 28, 81, 1, 1, 139, 1, 134, 22, 9, 96, 20, 28, 134, 1, 132, 22, 150, 139, 2, 136, 28, 132, 22, 149, 138, 141, 22, 135, 23, 136, 24, 141, 24, 139, 24, 97, 3, 204, 81,
  1, 138, 1, 1, 132, 22, 139, 2, 96, 20, 28, 1, 131, 22, 152, 138, 2, 135, 28, 131, 22, 141, 129, 146, 136, 142, 22, 132, 23, 142, 141, 24, 138, 24, 24, 97, 3, 150, 81, 1, 139, 1, 1, 133, 22, 109, 0, 14,
  0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 8, 9, 96, 21, 28, 134, 1, 132, 22
] := by decide

private theorem submissionInstructionsChunk17_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk17 = [
  150, 139, 2, 136, 28, 149, 138, 141, 22, 135, 23, 136, 24, 141, 24, 139, 24, 97, 2, 82, 81, 1, 138, 1, 1, 132, 22, 139, 2, 96, 22, 28, 1, 131, 22, 152, 138, 2, 135, 28, 138, 135, 2, 136, 28, 140, 139, 131,
  25, 138, 23, 24, 95, 81, 133, 1, 1, 139, 1, 22, 140, 2, 96, 25, 28, 135, 1, 141, 22, 97, 2, 100, 81, 139, 130, 142, 133, 25, 23, 24, 1, 1, 136, 1, 142, 22, 141, 2, 96, 28, 28, 131, 1, 140, 142, 2,
  139, 28, 155, 129, 131, 142, 25, 23, 24, 133, 1, 96, 198, 81, 1, 1, 143, 22, 142, 2, 96, 27, 28, 131, 1, 147, 97, 0, 144, 28, 1, 150, 80, 140, 2, 147, 80, 150, 97, 0, 144, 28, 1, 148, 97, 0, 144, 28,
  146, 80, 97, 0, 144, 28, 151, 96, 144, 28, 149, 28, 1, 143, 1, 136, 22, 159, 1, 135, 22, 159, 1, 134, 22, 154, 1, 1, 132, 22, 153, 1, 1, 130, 22, 152, 156, 86, 91, 145, 133, 96, 2, 27, 129, 129, 23, 96,
  9, 129, 146, 5, 1, 24, 24, 145, 96, 251, 135, 1, 128, 54, 3, 128, 54, 29, 22, 1, 96, 32, 129, 3, 148, 80, 150, 145, 132, 17, 97, 19, 15, 87, 97, 19, 41, 86, 91, 54, 96, 1, 112, 1, 1, 128, 0, 0,
  0, 0, 0, 3, 129, 128, 0, 1, 128, 0, 0, 2, 54, 28, 22, 97, 18, 188, 87,

] := by decide

private theorem submissionInstructionsChunk18_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk18 = [
  97, 1, 0, 20, 97, 1, 120, 54, 20, 1, 97, 18, 185, 87, 95, 53, 96, 232, 29, 54, 98, 32, 118, 33, 2, 24, 96, 247, 87, 115, 16, 181, 40, 89, 5, 22, 178, 98, 175, 214, 144, 26, 176, 43, 33, 241, 110, 170,
  221, 97, 54, 28, 115, 140, 164, 173, 252, 192, 255, 78, 54, 206, 254, 152, 141, 206, 195, 212, 185, 220, 143, 80, 80, 24, 95, 82, 89, 95, 243, 91, 115, 170, 105, 222, 238, 154, 137, 34, 233, 47, 129, 5, 224, 7, 247, 97,
  16, 243, 129, 233, 207, 95, 82, 89, 95, 243, 91, 80, 80, 80, 80, 80, 80, 96, 16, 82, 96, 12, 82, 96, 8, 82, 96, 4, 82, 95, 82, 96, 16, 81, 97, 1, 1, 129, 128, 96, 8, 28, 24, 133, 22, 2, 24, 128,
  129, 96, 16, 28, 24, 133, 22, 98, 1, 0, 1, 2, 24, 95, 82, 96, 32, 95, 243, 91, 96, 251, 91, 127, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96,
  96, 96, 96, 96, 96, 96, 96, 96, 128, 25, 96, 32, 131, 3, 127, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 95,
  95, 96, 33, 54, 16, 97, 19, 41, 87, 91, 129, 96, 32, 1, 145, 53, 133, 132, 23, 135,

] := by decide

private theorem submissionInstructionsChunk19_assemble : Challenge.EvmProof.PcEncoding.assembleBytes submissionInstructionsChunk19 = [
  129, 3, 24, 132, 24, 147, 24, 23, 131, 130, 16, 97, 19, 15, 87, 91, 129, 53, 131, 24, 132, 131, 3, 96, 3, 27, 28, 23, 54, 135, 3, 97, 17, 201, 87, 96, 247, 87, 96, 20, 96, 15, 54, 98, 219, 20, 123, 4,
  22, 129, 2, 56, 3, 96, 12, 57, 89, 95, 243, 91, 129, 129, 83, 96, 1, 1, 144, 96, 8, 28, 144, 129, 131, 87, 96, 200, 86,

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

private theorem tailPrefix_length : tailPrefix.length = 3555 := by
  simp only [tailPrefix, List.length_append, submissionInstructionsChunk0_length, submissionInstructionsChunk1_length, submissionInstructionsChunk2_length, submissionInstructionsChunk3_length, submissionInstructionsChunk4_length, submissionInstructionsChunk5_length, submissionInstructionsChunk6_length, submissionInstructionsChunk7_length, submissionInstructionsChunk8_length, submissionInstructionsChunk9_length, submissionInstructionsChunk10_length, submissionInstructionsChunk11_length, submissionInstructionsChunk12_length, submissionInstructionsChunk13_length, submissionInstructionsChunk14_length, submissionInstructionsChunk15_length, submissionInstructionsChunk16_length, submissionInstructionsChunk17_length, submissionInstructionsChunk18_length]

private theorem tailPrefix_bytes_length : (Challenge.EvmProof.PcEncoding.assembleBytes tailPrefix).length = 4890 := by
  simp only [tailPrefix, Challenge.EvmProof.PcEncoding.assembleBytes_append, List.length_append, chunk0_byteLength, chunk1_byteLength, chunk2_byteLength, chunk3_byteLength, chunk4_byteLength, chunk5_byteLength, chunk6_byteLength, chunk7_byteLength, chunk8_byteLength, chunk9_byteLength, chunk10_byteLength, chunk11_byteLength, chunk12_byteLength, chunk13_byteLength, chunk14_byteLength, chunk15_byteLength, chunk16_byteLength, chunk17_byteLength, chunk18_byteLength]

private theorem instructionPC_tail (i : Nat) (hi : i ≤ 62) :
    submissionArtifact.instructionPC (3555 + i) =
      4890 + (Challenge.EvmProof.PcEncoding.assembleBytes (submissionInstructionsChunk19.take i)).length := by
  apply ArtifactSegment.instructionPC_segment_of_bounds submissionArtifact
    tailPrefix submissionInstructionsChunk19 [] 3555 4890
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
    submissionArtifact.instructionPC 11 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc0 :
    submissionArtifact.instructionPC 11 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc0 :
    instructionPC 11 = 22 := by
  change submissionArtifact.instructionPC 11 = 22
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_1 :
    submissionArtifact.instructionPC 11 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc1 :
    submissionArtifact.instructionPC 11 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc1 :
    instructionPC 11 = 22 := by
  change submissionArtifact.instructionPC 11 = 22
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_405 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc405 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc405 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_406 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc406 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc406 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_407 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc407 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc407 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_408 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc408 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc408 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_409 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc409 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc409 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_410 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc410 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc410 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_412 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc412 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc412 :
    instructionPC 160 = 312 := by
  change submissionArtifact.instructionPC 160 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_417 :
    submissionArtifact.instructionPC 162 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc417 :
    submissionArtifact.instructionPC 162 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc417 :
    instructionPC 162 = 316 := by
  change submissionArtifact.instructionPC 162 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_420 :
    submissionArtifact.instructionPC 156 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc420 :
    submissionArtifact.instructionPC 156 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc420 :
    instructionPC 156 = 247 := by
  change submissionArtifact.instructionPC 156 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_421 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc421 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc421 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_422 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc422 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc422 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_423 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc423 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc423 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_424 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc424 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc424 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_426 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc426 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc426 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_427 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc427 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc427 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_428 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc428 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc428 :
    instructionPC 160 = 312 := by
  change submissionArtifact.instructionPC 160 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_430 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc430 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc430 :
    instructionPC 160 = 312 := by
  change submissionArtifact.instructionPC 160 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_431 :
    submissionArtifact.instructionPC 162 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc431 :
    submissionArtifact.instructionPC 162 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc431 :
    instructionPC 162 = 316 := by
  change submissionArtifact.instructionPC 162 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_439 :
    submissionArtifact.instructionPC 165 = 321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc439 :
    submissionArtifact.instructionPC 165 = 321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc439 :
    instructionPC 165 = 321 := by
  change submissionArtifact.instructionPC 165 = 321
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_440 :
    submissionArtifact.instructionPC 166 = 326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc440 :
    submissionArtifact.instructionPC 166 = 326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc440 :
    instructionPC 166 = 326 := by
  change submissionArtifact.instructionPC 166 = 326
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_441 :
    submissionArtifact.instructionPC 167 = 331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc441 :
    submissionArtifact.instructionPC 167 = 331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc441 :
    instructionPC 167 = 331 := by
  change submissionArtifact.instructionPC 167 = 331
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_442 :
    submissionArtifact.instructionPC 168 = 336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc442 :
    submissionArtifact.instructionPC 168 = 336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc442 :
    instructionPC 168 = 336 := by
  change submissionArtifact.instructionPC 168 = 336
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_443 :
    submissionArtifact.instructionPC 169 = 341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc443 :
    submissionArtifact.instructionPC 169 = 341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc443 :
    instructionPC 169 = 341 := by
  change submissionArtifact.instructionPC 169 = 341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_444 :
    submissionArtifact.instructionPC 170 = 346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc444 :
    submissionArtifact.instructionPC 170 = 346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc444 :
    instructionPC 170 = 346 := by
  change submissionArtifact.instructionPC 170 = 346
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_445 :
    submissionArtifact.instructionPC 171 = 360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc445 :
    submissionArtifact.instructionPC 171 = 360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc445 :
    instructionPC 171 = 360 := by
  change submissionArtifact.instructionPC 171 = 360
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_446 :
    submissionArtifact.instructionPC 172 = 374 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc446 :
    submissionArtifact.instructionPC 172 = 374 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc446 :
    instructionPC 172 = 374 := by
  change submissionArtifact.instructionPC 172 = 374
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_448 :
    submissionArtifact.instructionPC 174 = 430 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc448 :
    submissionArtifact.instructionPC 174 = 430 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc448 :
    instructionPC 174 = 430 := by
  change submissionArtifact.instructionPC 174 = 430
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_449 :
    submissionArtifact.instructionPC 175 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc449 :
    submissionArtifact.instructionPC 175 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc449 :
    instructionPC 175 = 435 := by
  change submissionArtifact.instructionPC 175 = 435
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_450 :
    submissionArtifact.instructionPC 176 = 449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc450 :
    submissionArtifact.instructionPC 176 = 449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc450 :
    instructionPC 176 = 449 := by
  change submissionArtifact.instructionPC 176 = 449
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_451 :
    submissionArtifact.instructionPC 177 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc451 :
    submissionArtifact.instructionPC 177 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc451 :
    instructionPC 177 = 451 := by
  change submissionArtifact.instructionPC 177 = 451
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_452 :
    submissionArtifact.instructionPC 178 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc452 :
    submissionArtifact.instructionPC 178 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc452 :
    instructionPC 178 = 452 := by
  change submissionArtifact.instructionPC 178 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_843 :
    submissionArtifact.instructionPC 156 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc843 :
    submissionArtifact.instructionPC 156 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc843 :
    instructionPC 156 = 247 := by
  change submissionArtifact.instructionPC 156 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_844 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc844 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc844 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_859 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc859 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc859 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_860 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc860 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc860 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_861 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc861 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc861 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem referenceArtifact_pc_862 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem refPc862 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc862 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_265 :
    submissionArtifact.instructionPC 179 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_265 :
    instructionPC 179 = 453 := by
  change submissionArtifact.instructionPC 179 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_266 :
    submissionArtifact.instructionPC 179 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_266 :
    instructionPC 179 = 453 := by
  change submissionArtifact.instructionPC 179 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_268 :
    submissionArtifact.instructionPC 94 = 166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_268 :
    instructionPC 94 = 166 := by
  change submissionArtifact.instructionPC 94 = 166
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_270 :
    submissionArtifact.instructionPC 96 = 169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_270 :
    instructionPC 96 = 169 := by
  change submissionArtifact.instructionPC 96 = 169
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_271 :
    submissionArtifact.instructionPC 97 = 170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_271 :
    instructionPC 97 = 170 := by
  change submissionArtifact.instructionPC 97 = 170
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_272 :
    submissionArtifact.instructionPC 98 = 171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_272 :
    instructionPC 98 = 171 := by
  change submissionArtifact.instructionPC 98 = 171
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_273 :
    submissionArtifact.instructionPC 100 = 175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_273 :
    instructionPC 100 = 175 := by
  change submissionArtifact.instructionPC 100 = 175
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_274 :
    submissionArtifact.instructionPC 101 = 176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_274 :
    instructionPC 101 = 176 := by
  change submissionArtifact.instructionPC 101 = 176
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2_275 :
    submissionArtifact.instructionPC 102 = 178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_275 :
    instructionPC 102 = 178 := by
  change submissionArtifact.instructionPC 102 = 178
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_279 :
    submissionArtifact.instructionPC 3602 = 4949 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_279 :
    instructionPC 3602 = 4949 := by
  change submissionArtifact.instructionPC 3602 = 4949
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_280 :
    submissionArtifact.instructionPC 3603 = 4950 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_280 :
    instructionPC 3603 = 4950 := by
  change submissionArtifact.instructionPC 3603 = 4950
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_281 :
    submissionArtifact.instructionPC 3604 = 4951 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_281 :
    instructionPC 3604 = 4951 := by
  change submissionArtifact.instructionPC 3604 = 4951
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_282 :
    submissionArtifact.instructionPC 3605 = 4952 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_282 :
    instructionPC 3605 = 4952 := by
  change submissionArtifact.instructionPC 3605 = 4952
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_283 :
    submissionArtifact.instructionPC 3606 = 4953 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_283 :
    instructionPC 3606 = 4953 := by
  change submissionArtifact.instructionPC 3606 = 4953
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_284 :
    submissionArtifact.instructionPC 3607 = 4955 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_284 :
    instructionPC 3607 = 4955 := by
  change submissionArtifact.instructionPC 3607 = 4955
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_285 :
    submissionArtifact.instructionPC 3608 = 4956 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_285 :
    instructionPC 3608 = 4956 := by
  change submissionArtifact.instructionPC 3608 = 4956
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2_286 :
    submissionArtifact.instructionPC 3609 = 4957 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem pcU2i_286 :
    instructionPC 3609 = 4957 := by
  change submissionArtifact.instructionPC 3609 = 4957
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_132 :
    Decode.isValidJumpDest submissionBytecode 132 = true := by
  have hp : submissionArtifact.instructionPC 71 = 132 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 71 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_210 :
    Decode.isValidJumpDest submissionBytecode 4949 = true := by
  have hp : submissionArtifact.instructionPC 3602 = 4949 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 3602 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem pcU2_345 :
    submissionArtifact.instructionPC 181 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcU2i_345 :
    instructionPC 181 = 456 := by
  change submissionArtifact.instructionPC 181 = 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem validJumpDest_loop :
    Decode.isValidJumpDest submissionBytecode 457 = true := by
  have hp : submissionArtifact.instructionPC 182 = 457 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 182 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest submissionBytecode 247 = true := by
  have hp : submissionArtifact.instructionPC 156 = 247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 156 (by rfl)
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
    submissionArtifact.instructionPC 1 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci1 :
    instructionPC 1 = 7 := by
  change submissionArtifact.instructionPC 1 = 7
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc2 :
    submissionArtifact.instructionPC 2 = 8 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci2 :
    instructionPC 2 = 8 := by
  change submissionArtifact.instructionPC 2 = 8
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc3 :
    submissionArtifact.instructionPC 3 = 9 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci3 :
    instructionPC 3 = 9 := by
  change submissionArtifact.instructionPC 3 = 9
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc4 :
    submissionArtifact.instructionPC 4 = 10 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci4 :
    instructionPC 4 = 10 := by
  change submissionArtifact.instructionPC 4 = 10
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc5 :
    submissionArtifact.instructionPC 5 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci5 :
    instructionPC 5 = 12 := by
  change submissionArtifact.instructionPC 5 = 12
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc6 :
    submissionArtifact.instructionPC 6 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci6 :
    instructionPC 6 = 13 := by
  change submissionArtifact.instructionPC 6 = 13
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc7 :
    submissionArtifact.instructionPC 7 = 14 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci7 :
    instructionPC 7 = 14 := by
  change submissionArtifact.instructionPC 7 = 14
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc8 :
    submissionArtifact.instructionPC 8 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci8 :
    instructionPC 8 = 17 := by
  change submissionArtifact.instructionPC 8 = 17
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc10 :
    submissionArtifact.instructionPC 10 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci10 :
    instructionPC 10 = 21 := by
  change submissionArtifact.instructionPC 10 = 21
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc11 :
    submissionArtifact.instructionPC 11 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci11 :
    instructionPC 11 = 22 := by
  change submissionArtifact.instructionPC 11 = 22
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc12 :
    submissionArtifact.instructionPC 12 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci12 :
    instructionPC 12 = 23 := by
  change submissionArtifact.instructionPC 12 = 23
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc13 :
    submissionArtifact.instructionPC 13 = 24 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci13 :
    instructionPC 13 = 24 := by
  change submissionArtifact.instructionPC 13 = 24
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc14 :
    submissionArtifact.instructionPC 14 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci14 :
    instructionPC 14 = 26 := by
  change submissionArtifact.instructionPC 14 = 26
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc15 :
    submissionArtifact.instructionPC 15 = 27 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci15 :
    instructionPC 15 = 27 := by
  change submissionArtifact.instructionPC 15 = 27
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc16 :
    submissionArtifact.instructionPC 16 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci16 :
    instructionPC 16 = 29 := by
  change submissionArtifact.instructionPC 16 = 29
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc18 :
    submissionArtifact.instructionPC 18 = 33 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci18 :
    instructionPC 18 = 33 := by
  change submissionArtifact.instructionPC 18 = 33
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc19 :
    submissionArtifact.instructionPC 19 = 34 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci19 :
    instructionPC 19 = 34 := by
  change submissionArtifact.instructionPC 19 = 34
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc20 :
    submissionArtifact.instructionPC 20 = 35 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci20 :
    instructionPC 20 = 35 := by
  change submissionArtifact.instructionPC 20 = 35
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc21 :
    submissionArtifact.instructionPC 21 = 36 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci21 :
    instructionPC 21 = 36 := by
  change submissionArtifact.instructionPC 21 = 36
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc22 :
    submissionArtifact.instructionPC 22 = 39 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci22 :
    instructionPC 22 = 39 := by
  change submissionArtifact.instructionPC 22 = 39
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc23 :
    submissionArtifact.instructionPC 23 = 42 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci23 :
    instructionPC 23 = 42 := by
  change submissionArtifact.instructionPC 23 = 42
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc24 :
    submissionArtifact.instructionPC 24 = 43 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci24 :
    instructionPC 24 = 43 := by
  change submissionArtifact.instructionPC 24 = 43
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc25 :
    submissionArtifact.instructionPC 25 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci25 :
    instructionPC 25 = 44 := by
  change submissionArtifact.instructionPC 25 = 44
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc26 :
    submissionArtifact.instructionPC 127 = 212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci26 :
    instructionPC 127 = 212 := by
  change submissionArtifact.instructionPC 127 = 212
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc27 :
    submissionArtifact.instructionPC 128 = 213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci27 :
    instructionPC 128 = 213 := by
  change submissionArtifact.instructionPC 128 = 213
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc28 :
    submissionArtifact.instructionPC 129 = 215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci28 :
    instructionPC 129 = 215 := by
  change submissionArtifact.instructionPC 129 = 215
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc29 :
    submissionArtifact.instructionPC 130 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci29 :
    instructionPC 130 = 216 := by
  change submissionArtifact.instructionPC 130 = 216
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc30 :
    submissionArtifact.instructionPC 131 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci30 :
    instructionPC 131 = 217 := by
  change submissionArtifact.instructionPC 131 = 217
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc31 :
    submissionArtifact.instructionPC 132 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci31 :
    instructionPC 132 = 218 := by
  change submissionArtifact.instructionPC 132 = 218
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc32 :
    submissionArtifact.instructionPC 133 = 219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci32 :
    instructionPC 133 = 219 := by
  change submissionArtifact.instructionPC 133 = 219
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc33 :
    submissionArtifact.instructionPC 134 = 220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci33 :
    instructionPC 134 = 220 := by
  change submissionArtifact.instructionPC 134 = 220
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc34 :
    submissionArtifact.instructionPC 135 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci34 :
    instructionPC 135 = 221 := by
  change submissionArtifact.instructionPC 135 = 221
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc35 :
    submissionArtifact.instructionPC 136 = 223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci35 :
    instructionPC 136 = 223 := by
  change submissionArtifact.instructionPC 136 = 223
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc36 :
    submissionArtifact.instructionPC 137 = 224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci36 :
    instructionPC 137 = 224 := by
  change submissionArtifact.instructionPC 137 = 224
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc37 :
    submissionArtifact.instructionPC 138 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci37 :
    instructionPC 138 = 225 := by
  change submissionArtifact.instructionPC 138 = 225
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc38 :
    submissionArtifact.instructionPC 139 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci38 :
    instructionPC 139 = 226 := by
  change submissionArtifact.instructionPC 139 = 226
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc39 :
    submissionArtifact.instructionPC 140 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci39 :
    instructionPC 140 = 227 := by
  change submissionArtifact.instructionPC 140 = 227
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc40 :
    submissionArtifact.instructionPC 141 = 228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci40 :
    instructionPC 141 = 228 := by
  change submissionArtifact.instructionPC 141 = 228
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc41 :
    submissionArtifact.instructionPC 142 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci41 :
    instructionPC 142 = 229 := by
  change submissionArtifact.instructionPC 142 = 229
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc42 :
    submissionArtifact.instructionPC 143 = 231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci42 :
    instructionPC 143 = 231 := by
  change submissionArtifact.instructionPC 143 = 231
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc43 :
    submissionArtifact.instructionPC 144 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci43 :
    instructionPC 144 = 232 := by
  change submissionArtifact.instructionPC 144 = 232
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc44 :
    submissionArtifact.instructionPC 145 = 233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci44 :
    instructionPC 145 = 233 := by
  change submissionArtifact.instructionPC 145 = 233
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc45 :
    submissionArtifact.instructionPC 146 = 234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci45 :
    instructionPC 146 = 234 := by
  change submissionArtifact.instructionPC 146 = 234
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc46 :
    submissionArtifact.instructionPC 147 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci46 :
    instructionPC 147 = 235 := by
  change submissionArtifact.instructionPC 147 = 235
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc47 :
    submissionArtifact.instructionPC 148 = 236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci47 :
    instructionPC 148 = 236 := by
  change submissionArtifact.instructionPC 148 = 236
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc48 :
    submissionArtifact.instructionPC 149 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci48 :
    instructionPC 149 = 237 := by
  change submissionArtifact.instructionPC 149 = 237
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc49 :
    submissionArtifact.instructionPC 150 = 238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci49 :
    instructionPC 150 = 238 := by
  change submissionArtifact.instructionPC 150 = 238
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc50 :
    submissionArtifact.instructionPC 151 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci50 :
    instructionPC 151 = 239 := by
  change submissionArtifact.instructionPC 151 = 239
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc51 :
    submissionArtifact.instructionPC 152 = 241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci51 :
    instructionPC 152 = 241 := by
  change submissionArtifact.instructionPC 152 = 241
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc53 :
    submissionArtifact.instructionPC 155 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci53 :
    instructionPC 155 = 246 := by
  change submissionArtifact.instructionPC 155 = 246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc54 :
    submissionArtifact.instructionPC 3478 = 4710 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci54 :
    instructionPC 3478 = 4710 := by
  change submissionArtifact.instructionPC 3478 = 4710
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc55 :
    submissionArtifact.instructionPC 3478 = 4710 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci55 :
    instructionPC 3478 = 4710 := by
  change submissionArtifact.instructionPC 3478 = 4710
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc56 :
    submissionArtifact.instructionPC 3479 = 4731 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci56 :
    instructionPC 3479 = 4731 := by
  change submissionArtifact.instructionPC 3479 = 4731
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc57 :
    submissionArtifact.instructionPC 3480 = 4732 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci57 :
    instructionPC 3480 = 4732 := by
  change submissionArtifact.instructionPC 3480 = 4732
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc58 :
    submissionArtifact.instructionPC 3481 = 4733 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci58 :
    instructionPC 3481 = 4733 := by
  change submissionArtifact.instructionPC 3481 = 4733
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc59 :
    submissionArtifact.instructionPC 3482 = 4734 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci59 :
    instructionPC 3482 = 4734 := by
  change submissionArtifact.instructionPC 3482 = 4734
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPc60 :
    submissionArtifact.instructionPC 3483 = 4735 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cjPci60 :
    instructionPC 3483 = 4735 := by
  change submissionArtifact.instructionPC 3483 = 4735
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem cjPc66 :
    submissionArtifact.instructionPC 84 = 151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci66 :
    instructionPC 84 = 151 := by
  change submissionArtifact.instructionPC 84 = 151
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc67 :
    submissionArtifact.instructionPC 85 = 153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci67 :
    instructionPC 85 = 153 := by
  change submissionArtifact.instructionPC 85 = 153
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc68 :
    submissionArtifact.instructionPC 86 = 154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci68 :
    instructionPC 86 = 154 := by
  change submissionArtifact.instructionPC 86 = 154
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc69 :
    submissionArtifact.instructionPC 87 = 155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci69 :
    instructionPC 87 = 155 := by
  change submissionArtifact.instructionPC 87 = 155
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc70 :
    submissionArtifact.instructionPC 88 = 157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci70 :
    instructionPC 88 = 157 := by
  change submissionArtifact.instructionPC 88 = 157
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc71 :
    submissionArtifact.instructionPC 89 = 158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci71 :
    instructionPC 89 = 158 := by
  change submissionArtifact.instructionPC 89 = 158
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc72 :
    submissionArtifact.instructionPC 90 = 159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci72 :
    instructionPC 90 = 159 := by
  change submissionArtifact.instructionPC 90 = 159
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc73 :
    submissionArtifact.instructionPC 91 = 161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci73 :
    instructionPC 91 = 161 := by
  change submissionArtifact.instructionPC 91 = 161
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc74 :
    submissionArtifact.instructionPC 92 = 162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci74 :
    instructionPC 92 = 162 := by
  change submissionArtifact.instructionPC 92 = 162
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc75 :
    submissionArtifact.instructionPC 93 = 165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci75 :
    instructionPC 93 = 165 := by
  change submissionArtifact.instructionPC 93 = 165
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc84 :
    submissionArtifact.instructionPC 44 = 72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci84 :
    instructionPC 44 = 72 := by
  change submissionArtifact.instructionPC 44 = 72
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc85 :
    submissionArtifact.instructionPC 45 = 73 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci85 :
    instructionPC 45 = 73 := by
  change submissionArtifact.instructionPC 45 = 73
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc86 :
    submissionArtifact.instructionPC 46 = 75 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci86 :
    instructionPC 46 = 75 := by
  change submissionArtifact.instructionPC 46 = 75
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc87 :
    submissionArtifact.instructionPC 47 = 76 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci87 :
    instructionPC 47 = 76 := by
  change submissionArtifact.instructionPC 47 = 76
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc89 :
    submissionArtifact.instructionPC 49 = 79 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci89 :
    instructionPC 49 = 79 := by
  change submissionArtifact.instructionPC 49 = 79
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc90 :
    submissionArtifact.instructionPC 50 = 80 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci90 :
    instructionPC 50 = 80 := by
  change submissionArtifact.instructionPC 50 = 80
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc91 :
    submissionArtifact.instructionPC 51 = 81 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci91 :
    instructionPC 51 = 81 := by
  change submissionArtifact.instructionPC 51 = 81
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc92 :
    submissionArtifact.instructionPC 52 = 84 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci92 :
    instructionPC 52 = 84 := by
  change submissionArtifact.instructionPC 52 = 84
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc93 :
    submissionArtifact.instructionPC 53 = 85 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci93 :
    instructionPC 53 = 85 := by
  change submissionArtifact.instructionPC 53 = 85
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc94 :
    submissionArtifact.instructionPC 54 = 87 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci94 :
    instructionPC 54 = 87 := by
  change submissionArtifact.instructionPC 54 = 87
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc95 :
    submissionArtifact.instructionPC 55 = 88 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci95 :
    instructionPC 55 = 88 := by
  change submissionArtifact.instructionPC 55 = 88
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc109 :
    submissionArtifact.instructionPC 103 = 179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci109 :
    instructionPC 103 = 179 := by
  change submissionArtifact.instructionPC 103 = 179
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc110 :
    submissionArtifact.instructionPC 104 = 180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci110 :
    instructionPC 104 = 180 := by
  change submissionArtifact.instructionPC 104 = 180
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc111 :
    submissionArtifact.instructionPC 105 = 183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci111 :
    instructionPC 105 = 183 := by
  change submissionArtifact.instructionPC 105 = 183
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc112 :
    submissionArtifact.instructionPC 106 = 184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci112 :
    instructionPC 106 = 184 := by
  change submissionArtifact.instructionPC 106 = 184
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc113 :
    submissionArtifact.instructionPC 107 = 186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci113 :
    instructionPC 107 = 186 := by
  change submissionArtifact.instructionPC 107 = 186
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc116 :
    submissionArtifact.instructionPC 94 = 166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci116 :
    instructionPC 94 = 166 := by
  change submissionArtifact.instructionPC 94 = 166
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc117 :
    submissionArtifact.instructionPC 95 = 168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci117 :
    instructionPC 95 = 168 := by
  change submissionArtifact.instructionPC 95 = 168
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc118 :
    submissionArtifact.instructionPC 96 = 169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci118 :
    instructionPC 96 = 169 := by
  change submissionArtifact.instructionPC 96 = 169
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc119 :
    submissionArtifact.instructionPC 97 = 170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci119 :
    instructionPC 97 = 170 := by
  change submissionArtifact.instructionPC 97 = 170
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc120 :
    submissionArtifact.instructionPC 98 = 171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci120 :
    instructionPC 98 = 171 := by
  change submissionArtifact.instructionPC 98 = 171
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc121 :
    submissionArtifact.instructionPC 100 = 175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci121 :
    instructionPC 100 = 175 := by
  change submissionArtifact.instructionPC 100 = 175
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc122 :
    submissionArtifact.instructionPC 101 = 176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci122 :
    instructionPC 101 = 176 := by
  change submissionArtifact.instructionPC 101 = 176
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc123 :
    submissionArtifact.instructionPC 102 = 178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci123 :
    instructionPC 102 = 178 := by
  change submissionArtifact.instructionPC 102 = 178
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc127 :
    submissionArtifact.instructionPC 3602 = 4949 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci127 :
    instructionPC 3602 = 4949 := by
  change submissionArtifact.instructionPC 3602 = 4949
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc128 :
    submissionArtifact.instructionPC 3603 = 4950 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci128 :
    instructionPC 3603 = 4950 := by
  change submissionArtifact.instructionPC 3603 = 4950
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc129 :
    submissionArtifact.instructionPC 3604 = 4951 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci129 :
    instructionPC 3604 = 4951 := by
  change submissionArtifact.instructionPC 3604 = 4951
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc130 :
    submissionArtifact.instructionPC 3605 = 4952 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci130 :
    instructionPC 3605 = 4952 := by
  change submissionArtifact.instructionPC 3605 = 4952
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc131 :
    submissionArtifact.instructionPC 3606 = 4953 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci131 :
    instructionPC 3606 = 4953 := by
  change submissionArtifact.instructionPC 3606 = 4953
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc132 :
    submissionArtifact.instructionPC 3607 = 4955 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci132 :
    instructionPC 3607 = 4955 := by
  change submissionArtifact.instructionPC 3607 = 4955
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc133 :
    submissionArtifact.instructionPC 3608 = 4956 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci133 :
    instructionPC 3608 = 4956 := by
  change submissionArtifact.instructionPC 3608 = 4956
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPc134 :
    submissionArtifact.instructionPC 3609 = 4957 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cjPci134 :
    instructionPC 3609 = 4957 := by
  change submissionArtifact.instructionPC 3609 = 4957
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc147 :
    submissionArtifact.instructionPC 156 = 247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci147 :
    instructionPC 156 = 247 := by
  change submissionArtifact.instructionPC 156 = 247
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc148 :
    submissionArtifact.instructionPC 157 = 248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci148 :
    instructionPC 157 = 248 := by
  change submissionArtifact.instructionPC 157 = 248
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc149 :
    submissionArtifact.instructionPC 158 = 279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci149 :
    instructionPC 158 = 279 := by
  change submissionArtifact.instructionPC 158 = 279
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc152 :
    submissionArtifact.instructionPC 159 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci152 :
    instructionPC 159 = 311 := by
  change submissionArtifact.instructionPC 159 = 311
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc153 :
    submissionArtifact.instructionPC 160 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci153 :
    instructionPC 160 = 312 := by
  change submissionArtifact.instructionPC 160 = 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc155 :
    submissionArtifact.instructionPC 162 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci155 :
    instructionPC 162 = 316 := by
  change submissionArtifact.instructionPC 162 = 316
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc156 :
    submissionArtifact.instructionPC 165 = 321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci156 :
    instructionPC 165 = 321 := by
  change submissionArtifact.instructionPC 165 = 321
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc157 :
    submissionArtifact.instructionPC 166 = 326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci157 :
    instructionPC 166 = 326 := by
  change submissionArtifact.instructionPC 166 = 326
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc158 :
    submissionArtifact.instructionPC 167 = 331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci158 :
    instructionPC 167 = 331 := by
  change submissionArtifact.instructionPC 167 = 331
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc159 :
    submissionArtifact.instructionPC 168 = 336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci159 :
    instructionPC 168 = 336 := by
  change submissionArtifact.instructionPC 168 = 336
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc160 :
    submissionArtifact.instructionPC 169 = 341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci160 :
    instructionPC 169 = 341 := by
  change submissionArtifact.instructionPC 169 = 341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc161 :
    submissionArtifact.instructionPC 170 = 346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci161 :
    instructionPC 170 = 346 := by
  change submissionArtifact.instructionPC 170 = 346
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc162 :
    submissionArtifact.instructionPC 171 = 360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci162 :
    instructionPC 171 = 360 := by
  change submissionArtifact.instructionPC 171 = 360
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc163 :
    submissionArtifact.instructionPC 172 = 374 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci163 :
    instructionPC 172 = 374 := by
  change submissionArtifact.instructionPC 172 = 374
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc164 :
    submissionArtifact.instructionPC 173 = 402 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci164 :
    instructionPC 173 = 402 := by
  change submissionArtifact.instructionPC 173 = 402
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc165 :
    submissionArtifact.instructionPC 174 = 430 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci165 :
    instructionPC 174 = 430 := by
  change submissionArtifact.instructionPC 174 = 430
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc166 :
    submissionArtifact.instructionPC 175 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci166 :
    instructionPC 175 = 435 := by
  change submissionArtifact.instructionPC 175 = 435
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc167 :
    submissionArtifact.instructionPC 176 = 449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci167 :
    instructionPC 176 = 449 := by
  change submissionArtifact.instructionPC 176 = 449
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc168 :
    submissionArtifact.instructionPC 177 = 451 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci168 :
    instructionPC 177 = 451 := by
  change submissionArtifact.instructionPC 177 = 451
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc169 :
    submissionArtifact.instructionPC 178 = 452 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci169 :
    instructionPC 178 = 452 := by
  change submissionArtifact.instructionPC 178 = 452
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc170 :
    submissionArtifact.instructionPC 179 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci170 :
    instructionPC 179 = 453 := by
  change submissionArtifact.instructionPC 179 = 453
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPc172 :
    submissionArtifact.instructionPC 181 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cjPci172 :
    instructionPC 181 = 456 := by
  change submissionArtifact.instructionPC 181 = 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

/-! Cached instruction PCs of the CONT prologue and footer tail. -/

@[simp] theorem cgPc9 :
    submissionArtifact.instructionPC 9 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci9 :
    instructionPC 9 = 18 := by
  change submissionArtifact.instructionPC 9 = 18
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc17 :
    submissionArtifact.instructionPC 17 = 30 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci17 :
    instructionPC 17 = 30 := by
  change submissionArtifact.instructionPC 17 = 30
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc26 :
    submissionArtifact.instructionPC 26 = 45 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci26 :
    instructionPC 26 = 45 := by
  change submissionArtifact.instructionPC 26 = 45
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc27 :
    submissionArtifact.instructionPC 27 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci27 :
    instructionPC 27 = 47 := by
  change submissionArtifact.instructionPC 27 = 47
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc28 :
    submissionArtifact.instructionPC 28 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci28 :
    instructionPC 28 = 48 := by
  change submissionArtifact.instructionPC 28 = 48
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc29 :
    submissionArtifact.instructionPC 29 = 49 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci29 :
    instructionPC 29 = 49 := by
  change submissionArtifact.instructionPC 29 = 49
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc30 :
    submissionArtifact.instructionPC 30 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci30 :
    instructionPC 30 = 51 := by
  change submissionArtifact.instructionPC 30 = 51
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc31 :
    submissionArtifact.instructionPC 31 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci31 :
    instructionPC 31 = 52 := by
  change submissionArtifact.instructionPC 31 = 52
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc32 :
    submissionArtifact.instructionPC 32 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci32 :
    instructionPC 32 = 53 := by
  change submissionArtifact.instructionPC 32 = 53
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc33 :
    submissionArtifact.instructionPC 33 = 54 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci33 :
    instructionPC 33 = 54 := by
  change submissionArtifact.instructionPC 33 = 54
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc34 :
    submissionArtifact.instructionPC 34 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci34 :
    instructionPC 34 = 55 := by
  change submissionArtifact.instructionPC 34 = 55
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc35 :
    submissionArtifact.instructionPC 35 = 58 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci35 :
    instructionPC 35 = 58 := by
  change submissionArtifact.instructionPC 35 = 58
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc37 :
    submissionArtifact.instructionPC 38 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci37 :
    instructionPC 38 = 63 := by
  change submissionArtifact.instructionPC 38 = 63
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc41 :
    submissionArtifact.instructionPC 39 = 64 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci41 :
    instructionPC 39 = 64 := by
  change submissionArtifact.instructionPC 39 = 64
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc42 :
    submissionArtifact.instructionPC 40 = 65 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci42 :
    instructionPC 40 = 65 := by
  change submissionArtifact.instructionPC 40 = 65
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc43 :
    submissionArtifact.instructionPC 41 = 68 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci43 :
    instructionPC 41 = 68 := by
  change submissionArtifact.instructionPC 41 = 68
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc44 :
    submissionArtifact.instructionPC 42 = 69 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci44 :
    instructionPC 42 = 69 := by
  change submissionArtifact.instructionPC 42 = 69
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc45 :
    submissionArtifact.instructionPC 43 = 71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci45 :
    instructionPC 43 = 71 := by
  change submissionArtifact.instructionPC 43 = 71
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc50 :
    submissionArtifact.instructionPC 48 = 77 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci50 :
    instructionPC 48 = 77 := by
  change submissionArtifact.instructionPC 48 = 77
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc60 :
    submissionArtifact.instructionPC 56 = 90 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci60 :
    instructionPC 56 = 90 := by
  change submissionArtifact.instructionPC 56 = 90
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc61 :
    submissionArtifact.instructionPC 57 = 93 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci61 :
    instructionPC 57 = 93 := by
  change submissionArtifact.instructionPC 57 = 93
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc66 :
    submissionArtifact.instructionPC 61 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci66 :
    instructionPC 61 = 117 := by
  change submissionArtifact.instructionPC 61 = 117
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc67 :
    submissionArtifact.instructionPC 62 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci67 :
    instructionPC 62 = 120 := by
  change submissionArtifact.instructionPC 62 = 120
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc68 :
    submissionArtifact.instructionPC 63 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci68 :
    instructionPC 63 = 121 := by
  change submissionArtifact.instructionPC 63 = 121
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc69 :
    submissionArtifact.instructionPC 64 = 122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci69 :
    instructionPC 64 = 122 := by
  change submissionArtifact.instructionPC 64 = 122
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc70 :
    submissionArtifact.instructionPC 65 = 125 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci70 :
    instructionPC 65 = 125 := by
  change submissionArtifact.instructionPC 65 = 125
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc84 :
    submissionArtifact.instructionPC 68 = 128 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci84 :
    instructionPC 68 = 128 := by
  change submissionArtifact.instructionPC 68 = 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc85 :
    submissionArtifact.instructionPC 69 = 129 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci85 :
    instructionPC 69 = 129 := by
  change submissionArtifact.instructionPC 69 = 129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc86 :
    submissionArtifact.instructionPC 70 = 131 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci86 :
    instructionPC 70 = 131 := by
  change submissionArtifact.instructionPC 70 = 131
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc87 :
    submissionArtifact.instructionPC 72 = 133 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci87 :
    instructionPC 72 = 133 := by
  change submissionArtifact.instructionPC 72 = 133
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc89 :
    submissionArtifact.instructionPC 73 = 134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci89 :
    instructionPC 73 = 134 := by
  change submissionArtifact.instructionPC 73 = 134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc90 :
    submissionArtifact.instructionPC 74 = 135 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci90 :
    instructionPC 74 = 135 := by
  change submissionArtifact.instructionPC 74 = 135
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc91 :
    submissionArtifact.instructionPC 75 = 137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci91 :
    instructionPC 75 = 137 := by
  change submissionArtifact.instructionPC 75 = 137
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc92 :
    submissionArtifact.instructionPC 76 = 138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci92 :
    instructionPC 76 = 138 := by
  change submissionArtifact.instructionPC 76 = 138
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc93 :
    submissionArtifact.instructionPC 77 = 139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci93 :
    instructionPC 77 = 139 := by
  change submissionArtifact.instructionPC 77 = 139
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc94 :
    submissionArtifact.instructionPC 78 = 142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci94 :
    instructionPC 78 = 142 := by
  change submissionArtifact.instructionPC 78 = 142
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc95 :
    submissionArtifact.instructionPC 79 = 143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci95 :
    instructionPC 79 = 143 := by
  change submissionArtifact.instructionPC 79 = 143
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc96 :
    submissionArtifact.instructionPC 80 = 144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci96 :
    instructionPC 80 = 144 := by
  change submissionArtifact.instructionPC 80 = 144
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc97 :
    submissionArtifact.instructionPC 81 = 147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci97 :
    instructionPC 81 = 147 := by
  change submissionArtifact.instructionPC 81 = 147
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc98 :
    submissionArtifact.instructionPC 82 = 148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci98 :
    instructionPC 82 = 148 := by
  change submissionArtifact.instructionPC 82 = 148
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc99 :
    submissionArtifact.instructionPC 83 = 149 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci99 :
    instructionPC 83 = 149 := by
  change submissionArtifact.instructionPC 83 = 149
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc127 :
    submissionArtifact.instructionPC 111 = 191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci127 :
    instructionPC 111 = 191 := by
  change submissionArtifact.instructionPC 111 = 191
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc129 :
    submissionArtifact.instructionPC 112 = 192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci129 :
    instructionPC 112 = 192 := by
  change submissionArtifact.instructionPC 112 = 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc130 :
    submissionArtifact.instructionPC 113 = 193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci130 :
    instructionPC 113 = 193 := by
  change submissionArtifact.instructionPC 113 = 193
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc131 :
    submissionArtifact.instructionPC 115 = 196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci131 :
    instructionPC 115 = 196 := by
  change submissionArtifact.instructionPC 115 = 196
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc134 :
    submissionArtifact.instructionPC 126 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci134 :
    instructionPC 126 = 211 := by
  change submissionArtifact.instructionPC 126 = 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc177 :
    submissionArtifact.instructionPC 161 = 313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci177 :
    instructionPC 161 = 313 := by
  change submissionArtifact.instructionPC 161 = 313
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc179 :
    submissionArtifact.instructionPC 163 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci179 :
    instructionPC 163 = 317 := by
  change submissionArtifact.instructionPC 163 = 317
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc180 :
    submissionArtifact.instructionPC 164 = 318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci180 :
    instructionPC 164 = 318 := by
  change submissionArtifact.instructionPC 164 = 318
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc196 :
    submissionArtifact.instructionPC 180 = 454 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci196 :
    instructionPC 180 = 454 := by
  change submissionArtifact.instructionPC 180 = 454
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc198 :
    submissionArtifact.instructionPC 182 = 457 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci198 :
    instructionPC 182 = 457 := by
  change submissionArtifact.instructionPC 182 = 457
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPc199 :
    submissionArtifact.instructionPC 183 = 458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem cgPci199 :
    instructionPC 183 = 458 := by
  change submissionArtifact.instructionPC 183 = 458
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3455 :
    submissionArtifact.instructionPC 3436 = 4593 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3455 :
    instructionPC 3436 = 4593 := by
  change submissionArtifact.instructionPC 3436 = 4593
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3456 :
    submissionArtifact.instructionPC 3437 = 4596 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3456 :
    instructionPC 3437 = 4596 := by
  change submissionArtifact.instructionPC 3437 = 4596
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3457 :
    submissionArtifact.instructionPC 3438 = 4597 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3457 :
    instructionPC 3438 = 4597 := by
  change submissionArtifact.instructionPC 3438 = 4597
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3458 :
    submissionArtifact.instructionPC 3439 = 4600 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3458 :
    instructionPC 3439 = 4600 := by
  change submissionArtifact.instructionPC 3439 = 4600
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3459 :
    submissionArtifact.instructionPC 3440 = 4601 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3459 :
    instructionPC 3440 = 4601 := by
  change submissionArtifact.instructionPC 3440 = 4601
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3460 :
    submissionArtifact.instructionPC 3441 = 4602 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3460 :
    instructionPC 3441 = 4602 := by
  change submissionArtifact.instructionPC 3441 = 4602
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3461 :
    submissionArtifact.instructionPC 3442 = 4603 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3461 :
    instructionPC 3442 = 4603 := by
  change submissionArtifact.instructionPC 3442 = 4603
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3462 :
    submissionArtifact.instructionPC 3443 = 4605 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3462 :
    instructionPC 3443 = 4605 := by
  change submissionArtifact.instructionPC 3443 = 4605
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3463 :
    submissionArtifact.instructionPC 3444 = 4623 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3463 :
    instructionPC 3444 = 4623 := by
  change submissionArtifact.instructionPC 3444 = 4623
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3464 :
    submissionArtifact.instructionPC 3445 = 4624 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3464 :
    instructionPC 3445 = 4624 := by
  change submissionArtifact.instructionPC 3445 = 4624
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3465 :
    submissionArtifact.instructionPC 3446 = 4625 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3465 :
    instructionPC 3446 = 4625 := by
  change submissionArtifact.instructionPC 3446 = 4625
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3466 :
    submissionArtifact.instructionPC 3447 = 4626 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3466 :
    instructionPC 3447 = 4626 := by
  change submissionArtifact.instructionPC 3447 = 4626
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3467 :
    submissionArtifact.instructionPC 3448 = 4629 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3467 :
    instructionPC 3448 = 4629 := by
  change submissionArtifact.instructionPC 3448 = 4629
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3468 :
    submissionArtifact.instructionPC 3449 = 4630 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3468 :
    instructionPC 3449 = 4630 := by
  change submissionArtifact.instructionPC 3449 = 4630
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3469 :
    submissionArtifact.instructionPC 3450 = 4633 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3469 :
    instructionPC 3450 = 4633 := by
  change submissionArtifact.instructionPC 3450 = 4633
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3470 :
    submissionArtifact.instructionPC 3451 = 4634 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3470 :
    instructionPC 3451 = 4634 := by
  change submissionArtifact.instructionPC 3451 = 4634
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3471 :
    submissionArtifact.instructionPC 3452 = 4637 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3471 :
    instructionPC 3452 = 4637 := by
  change submissionArtifact.instructionPC 3452 = 4637
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3472 :
    submissionArtifact.instructionPC 3453 = 4638 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3472 :
    instructionPC 3453 = 4638 := by
  change submissionArtifact.instructionPC 3453 = 4638
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3473 :
    submissionArtifact.instructionPC 3454 = 4639 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3473 :
    instructionPC 3454 = 4639 := by
  change submissionArtifact.instructionPC 3454 = 4639
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3474 :
    submissionArtifact.instructionPC 3455 = 4640 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3474 :
    instructionPC 3455 = 4640 := by
  change submissionArtifact.instructionPC 3455 = 4640
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3475 :
    submissionArtifact.instructionPC 3456 = 4643 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3475 :
    instructionPC 3456 = 4643 := by
  change submissionArtifact.instructionPC 3456 = 4643
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3476 :
    submissionArtifact.instructionPC 3457 = 4644 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3476 :
    instructionPC 3457 = 4644 := by
  change submissionArtifact.instructionPC 3457 = 4644
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3477 :
    submissionArtifact.instructionPC 3458 = 4645 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3477 :
    instructionPC 3458 = 4645 := by
  change submissionArtifact.instructionPC 3458 = 4645
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3478 :
    submissionArtifact.instructionPC 3459 = 4646 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3478 :
    instructionPC 3459 = 4646 := by
  change submissionArtifact.instructionPC 3459 = 4646
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3479 :
    submissionArtifact.instructionPC 3460 = 4648 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3479 :
    instructionPC 3460 = 4648 := by
  change submissionArtifact.instructionPC 3460 = 4648
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3480 :
    submissionArtifact.instructionPC 3461 = 4649 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3480 :
    instructionPC 3461 = 4649 := by
  change submissionArtifact.instructionPC 3461 = 4649
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3481 :
    submissionArtifact.instructionPC 3462 = 4650 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3481 :
    instructionPC 3462 = 4650 := by
  change submissionArtifact.instructionPC 3462 = 4650
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3482 :
    submissionArtifact.instructionPC 3463 = 4654 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3482 :
    instructionPC 3463 = 4654 := by
  change submissionArtifact.instructionPC 3463 = 4654
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3483 :
    submissionArtifact.instructionPC 3464 = 4655 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3483 :
    instructionPC 3464 = 4655 := by
  change submissionArtifact.instructionPC 3464 = 4655
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3484 :
    submissionArtifact.instructionPC 3465 = 4656 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3484 :
    instructionPC 3465 = 4656 := by
  change submissionArtifact.instructionPC 3465 = 4656
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3485 :
    submissionArtifact.instructionPC 3466 = 4658 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3485 :
    instructionPC 3466 = 4658 := by
  change submissionArtifact.instructionPC 3466 = 4658
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3486 :
    submissionArtifact.instructionPC 3467 = 4659 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3486 :
    instructionPC 3467 = 4659 := by
  change submissionArtifact.instructionPC 3467 = 4659
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3487 :
    submissionArtifact.instructionPC 3468 = 4680 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3487 :
    instructionPC 3468 = 4680 := by
  change submissionArtifact.instructionPC 3468 = 4680
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3488 :
    submissionArtifact.instructionPC 3469 = 4681 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3488 :
    instructionPC 3469 = 4681 := by
  change submissionArtifact.instructionPC 3469 = 4681
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3489 :
    submissionArtifact.instructionPC 3470 = 4682 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3489 :
    instructionPC 3470 = 4682 := by
  change submissionArtifact.instructionPC 3470 = 4682
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3490 :
    submissionArtifact.instructionPC 3471 = 4703 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3490 :
    instructionPC 3471 = 4703 := by
  change submissionArtifact.instructionPC 3471 = 4703
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3491 :
    submissionArtifact.instructionPC 3472 = 4704 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3491 :
    instructionPC 3472 = 4704 := by
  change submissionArtifact.instructionPC 3472 = 4704
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3492 :
    submissionArtifact.instructionPC 3473 = 4705 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3492 :
    instructionPC 3473 = 4705 := by
  change submissionArtifact.instructionPC 3473 = 4705
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3502 :
    submissionArtifact.instructionPC 3477 = 4709 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3502 :
    instructionPC 3477 = 4709 := by
  change submissionArtifact.instructionPC 3477 = 4709
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3510 :
    submissionArtifact.instructionPC 3484 = 4736 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3510 :
    instructionPC 3484 = 4736 := by
  change submissionArtifact.instructionPC 3484 = 4736
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPc3511 :
    submissionArtifact.instructionPC 3485 = 4737 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

set_option maxRecDepth 100000 in
@[simp] theorem cgPci3511 :
    instructionPC 3485 = 4737 := by
  change submissionArtifact.instructionPC 3485 = 4737
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

/-- The padding code is entered by fall-through; no return address is pushed. -/
def padEnterPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨157, .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255), by rfl, by decide⟩,
   ⟨158, .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), by rfl, by decide⟩]

/-- Cached located path for the calldata copy and the zero offset; CALLDATASIZE stays in slot 12 as the fast-entry continuation. -/
def padCopyPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨159, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨160, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨161, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨162, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨164, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩]

/-- Cached located path for the fast-entry test: only the lengths 64, 128 and 192 (the
calldata size has no bit outside `0xc0`) go straight to the block loop. -/
def padGuardPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨176, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨177, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨178, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨180, .push ⟨1, by decide⟩ (UInt256.ofNat 143), by rfl, by decide⟩,
   ⟨181, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the sentinel byte. -/
def padSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨94, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨95, .op (.Dup ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨96, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨97, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨98, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the footer-loop setup: the loop head 4949 stays under the two loop
registers (it is the back-edge target of the loop's `DUP4 JUMPI`), then the bit length, the rounded
length offset plus 89, and `DUP3 JUMP` to the loop head. -/
def padFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨99, .push ⟨2, by decide⟩ (UInt256.ofNat 4949), by rfl, by decide⟩,
   ⟨100, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨101, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨102, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨103, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨104, .push ⟨2, by decide⟩ (UInt256.ofNat 968), by rfl, by decide⟩,
   ⟨105, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨106, .push ⟨1, by decide⟩ (UInt256.ofNat 63), by rfl, by decide⟩,
   ⟨107, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨108, .push ⟨1, by decide⟩ (UInt256.ofNat 89), by rfl, by decide⟩,
   ⟨109, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨110, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨111, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for the footer-loop exit: `PUSH1 200 JUMP` at 4964 (the fall-through of the
loop's `JUMPI`), then at 200 the generic continuation 48 replaces the output entry and the three
loop words are dropped. -/
def padExitPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨3615, .push ⟨1, by decide⟩ (UInt256.ofNat 200), by rfl, by decide⟩,
   ⟨3616, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, .push ⟨1, by decide⟩ (UInt256.ofNat 48), by rfl, by decide⟩,
   ⟨120, .op (.Swap ⟨15, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨121, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨122, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨123, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨124, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, .push ⟨2, by decide⟩ (UInt256.ofNat 457), by rfl, by decide⟩,
   ⟨126, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem validJumpDest_200 :
    Decode.isValidJumpDest submissionBytecode 200 = true := by
  have hp : submissionArtifact.instructionPC 118 = 200 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 118 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_212 :
    Decode.isValidJumpDest submissionBytecode 212 = true := by
  have hp : submissionArtifact.instructionPC 127 = 212 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 127 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4708 :
    Decode.isValidJumpDest submissionBytecode 4709 = true := by
  have hp : submissionArtifact.instructionPC 3477 = 4709 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3477 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_47 :
    Decode.isValidJumpDest submissionBytecode 48 = true := by
  have hp : submissionArtifact.instructionPC 28 = 48 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 28 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_64 :
    Decode.isValidJumpDest submissionBytecode 64 = true := by
  have hp : submissionArtifact.instructionPC 39 = 64 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 39 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_128 :
    Decode.isValidJumpDest submissionBytecode 128 = true := by
  have hp : submissionArtifact.instructionPC 68 = 128 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 68 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_143 :
    Decode.isValidJumpDest submissionBytecode 143 = true := by
  have hp : submissionArtifact.instructionPC 79 = 143 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 79 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_192 :
    Decode.isValidJumpDest submissionBytecode 192 = true := by
  have hp : submissionArtifact.instructionPC 112 = 192 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 112 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem validJumpDest_494 :
    Decode.isValidJumpDest submissionBytecode 494 = true := by
  have hp : submissionArtifact.instructionPC 209 = 494 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 209 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_824 :
    Decode.isValidJumpDest submissionBytecode 824 = true := by
  have hp : submissionArtifact.instructionPC 403 = 824 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 403 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4748 :
    Decode.isValidJumpDest submissionBytecode 4736 = true := by
  have hp : submissionArtifact.instructionPC 3484 = 4736 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3484 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4553 :
    Decode.isValidJumpDest submissionBytecode 4553 = true := by
  have hp : submissionArtifact.instructionPC 3400 = 4553 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3400 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4601 :
    Decode.isValidJumpDest submissionBytecode 4601 = true := by
  have hp : submissionArtifact.instructionPC 3440 = 4601 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3440 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4805 :
    Decode.isValidJumpDest submissionBytecode 4793 = true := by
  have hp : submissionArtifact.instructionPC 3528 = 4793 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3528 (by rfl)
  rw [hp] at h
  exact h

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4808 :
    Decode.isValidJumpDest submissionBytecode 4796 = true := by
  have hp : submissionArtifact.instructionPC 3530 = 4796 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 3530 (by rfl)
  rw [hp] at h
  exact h










end Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
