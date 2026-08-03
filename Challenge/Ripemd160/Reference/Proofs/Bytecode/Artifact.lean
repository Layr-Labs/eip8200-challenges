import Challenge.EvmProof.Program
import Challenge.Ripemd160.Reference.Bytecode
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Structural certificate for the frozen RIPEMD-160 artifact

The instruction-boundary list below is generated from the reusable raw-bytecode
disassembler. Its assembly theorem ties every location used by the direct proof
to the exact frozen bytes.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

def referenceInstructions : List Instr :=
[
  .push 2 27,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x81,
  op 0x83,
  .push 1 32,
  op 0x03,
  op 0x1c,
  op 0x82,
  op 0x84,
  op 0x1b,
  op 0x17,
  op 0x16,
  op 0x92,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 46,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 1 32,
  op 0x01,
  op 0x51,
  op 0x91,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 70,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x83,
  op 0x16,
  op 0x82,
  .push 1 5,
  op 0x1b,
  op 0x82,
  op 0x01,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 90,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 2 672,
  op 0x01,
  op 0x51,
  op 0x91,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 115,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x82,
  op 0x16,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 672,
  op 0x01,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 142,
  op 0x56,
  op 0x5b,
  op 0x81,
  .push 1 5,
  op 0x1c,
  .push 1 5,
  op 0x1b,
  op 0x81,
  op 0x01,
  op 0x51,
  .push 1 31,
  op 0x83,
  op 0x16,
  op 0x1a,
  op 0x92,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 271,
  op 0x56,
  op 0x5b,
  op 0x80,
  op 0x80,
  .push 0 0,
  op 0x14,
  op 0x15,
  .push 2 169,
  op 0x57,
  op 0x50,
  op 0x83,
  op 0x83,
  op 0x83,
  op 0x18,
  op 0x18,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 1,
  op 0x14,
  op 0x15,
  .push 2 194,
  op 0x57,
  op 0x50,
  op 0x83,
  op 0x82,
  op 0x19,
  op 0x16,
  op 0x83,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 2,
  op 0x14,
  op 0x15,
  .push 2 223,
  op 0x57,
  op 0x50,
  .push 4 4294967295,
  op 0x84,
  op 0x84,
  op 0x19,
  op 0x84,
  op 0x17,
  op 0x18,
  op 0x16,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 3,
  op 0x14,
  op 0x15,
  .push 2 248,
  op 0x57,
  op 0x50,
  op 0x83,
  op 0x19,
  op 0x83,
  op 0x16,
  op 0x84,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 4 4294967295,
  op 0x84,
  op 0x19,
  op 0x84,
  op 0x17,
  op 0x83,
  op 0x18,
  op 0x16,
  op 0x94,
  op 0x50,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 434,
  op 0x56,
  op 0x5b,
  op 0x80,
  op 0x51,
  .push 1 32,
  op 0x82,
  op 0x01,
  op 0x51,
  .push 1 64,
  op 0x83,
  op 0x01,
  op 0x51,
  .push 1 96,
  op 0x84,
  op 0x01,
  op 0x51,
  .push 1 128,
  op 0x85,
  op 0x01,
  op 0x51,
  .push 4 4294967295,
  op 0x8a,
  .push 2 314,
  .push 0 0,
  op 0x8b,
  .push 2 75,
  op 0x56,
  op 0x5b,
  .push 2 327,
  .push 0 0,
  op 0x86,
  op 0x88,
  op 0x8a,
  op 0x8e,
  .push 2 147,
  op 0x56,
  op 0x5b,
  op 0x88,
  op 0x01,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x82,
  .push 2 349,
  .push 0 0,
  op 0x8d,
  op 0x85,
  .push 2 4,
  op 0x56,
  op 0x5b,
  op 0x01,
  op 0x16,
  op 0x90,
  op 0x50,
  .push 4 4294967295,
  op 0x82,
  op 0x16,
  op 0x87,
  op 0x52,
  .push 4 4294967295,
  op 0x83,
  op 0x16,
  .push 1 128,
  op 0x88,
  op 0x01,
  op 0x52,
  .push 2 397,
  .push 2 389,
  .push 0 0,
  .push 1 10,
  op 0x87,
  .push 2 4,
  op 0x56,
  op 0x5b,
  .push 1 3,
  op 0x89,
  .push 2 51,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x85,
  op 0x16,
  .push 1 64,
  op 0x88,
  op 0x01,
  op 0x52,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 32,
  op 0x88,
  op 0x01,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 475,
  op 0x56,
  op 0x5b,
  op 0x80,
  op 0x51,
  op 0x80,
  .push 1 3,
  op 0x1a,
  .push 1 24,
  op 0x1b,
  op 0x81,
  .push 1 2,
  op 0x1a,
  .push 1 16,
  op 0x1b,
  op 0x17,
  op 0x81,
  .push 1 1,
  op 0x1a,
  .push 1 8,
  op 0x1b,
  op 0x82,
  .push 0 0,
  op 0x1a,
  op 0x17,
  op 0x17,
  op 0x92,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 561,
  op 0x56,
  op 0x5b,
  op 0x36,
  .push 1 72,
  op 0x81,
  op 0x01,
  .push 1 6,
  op 0x1c,
  .push 1 6,
  op 0x1b,
  op 0x91,
  op 0x50,
  op 0x80,
  .push 0 0,
  .push 2 2048,
  op 0x37,
  .push 1 128,
  op 0x81,
  .push 2 2048,
  op 0x01,
  op 0x53,
  op 0x80,
  .push 1 3,
  op 0x1b,
  .push 1 8,
  op 0x83,
  op 0x03,
  .push 2 2048,
  op 0x01,
  .push 0 0,
  op 0x5b,
  .push 1 8,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 554,
  op 0x57,
  .push 1 255,
  op 0x83,
  op 0x82,
  .push 1 3,
  op 0x1b,
  op 0x1c,
  op 0x16,
  op 0x81,
  op 0x83,
  op 0x01,
  op 0x53,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 521,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 616,
  op 0x56,
  op 0x5b,
  .push 0 0,
  op 0x5b,
  .push 1 16,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 612,
  op 0x57,
  .push 2 601,
  .push 2 595,
  .push 0 0,
  op 0x83,
  .push 1 2,
  op 0x1b,
  op 0x85,
  op 0x01,
  .push 2 439,
  op 0x56,
  op 0x5b,
  op 0x82,
  .push 2 95,
  op 0x56,
  op 0x5b,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 568,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 961,
  op 0x56,
  op 0x5b,
  .push 2 630,
  op 0x81,
  .push 2 566,
  op 0x56,
  op 0x5b,
  .push 1 160,
  .push 1 32,
  .push 1 192,
  op 0x5e,
  .push 1 160,
  .push 1 32,
  .push 2 352,
  op 0x5e,
  .push 1 160,
  .push 1 32,
  .push 2 512,
  op 0x5e,
  .push 0 0,
  op 0x5b,
  .push 1 80,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 726,
  op 0x57,
  op 0x80,
  .push 1 4,
  op 0x1c,
  .push 2 714,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 1568,
  op 0x01,
  op 0x51,
  .push 2 693,
  .push 0 0,
  op 0x85,
  .push 2 1376,
  .push 2 120,
  op 0x56,
  op 0x5b,
  .push 2 706,
  .push 0 0,
  op 0x86,
  .push 2 1184,
  .push 2 120,
  op 0x56,
  op 0x5b,
  op 0x84,
  .push 1 192,
  .push 2 276,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 655,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 0 0,
  op 0x5b,
  .push 1 80,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 804,
  op 0x57,
  op 0x80,
  .push 1 4,
  op 0x1c,
  .push 2 792,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 1728,
  op 0x01,
  op 0x51,
  .push 2 767,
  .push 0 0,
  op 0x85,
  .push 2 1472,
  .push 2 120,
  op 0x56,
  op 0x5b,
  .push 2 780,
  .push 0 0,
  op 0x86,
  .push 2 1280,
  .push 2 120,
  op 0x56,
  op 0x5b,
  op 0x84,
  .push 1 4,
  op 0x03,
  .push 2 352,
  .push 2 276,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 729,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 4 4294967295,
  .push 2 448,
  op 0x51,
  .push 2 256,
  op 0x51,
  .push 2 544,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  .push 2 480,
  op 0x51,
  .push 2 288,
  op 0x51,
  .push 2 576,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 64,
  op 0x52,
  .push 4 4294967295,
  .push 2 352,
  op 0x51,
  .push 2 320,
  op 0x51,
  .push 2 608,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 96,
  op 0x52,
  .push 4 4294967295,
  .push 2 384,
  op 0x51,
  .push 1 192,
  op 0x51,
  .push 2 640,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 128,
  op 0x52,
  .push 4 4294967295,
  .push 2 416,
  op 0x51,
  .push 1 224,
  op 0x51,
  .push 2 512,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 160,
  op 0x52,
  .push 4 4294967295,
  op 0x85,
  op 0x16,
  .push 1 32,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 1006,
  op 0x56,
  op 0x5b,
  .push 0 0,
  op 0x5b,
  .push 1 4,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 1001,
  op 0x57,
  .push 1 255,
  op 0x83,
  op 0x82,
  .push 1 3,
  op 0x1b,
  op 0x1c,
  op 0x16,
  op 0x81,
  op 0x83,
  op 0x01,
  op 0x53,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 968,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 31 1780731860627700044960722568376592188711674974810043212252563479055960840,
  .push 2 1184,
  op 0x52,
  .push 32 1374703749640218873849524064026661036561295975619335768036000015621818746370,
  .push 2 1216,
  op 0x52,
  .push 32 1809286146446445343010337679715913357291520642540487409382712519614204477440,
  .push 2 1248,
  op 0x52,
  .push 32 2286348414996307935469207465186628553155355030353023797310855598864584999170,
  .push 2 1280,
  op 0x52,
  .push 32 6793533947442029545286681365244130742947859423983440781638017424580845963790,
  .push 2 1312,
  op 0x52,
  .push 32 5454326014381509071620663843103927214778145566039445656282506490595801825280,
  .push 2 1344,
  op 0x52,
  .push 32 5000281043567253289773844389228683908720941172611121566642559091978571025676,
  .push 2 1376,
  op 0x52,
  .push 32 4998451946933852135137276647445154408072640462072745561656555001729660617996,
  .push 2 1408,
  op 0x52,
  .push 32 4097353149147406276549177442451244923784709130172834976461593227075946283008,
  .push 2 1440,
  op 0x52,
  .push 32 3634466825900925589093651101374881051901026410458987220032629834781140389131,
  .push 2 1472,
  op 0x52,
  .push 32 4083287390302437702768465126624575726298108573653391417181074648310269415176,
  .push 2 1504,
  op 0x52,
  .push 32 3627420088851531435467691758328083203359072412578514691593700216701345333248,
  .push 2 1536,
  op 0x52,
  .push 0 0,
  .push 2 1568,
  op 0x52,
  .push 4 1518500249,
  .push 2 1600,
  op 0x52,
  .push 4 1859775393,
  .push 2 1632,
  op 0x52,
  .push 4 2400959708,
  .push 2 1664,
  op 0x52,
  .push 4 2840853838,
  .push 2 1696,
  op 0x52,
  .push 4 1352829926,
  .push 2 1728,
  op 0x52,
  .push 4 1548603684,
  .push 2 1760,
  op 0x52,
  .push 4 1836072691,
  .push 2 1792,
  op 0x52,
  .push 4 2053994217,
  .push 2 1824,
  op 0x52,
  .push 0 0,
  .push 2 1856,
  op 0x52,
  .push 4 1732584193,
  .push 1 32,
  op 0x52,
  .push 4 4023233417,
  .push 1 64,
  op 0x52,
  .push 4 2562383102,
  .push 1 96,
  op 0x52,
  .push 4 271733878,
  .push 1 128,
  op 0x52,
  .push 4 3285377520,
  .push 1 160,
  op 0x52,
  .push 2 1580,
  .push 0 0,
  .push 2 480,
  op 0x56,
  op 0x5b,
  .push 0 0,
  op 0x5b,
  op 0x81,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 1614,
  op 0x57,
  .push 2 1603,
  op 0x81,
  .push 2 2048,
  op 0x01,
  .push 2 621,
  op 0x56,
  op 0x5b,
  .push 1 64,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 1582,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 0 0,
  .push 0 0,
  op 0x52,
  .push 0 0,
  op 0x5b,
  .push 1 5,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 1665,
  op 0x57,
  .push 2 1654,
  .push 2 1642,
  .push 0 0,
  op 0x83,
  .push 2 32,
  op 0x56,
  op 0x5b,
  op 0x82,
  .push 1 2,
  op 0x1b,
  .push 1 12,
  op 0x01,
  .push 2 966,
  op 0x56,
  op 0x5b,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 1620,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 1 32,
  .push 0 0,
  op 0xf3
]

theorem referenceInstructions_count : referenceInstructions.length = 831 := by
  decide

theorem assemble_referenceInstructions :
    assemble referenceInstructions = referenceBytecode := by
  apply ByteArray.ext
  simp (config := { maxSteps := 1000000 })
    [assemble, assembleBytes, referenceInstructions, op, referenceBytecode,
    referenceBytes, Instr.bytes, natToBE]
  repeat' apply And.intro
  all_goals decide

def referenceArtifact : Challenge.EvmProof.ProgramArtifact where
  code := referenceBytecode
  instructions := referenceInstructions
  assembly_eq := assemble_referenceInstructions

def instructionPC (index : Nat) : Nat :=
  referenceArtifact.instructionPC index

@[simp] theorem referenceArtifact_pc_0 :
    referenceArtifact.instructionPC 0 = 0x0 := by rfl

@[simp] theorem referenceArtifact_pc_1 :
    referenceArtifact.instructionPC 1 = 0x3 := by rfl

@[simp] theorem referenceArtifact_pc_20 :
    referenceArtifact.instructionPC 20 = 0x1b := by rfl

@[simp] theorem referenceArtifact_pc_21 :
    referenceArtifact.instructionPC 21 = 0x1c := by rfl

@[simp] theorem referenceArtifact_pc_22 :
    referenceArtifact.instructionPC 22 = 0x1f := by rfl

@[simp] theorem referenceArtifact_pc_35 :
    referenceArtifact.instructionPC 35 = 0x2e := by rfl

@[simp] theorem referenceArtifact_pc_36 :
    referenceArtifact.instructionPC 36 = 0x2f := by rfl

@[simp] theorem referenceArtifact_pc_37 :
    referenceArtifact.instructionPC 37 = 0x32 := by rfl

@[simp] theorem referenceArtifact_pc_52 :
    referenceArtifact.instructionPC 52 = 0x46 := by rfl

@[simp] theorem referenceArtifact_pc_53 :
    referenceArtifact.instructionPC 53 = 0x47 := by rfl

@[simp] theorem referenceArtifact_pc_54 :
    referenceArtifact.instructionPC 54 = 0x4a := by rfl

@[simp] theorem referenceArtifact_pc_67 :
    referenceArtifact.instructionPC 67 = 0x5a := by rfl

@[simp] theorem referenceArtifact_pc_68 :
    referenceArtifact.instructionPC 68 = 0x5b := by rfl

@[simp] theorem referenceArtifact_pc_69 :
    referenceArtifact.instructionPC 69 = 0x5e := by rfl

@[simp] theorem referenceArtifact_pc_83 :
    referenceArtifact.instructionPC 83 = 0x73 := by rfl

@[simp] theorem referenceArtifact_pc_84 :
    referenceArtifact.instructionPC 84 = 0x74 := by rfl

@[simp] theorem referenceArtifact_pc_85 :
    referenceArtifact.instructionPC 85 = 0x77 := by rfl

@[simp] theorem referenceArtifact_pc_105 :
    referenceArtifact.instructionPC 105 = 0x8e := by rfl

@[simp] theorem referenceArtifact_pc_106 :
    referenceArtifact.instructionPC 106 = 0x8f := by rfl

@[simp] theorem referenceArtifact_pc_107 :
    referenceArtifact.instructionPC 107 = 0x92 := by rfl

@[simp] theorem referenceArtifact_pc_205 :
    referenceArtifact.instructionPC 205 = 0x10f := by rfl

@[simp] theorem referenceArtifact_pc_206 :
    referenceArtifact.instructionPC 206 = 0x110 := by rfl

@[simp] theorem referenceArtifact_pc_207 :
    referenceArtifact.instructionPC 207 = 0x113 := by rfl

@[simp] theorem referenceArtifact_pc_313 :
    referenceArtifact.instructionPC 313 = 0x1b2 := by rfl

@[simp] theorem referenceArtifact_pc_314 :
    referenceArtifact.instructionPC 314 = 0x1b3 := by rfl

@[simp] theorem referenceArtifact_pc_315 :
    referenceArtifact.instructionPC 315 = 0x1b6 := by rfl

@[simp] theorem referenceArtifact_pc_346 :
    referenceArtifact.instructionPC 346 = 0x1db := by rfl

@[simp] theorem referenceArtifact_pc_347 :
    referenceArtifact.instructionPC 347 = 0x1dc := by rfl

@[simp] theorem referenceArtifact_pc_348 :
    referenceArtifact.instructionPC 348 = 0x1df := by rfl

@[simp] theorem referenceArtifact_pc_410 :
    referenceArtifact.instructionPC 410 = 0x231 := by rfl

@[simp] theorem referenceArtifact_pc_411 :
    referenceArtifact.instructionPC 411 = 0x232 := by rfl

@[simp] theorem referenceArtifact_pc_412 :
    referenceArtifact.instructionPC 412 = 0x235 := by rfl

@[simp] theorem referenceArtifact_pc_448 :
    referenceArtifact.instructionPC 448 = 0x268 := by rfl

@[simp] theorem referenceArtifact_pc_449 :
    referenceArtifact.instructionPC 449 = 0x269 := by rfl

@[simp] theorem referenceArtifact_pc_450 :
    referenceArtifact.instructionPC 450 = 0x26c := by rfl

@[simp] theorem referenceArtifact_pc_647 :
    referenceArtifact.instructionPC 647 = 0x3c1 := by rfl

@[simp] theorem referenceArtifact_pc_648 :
    referenceArtifact.instructionPC 648 = 0x3c2 := by rfl

@[simp] theorem referenceArtifact_pc_649 :
    referenceArtifact.instructionPC 649 = 0x3c5 := by rfl

@[simp] theorem referenceArtifact_pc_682 :
    referenceArtifact.instructionPC 682 = 0x3ee := by rfl

@[simp] theorem validJumpDest_1b :
    Decode.isValidJumpDest referenceBytecode 0x1b = true := by
  have h := referenceArtifact.isValidJumpDest_index 20 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 20) = true at h
  simpa using h

@[simp] theorem validJumpDest_2e :
    Decode.isValidJumpDest referenceBytecode 0x2e = true := by
  have h := referenceArtifact.isValidJumpDest_index 35 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 35) = true at h
  simpa using h

@[simp] theorem validJumpDest_46 :
    Decode.isValidJumpDest referenceBytecode 0x46 = true := by
  have h := referenceArtifact.isValidJumpDest_index 52 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 52) = true at h
  simpa using h

@[simp] theorem validJumpDest_5a :
    Decode.isValidJumpDest referenceBytecode 0x5a = true := by
  have h := referenceArtifact.isValidJumpDest_index 67 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 67) = true at h
  simpa using h

@[simp] theorem validJumpDest_73 :
    Decode.isValidJumpDest referenceBytecode 0x73 = true := by
  have h := referenceArtifact.isValidJumpDest_index 83 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 83) = true at h
  simpa using h

@[simp] theorem validJumpDest_8e :
    Decode.isValidJumpDest referenceBytecode 0x8e = true := by
  have h := referenceArtifact.isValidJumpDest_index 105 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 105) = true at h
  simpa using h

@[simp] theorem validJumpDest_10f :
    Decode.isValidJumpDest referenceBytecode 0x10f = true := by
  have h := referenceArtifact.isValidJumpDest_index 205 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 205) = true at h
  simpa using h

@[simp] theorem validJumpDest_1b2 :
    Decode.isValidJumpDest referenceBytecode 0x1b2 = true := by
  have h := referenceArtifact.isValidJumpDest_index 313 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 313) = true at h
  simpa using h

@[simp] theorem validJumpDest_1db :
    Decode.isValidJumpDest referenceBytecode 0x1db = true := by
  have h := referenceArtifact.isValidJumpDest_index 346 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 346) = true at h
  simpa using h

@[simp] theorem validJumpDest_231 :
    Decode.isValidJumpDest referenceBytecode 0x231 = true := by
  have h := referenceArtifact.isValidJumpDest_index 410 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 410) = true at h
  simpa using h

@[simp] theorem validJumpDest_268 :
    Decode.isValidJumpDest referenceBytecode 0x268 = true := by
  have h := referenceArtifact.isValidJumpDest_index 448 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 448) = true at h
  simpa using h

@[simp] theorem validJumpDest_3c1 :
    Decode.isValidJumpDest referenceBytecode 0x3c1 = true := by
  have h := referenceArtifact.isValidJumpDest_index 647 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 647) = true at h
  simpa using h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest referenceBytecode 0x3ee = true := by
  have h := referenceArtifact.isValidJumpDest_index 682 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 682) = true at h
  simpa using h


end Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
