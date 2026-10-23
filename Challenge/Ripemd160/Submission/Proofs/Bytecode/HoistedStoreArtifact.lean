import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStorePrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreSuffix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreArtifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open RetainedBridge111.Candidate

/-- Exact proposed image. Only the first and last instruction chunks differ
from the protected-validated predecessor; the installed submission is unchanged. -/
def instructions : List Instr := headInstructions ++ prefix1 ++ prefix2 ++ prefix3 ++ prefix4 ++ prefix5 ++ prefix6 ++ prefix7 ++ prefix8 ++ prefix9 ++ prefix10 ++ prefix11 ++ prefix12 ++ prefix13 ++ prefix14 ++ prefix15 ++ prefix16 ++ prefix17 ++ prefix18 ++ prefix19 ++ literal0 ++ suffix

def bytes : List UInt8 := prefixBytes ++ prefix1Bytes ++ prefix2Bytes ++ prefix3Bytes ++ prefix4Bytes ++ prefix5Bytes ++ prefix6Bytes ++ prefix7Bytes ++ prefix8Bytes ++ prefix9Bytes ++ prefix10Bytes ++ prefix11Bytes ++ prefix12Bytes ++ prefix13Bytes ++ prefix14Bytes ++ prefix15Bytes ++ prefix16Bytes ++ prefix17Bytes ++ prefix18Bytes ++ prefix19Bytes ++ literal0Bytes ++ suffixBytes

def code : ByteArray := mkCode bytes

theorem exact_assembly : mkCode (PcEncoding.assembleBytes instructions ++ []) = code := by
  simp only [instructions, PcEncoding.assembleBytes_append, List.append_nil,
    code, bytes, prefix_assembly, prefix1_assembly, prefix2_assembly, prefix3_assembly,
    prefix4_assembly, prefix5_assembly, prefix6_assembly, prefix7_assembly, prefix8_assembly,
    prefix9_assembly, prefix10_assembly, prefix11_assembly, prefix12_assembly,
    prefix13_assembly, prefix14_assembly, prefix15_assembly, prefix16_assembly,
    prefix17_assembly, prefix18_assembly, prefix19_assembly, literal0_assembly, suffix_assembly]

def artifact : DataProgramArtifact where
  code := code
  instructions := instructions
  data := []
  assembly_eq := exact_assembly

theorem code_size : code.size = 9742 := by
  change bytes.toArray.size = 9742
  simp only [List.size_toArray, bytes, List.length_append, prefix_bytes_count,
    prefix1_bytes_count, prefix2_bytes_count, prefix3_bytes_count, prefix4_bytes_count,
    prefix5_bytes_count, prefix6_bytes_count, prefix7_bytes_count, prefix8_bytes_count,
    prefix9_bytes_count, prefix10_bytes_count, prefix11_bytes_count, prefix12_bytes_count,
    prefix13_bytes_count, prefix14_bytes_count, prefix15_bytes_count, prefix16_bytes_count,
    prefix17_bytes_count, prefix18_bytes_count, prefix19_bytes_count, literal0_bytes_count,
    suffix_bytes_count]

theorem instruction_count : instructions.length = 5429 := by
  simp only [instructions, List.length_append, prefix_count, prefix1_count, prefix2_count,
    prefix3_count, prefix4_count, prefix5_count, prefix6_count, prefix7_count, prefix8_count,
    prefix9_count, prefix10_count, prefix11_count, prefix12_count, prefix13_count,
    prefix14_count, prefix15_count, prefix16_count, prefix17_count, prefix18_count,
    prefix19_count, literal0_count, suffix_count]

#print axioms exact_assembly
#print axioms code_size
#print axioms instruction_count
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreArtifact
