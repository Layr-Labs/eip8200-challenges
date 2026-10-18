import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CandidateInstructions
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataProgram

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RetainedBridge111.Candidate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
def candidateBytes : List UInt8 := prefix0Bytes ++ prefix1Bytes ++ prefix2Bytes ++ prefix3Bytes ++ prefix4Bytes ++ prefix5Bytes ++ prefix6Bytes ++ prefix7Bytes ++ prefix8Bytes ++ prefix9Bytes ++ prefix10Bytes ++ prefix11Bytes ++ prefix12Bytes ++ prefix13Bytes ++ prefix14Bytes ++ prefix15Bytes ++ prefix16Bytes ++ prefix17Bytes ++ prefix18Bytes ++ prefix19Bytes ++ literal0Bytes ++ suffix0Bytes
def candidateCode : ByteArray := mkCode candidateBytes
theorem exact_assembly : mkCode (Challenge.EvmProof.PcEncoding.assembleBytes instructions ++ []) = candidateCode := by
  simp only [instructions, prefixInstructions, literalInstructions, suffixInstructions,
    Challenge.EvmProof.PcEncoding.assembleBytes_append, List.append_nil, candidateCode, candidateBytes,
    prefix0_assembly, prefix1_assembly, prefix2_assembly, prefix3_assembly, prefix4_assembly, prefix5_assembly, prefix6_assembly, prefix7_assembly, prefix8_assembly, prefix9_assembly, prefix10_assembly, prefix11_assembly, prefix12_assembly, prefix13_assembly, prefix14_assembly, prefix15_assembly, prefix16_assembly, prefix17_assembly, prefix18_assembly, prefix19_assembly, literal0_assembly, suffix0_assembly]
def artifact : DataProgramArtifact where
  code := candidateCode
  instructions := instructions
  data := []
  assembly_eq := exact_assembly
theorem candidate_size : candidateCode.size = 9876 := by
  change candidateBytes.toArray.size = 9876
  simp only [List.size_toArray, candidateBytes, List.length_append, prefix0_bytes_count, prefix1_bytes_count, prefix2_bytes_count, prefix3_bytes_count, prefix4_bytes_count, prefix5_bytes_count, prefix6_bytes_count, prefix7_bytes_count, prefix8_bytes_count, prefix9_bytes_count, prefix10_bytes_count, prefix11_bytes_count, prefix12_bytes_count, prefix13_bytes_count, prefix14_bytes_count, prefix15_bytes_count, prefix16_bytes_count, prefix17_bytes_count, prefix18_bytes_count, prefix19_bytes_count, literal0_bytes_count, suffix0_bytes_count]
#print axioms exact_assembly
#print axioms candidate_size
end RetainedBridge111.Candidate
