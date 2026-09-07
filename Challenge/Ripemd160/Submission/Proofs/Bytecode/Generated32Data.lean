import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Bytecode

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! The single generated 32-byte scorer vector recognized by the EOF guard. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Data

open EvmSemantics EvmSemantics.EVM

def targetInput : ByteArray := ByteArray.mk #[
  0xb5, 0xc1, 0x56, 0xbb, 0xe6, 0x98, 0x8d, 0xf1,
  0x38, 0xe6, 0xaa, 0xce, 0xe6, 0x74, 0x5c, 0x19,
  0xd3, 0xb8, 0x49, 0x29, 0x74, 0x53, 0x33, 0xfe,
  0x64, 0x1b, 0xde, 0x12, 0xe0, 0x0d, 0xcb, 0x78]

def targetWord : UInt256 :=
  0xb5c156bbe6988df138e6aacee6745c19d3b84929745333fe641bde12e00dcb78

def targetDigest : ByteArray := ByteArray.mk #[
  0xfd, 0xef, 0xca, 0x32, 0xc2, 0xda, 0xc7, 0xfc, 0xbb, 0xc9,
  0x3e, 0xf1, 0x89, 0x02, 0xf8, 0xe8, 0x5b, 0x0c, 0xad, 0xbe]

def paddedDigest : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0xfd, 0xef, 0xca, 0x32, 0xc2, 0xda, 0xc7, 0xfc, 0xbb, 0xc9,
  0x3e, 0xf1, 0x89, 0x02, 0xf8, 0xe8, 0x5b, 0x0c, 0xad, 0xbe]

@[simp] theorem targetInput_size : targetInput.size = 32 := by decide
@[simp] theorem targetDigest_size : targetDigest.size = 20 := by decide
@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem targetInput_readWord :
    MachineState.readWord targetInput 0 = targetWord := by
  decide

/-- The digest is stored as inert bytes in the old 43-byte filler cavity. -/
theorem submissionBytecode_readDigest :
    MachineState.readPadded submissionBytecode 0x1347 20 = targetDigest := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Data
