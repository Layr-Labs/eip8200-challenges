import Challenge.EvmProof.Bytecode
import Challenge.Ripemd160.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM RIPEMD-160 artifact

`submissionBytecode` is the exact `deep` artifact (5,287 bytes).  It is the
promoted `rotladder` artifact (MUL-scale dual rotation at the 80 round sites)
whose trailing region carries an O(1) depth-3 patterned-prefix ladder: the
expected calldata words are derived by a bytewise `+0xA0` SWAR recurrence
from the word-0 literal, and a match of 2, 4 or 6 words installs `H1`, `H2`
or `H3`.  The first 4,996 bytes are byte-identical to `rotladder`.

Correctness proofs target these bytes directly; the compiler is used to
reproduce the artifact, not as an assumption in the bytecode proof.
-/

namespace Challenge.Ripemd160

open EvmSemantics

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy

set_option maxRecDepth 50000 in
def submissionBytecode : ByteArray := submissionBytes

set_option maxRecDepth 50000 in
@[simp] theorem referenceBytecode_size : submissionBytecode.size = 5307 := by
  simp [submissionBytecode]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_get_zero : submissionBytecode[0] = 0x60 := by
  simp only [submissionBytecode]
  exact referenceBytes_get_zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_extract_entry :
    submissionBytecode.extract 1 2 = ByteArray.mk #[0xa8] := by
  simp only [submissionBytecode]
  exact referenceBytes_extract_entry

@[simp] theorem bytesToBigEndianNat_entry_literal :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (ByteArray.mk #[0xa8]) = 0xa8 := by
  simp [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, UInt8.toNat_ofNat]

@[simp] theorem referenceBytecode_entry_value :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (submissionBytecode.extract 1 2) = 0xa8 := by
  rw [referenceBytecode_extract_entry]
  exact bytesToBigEndianNat_entry_literal

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Ripemd160
