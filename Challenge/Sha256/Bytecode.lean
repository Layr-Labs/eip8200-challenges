import Challenge.RouteB.Bytecode
import EvmSemantics.Data.Hex
set_option warningAsError true
/-!
# The frozen raw-EVM SHA-256 artifact

`referenceBytecode` is the byte-for-byte output of:

```sh
lake exe yulc Challenge/Sha256/reference.yul
```

The compiler is used only to generate the artifact. Route B proofs target
these frozen bytes and reason through `EvmSemantics.EVM.Step`; they do not
appeal to compiler correctness.
-/

namespace Challenge.Sha256

open EvmSemantics
/-- The canonical hexadecimal form of the submitted artifact. -/
def referenceHex : String :=
  (include_str "reference.hex").trimAscii.copy

/-- The submitted SHA-256 bytecode, decoded from the frozen artifact. -/
def referenceBytecode : ByteArray := Hex.hexToBytes referenceHex

/-- The generic Route B disassembler round-trips the frozen artifact. -/
theorem referenceBytecode_roundtrip :
    Challenge.RouteB.Bytecode.assemble
      (Challenge.RouteB.Bytecode.disassemble referenceBytecode) = referenceBytecode :=
  Challenge.RouteB.Bytecode.assemble_disassemble _

end Challenge.Sha256
