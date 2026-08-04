import Challenge.Ripemd160.Reference.Bytecode
import Challenge.Ripemd160.Reference.Source

set_option warningAsError true

/-!
# Bundled RIPEMD-160 reference implementation

Human-readable Yul and its frozen raw bytecode. Correctness proofs are excluded
from this lightweight artifact module; import
`Challenge.Ripemd160.Reference.Proofs` for the proof umbrellas.
-/
