import Challenge.Ripemd160.Reference.Proofs.Bytecode
import Challenge.Ripemd160.Reference.Proofs.Gas
import Challenge.Ripemd160.Reference.Proofs.Yul

/-!
# Proofs for the bundled RIPEMD-160 reference

This umbrella exposes both proof routes without adding either to the lightweight
artifact module `Challenge.Ripemd160.Reference`:

* `Bytecode.ReferenceCorrect` proves the frozen bytes directly in the EVM,
  including their exact gas schedule;
* `Yul` proves parsing, optimization, compilation, and assembly facts for the
  readable source and exposes its explicit semantic premises.
-/
